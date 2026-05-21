# `elf_schema` — a byte-serialization DSL for ELF structs

## Abstract

`elf_schema` is a Lean 4 command-level macro that compresses the
hand-written boilerplate for each fixed-layout ELF struct (a Lean
`structure` plus its byte-serializer, decoder, size lemma, byte-
roundtrip theorem, and `ByteWidth` bundle) into one schema
declaration. The DSL lives in `Patchelf/Elf/SchemaDSL.lean`; its
invocations live in `Patchelf/Elf/Schemas.lean`.

This document describes the DSL's syntax, semantics, emission
surface, and design tradeoffs. For the full end-to-end verification
story see `REWRITE-ABI.md` (architecture) and `lean/STATUS.md`
(current state).

## Motivation

Before the DSL, each ELF struct required ~100 LOC of hand-written
code split across four files:

- `Basic.lean` / `ElfFile.lean` — the `structure Foo`
- `Serialize.lean` — `def Foo.write : Foo → ByteArray`
- `Decode.lean` — `def Decode.decodeFoo : ByteArray → Nat → Foo`
- `Roundtrip.lean` — a ~50-line byte-roundtrip proof chain plus
  a ~7-line `ByteWidth` bundle

Seven structs × ~100 LOC = ~700 LOC of near-identical mechanical
boilerplate, plus ~240 LOC of byte-roundtrip proof chains that
differ only in field count / width pattern. The DSL collapses this
to ~10 LOC per struct plus ~670 LOC of shared infrastructure
(`SchemaDSL.lean`).

Reading a schema declaration:

```lean
elf_schema Vernaux := 16
  bytewidth_as vernaux
  vna_hash  : u32 @ 0
  vna_flags : u16 @ 4
  vna_other : u16 @ 6
  vna_name  : u32 @ 8
  vna_next  : u32 @ 12
```

is self-documenting in a way a sprawling hand-written encoder
chain isn't.

## Syntax

```
elf_schema <TypeName> := <TOTAL_BYTES>
  <opt-clause>*
  <field>*
```

where `<TypeName>` is an already-declared `structure` and
`<TOTAL_BYTES>` is the sum of field byte-sizes (also redundantly
computable from the field list; the DSL checks both agree).

## Field kinds

Six field kinds. Each field declares (at minimum) a name, a byte
offset into the struct, and an on-disk width.

### 1. Plain primitive

```
name : <width> @ <offset>
```

`<width>` is `u8` / `u16` / `u32` / `u64`. The Lean-level field
type is `UInt8` / `UInt16` / `UInt32` / `UInt64`. Generated write
is `writeUN x.name`; decode is `name := readUN bs (off + k)`.

### 2. Wrapped primitive

```
name : <width> @ <offset> wrap <WrapperType> <projection>
```

For fields whose Lean-level type is a 1-field structure wrapping a
primitive, e.g. `FileOffset { val : UInt64 }`, `PhType { raw : UInt32 }`.
Generated write is `writeUN x.name.<projection>`; decode is
`name := ⟨readUN bs (off + k)⟩`.

Used by some wrapped fields whose Lean-level type wraps a primitive
*UIntN* (e.g. legacy `UInt64`-backed wrappers).

### 3. Wrapped primitive (Nat-valued)

```
name : <width> @ <offset> wrap_nat <WrapperType> <projection>
```

For fields whose Lean-level type is a 1-field structure wrapping a
`Nat` (not a primitive UIntN): the wrapper types in `Layout.lean` —
`FileOffset { val : Nat }`, `VirtualAddr { val : Nat }`,
`PhysicalAddr { val : Nat }`, `ByteSize { val : Nat }`,
`Alignment { val : Nat }`.  Generated write is
`writeUN x.name.<projection>.toUIntN`; decode is
`name := ⟨(readUN bs (off + k)).toNat⟩`.  The forward-roundtrip
proof uses `simp only [UIntN.ofNat_toNat]` to collapse
`Nat.toUIntN ∘ UIntN.toNat`.

Used by every wrapped field in `ProgramHeader` / `SectionHeader` /
`ElfHeader`.

### 4. Codec-encoded primitive

```
name : <CType> via <width> @ <offset> codec <encFn> <decFn>
                                            <reverseIdLemma>
                                            <forwardIdLemma>
```

For fields whose Lean-level type is arbitrary but the on-disk
representation is a primitive `UIntN`. `encFn : CType → UIntN` and
`decFn : UIntN → CType` are named functions; the DSL emits BOTH
roundtrip directions and consumes corresponding identity lemmas:

- `reverseIdLemma : ∀ u, encFn (decFn u) = u` — used by the
  byte-roundtrip (decode-then-write) proof.
- `forwardIdLemma : ∀ x, decFn (encFn x) = x` — used by the
  forward-roundtrip (write-then-decode, `Foo_decode_write`) proof.

Generated write is `writeUN (encFn x.name)`; decode is
`name := decFn (readUN bs (off + k))`; the byte roundtrip uses
`rw [reverseIdLemma]` to collapse `encFn (decFn _)` to primitive
form before applying `writeUN_readUN_extract`; the forward
roundtrip uses `forwardIdLemma` symmetrically.

Used by:
- `DynEntry.tag` — `DynTag` inductive enum, UInt64 on disk.
  `encFn = DynTag.encodeU64`, `decFn = DynTag.decodeU64`,
  `reverseIdLemma = DynTag.encodeU64_decodeU64`,
  `forwardIdLemma = DynTag.decodeU64_encodeU64`.
- `ElfIdent.osAbi` — `OsAbi` inductive enum, UInt8 on disk.
  `encFn = OsAbi.encode`, `decFn = OsAbi.ofByte`,
  `reverseIdLemma = OsAbi.encode_ofByte`,
  `forwardIdLemma = OsAbi.ofByte_encode`.

### 5. Raw bytes

```
name : raw_bytes <N> @ <offset> [with_size_field <sf>]
```

For fields whose Lean-level type is `ByteArray` and whose on-disk
width is `N` bytes. Generated write is literally `x.name` (the
field is already a ByteArray of the right size, from the decoder);
decode is `name := Reader.readBytes bs (off + k) N`
(= `bs.extract (off+k) (off+k+N)`).

Optional `with_size_field <sf>` names a dependent-proof field
`sf : name.size = N`. When present, decode also emits
`sf := Reader.readBytes_size bs (off+k) N (by omega)`. Forces the
emitted decoder to take an `(h : off + total ≤ bs.size)`
precondition and requires `skip_bytewidth` (because the
`ByteWidth.read` signature is preconditionless).

Used by:
- `ElfIdent.head` — 7-byte magic + class + data + version prefix.
  `with_size_field head_size` for the dependent `head.size = 7`
  proof.
- `ElfIdent.tail` — 8-byte ABI-version + padding suffix.
  `with_size_field tail_size`.

### 6. Embedded sub-struct

```
name : embed <SubType> bytes <N>
         write_as <WriteFn>
         decode_as <DecodeFn>
         roundtrip_as <RoundtripLemma>
         [forward_as <ForwardRoundtripLemma>
          append_left_as <DecodeAppendLeftLemma>]
         @ <offset>
       [with_prec]
```

For fields whose Lean-level type is another ELF struct that itself
has a DSL-generated (or hand-written) byte-roundtrip theorem. The
sub-struct's write/decode/roundtrip are named arguments; `N` is
the sub-struct's byte size.

Generated write is `SubType.write x.name`; decode is
`name := DecodeFn bs (off + k)`; the byte-roundtrip proof uses
`rw [RoundtripLemma bs (off + k) hFit_i]` to reduce the
sub-struct's serialized form to an extract.

The optional `forward_as` and `append_left_as` clauses are
required when the enclosing schema emits a forward roundtrip
(`Foo_decode_write`) and the sub-struct sits at the front of the
serialized form (so the forward-roundtrip proof reads through the
sub-struct's bytes plus a tail).  `forward_as` names the
sub-struct's forward-roundtrip lemma (e.g.
`ElfIdent_decode_write`); `append_left_as` names a "decode is
unaffected by appending bytes on the right" lemma used to peel
the tail before applying `forward_as`.  Without these clauses
the DSL emits no forward roundtrip for the enclosing schema and
the user must hand-write `Foo_decode_write`.

`with_prec` variant is for sub-structs whose decoder itself takes
a precondition (e.g. because of `raw_bytes with_size_field`). The
outer decoder threads its own `h : off + total ≤ bs.size` through
to the sub-decoder via `by omega`.

Used by:
- `ElfHeader.ident` — embeds the 16-byte `ElfIdent` sub-struct
  with `with_prec` (since `ElfIdent.head` / `tail` are
  `raw_bytes with_size_field`); supplies `forward_as
  ElfIdent_decode_write` and `append_left_as
  decodeElfIdent_append_left` so the DSL emits
  `ElfHeader_decode_write`.

## Modifier clauses

Seven clauses placed between `:= TOTAL` and the field list.

### Name overrides

```
decode_as <ident>       — decoder function name (default decodeFoo)
roundtrip_as <ident>    — roundtrip theorem name
bytewidth_as <ident>    — ByteWidth instance name
```

Match existing conventions: `decodePhdr` (not `decodeProgramHeader`),
`ByteWidth.phdr` (not `ByteWidth.of_ProgramHeader`).

### Skip flags

```
skip_write       — caller supplies Foo.write + Foo.write_size
skip_decode      — caller supplies the decoder
skip_bytewidth   — don't emit the ByteWidth instance nor the array-lift
```

`skip_write` and `skip_decode` allow mixing DSL-emitted artifacts with hand-written ones — the
DSL emits just the roundtrip theorem + ByteWidth instance while
hand-written write/decode are left alone. `skip_bytewidth` is
required for schemas whose decoder has a precondition (i.e. any
schema with a `raw_bytes ... with_size_field ...` field, or an
`embed ... with_prec` field), because `ByteWidth.read` has a
preconditionless signature.

### Array-decoder opt-in

```
with_array_decoder <ident>   — emit Decode.<ident> (= buildArray-based
                               fixed-count decoder) + its _size / _getElem
                               lemmas
```

Used by `Symbol` / `ProgramHeader` / `SectionHeader` to emit the
CLI-facing `decodeDynsym` / `decodePhdrs` / `decodeShdrs`.  Not
compatible with `skip_decode` (the array decoder wraps the
per-entry decoder by name).

## Emission surface

Per schema invocation, the DSL emits up to 7 core declarations
(plus 3 more when the `with_array_decoder` opt-in clause is
present, for a total of 10):

| Artifact | Name (default) | Emitted when |
|---|---|---|
| Serializer | `Foo.write : Foo → ByteArray` | not `skip_write` |
| Size lemma | `@[simp] Foo.write_size : (Foo.write x).size = N` | not `skip_write` |
| Decoder | `Decode.decodeFoo : ByteArray → Nat [→ prec-proof] → Foo` | not `skip_decode` |
| Reverse roundtrip | `Foo_write_decodeFoo_extract : …` | always |
| Forward roundtrip | `Foo_decode_write : decodeFoo (Foo.write x) 0 = x` | when no `raw_bytes` field, OR when an `embed` field supplies `forward_as`/`append_left_as` |
| ByteWidth instance | `ByteWidth.of_Foo : ByteWidth Foo` | not `skip_bytewidth` |
| Array-lift theorem | `writeArray_Foo_write_extract : …` | not `skip_bytewidth` |
| Array decoder | `Decode.<Name>` | opt-in via `with_array_decoder <Name>` |
| Array-decoder size | `@[simp] Decode.<Name>_size` | opt-in |
| Array-decoder getElem | `Decode.<Name>_getElem` | opt-in |

6 of 7 fixed-layout schemas (`DynEntry`, `Vernaux`, `Symbol`,
`ProgramHeader`, `SectionHeader`, `ElfHeader`) get
`Foo_decode_write` auto-generated.  Only `ElfIdent_decode_write`
remains hand-written, because `ElfIdent.head`/`tail` are
`raw_bytes with_size_field` (the dependent `head.size = 7` proof
makes the DSL's uniform forward-emission template not apply
cleanly).  See [`ROADMAP.md`](ROADMAP.md) §4.1 for context.

The array-lift theorem (when emitted) is a thin wrapper:
`writeArray Foo.write arr = bs.extract off (off + arr.size * N) :=
 writeArray_of_width ByteWidth.foo bs off arr hFit hEach`.

The `with_array_decoder <Name>` clause (used by Symbol /
ProgramHeader / SectionHeader for the CLI-facing `decodeDynsym`
/ `decodePhdrs` / `decodeShdrs` array decoders) emits a
`buildArray`-based wrapper over the per-entry decoder plus the
matching size and getElem lemmas.

## Migrated structs

All 7 fixed-layout ELF structs are DSL-generated in
`Schemas.lean`:

| Struct | Size | Field kinds used |
|---|---|---|
| DynEntry | 16B | codec (DynTag) + primitive |
| Vernaux | 16B | all primitive |
| Symbol | 24B | all primitive, mixed widths |
| ProgramHeader | 56B | all `wrap_nat` (FileOffset / VirtualAddr / PhysicalAddr / ByteSize / Alignment) |
| SectionHeader | 64B | mixed `wrap_nat` / primitive |
| ElfIdent | 16B | raw_bytes + codec + raw_bytes |
| ElfHeader | 64B | embed (ElfIdent) + `wrap_nat` / primitive |

## Implementation

`SchemaDSL.lean` declares a syntax category `elfSchemaField` with
eight named rules (`fieldPrim`, `fieldWrap`, `fieldWrapNat`,
`fieldCodec`, `fieldRaw`, `fieldRawSf`, `fieldEmbed`,
`fieldEmbedPrec`).  These map to the 6 field kinds described
above (`fieldRaw` and `fieldRawSf` differ only in the optional
`with_size_field`; `fieldEmbed` and `fieldEmbedPrec` differ only
in the optional `with_prec` marker).  The command elaborator
`elabElfSchema`
(annotated `@[command_elab elfSchemaCmd]`) parses the schema
into an `Array FieldSpec`, validates contiguity + total-size +
duplicate-field-name check, then emits each artifact as a
`TSyntax \`command` via quotation patterns (no string-based
`runParserCategory` is used on the hot path).

Emitted code uses `_root_.`-prefixed fully-qualified identifiers
so the `elf_schema` command works inside any namespace.  Every
command wraps its body in `open Patchelf.Elf Patchelf.Elf.Reader
Patchelf.Elf.Writer in …` so bare names like `writeU16` /
`readU32` / `extract_append_extract` resolve without the user
having to pre-open those namespaces.

Field-kind rules use `&"keyword"` markers (not bare `"keyword"`)
so field-name identifiers like `size` in `SectionHeader` don't
collide with DSL keywords like `bytes` / `write_as`.

## DSL v3: trailing-array field kind (deferred)

Three writers in `Schemas.lean` remain hand-written, all with the
same shape: fixed prefix + trailing variable-length array(s).

- `Verneed.write` — 16-byte fixed prefix +
  `writeArray Vernaux.write aux`.  (`Verneed.writeHeader` — the
  16-byte prefix alone — could be DSLized today as a standalone
  schema if there were a `VerneedHeader` struct type; not worth
  the separate-struct overhead for one call site.)
- `SysVHashTable.write` — 8-byte prefix + 2 u32 arrays.
- `GnuHashTable.write` — 16-byte prefix + 3 arrays (u64 bloom,
  u32 buckets, u32 chain).

### Proposed syntax

```
elf_schema Verneed := ?  -- size is not fixed
  vn_version : u16 @ 0
  vn_cnt     : u16 @ 2
  vn_file    : u32 @ 4
  vn_aux     : u32 @ 8
  vn_next    : u32 @ 12
  aux : trailing Array Vernaux via Vernaux.write @ 16
```

The `trailing` field kind:

- Has no fixed byte size (the DSL's total-size check becomes a
  lower bound: `N ≥ fixed_prefix_size`).
- Emits `writeArray SubWriteFn x.field` appended after the prefix
  chain.
- Does NOT emit a decoder — decoder strategies are struct-specific:
  - Verneed: `decodeChain` walker on `.vn_next` pointer.
  - Vernaux (inside Verneed): `decodeChain` walker on `.vna_next`.
  - SysV: reads `numBuckets` / `numChain` from the prefix; uses
    them as array lengths.
  - GNU: reads `maskwords` / `numBuckets` / (chain fills the rest)
    from the prefix.
- Does NOT emit a roundtrip theorem — without a decoder the
  write(decode) = extract shape can't be generated. Hand-written
  roundtrips (if wanted) must combine the DSL's prefix roundtrip
  with a trailing-array-specific argument.

### Why the decode side stays hand-written

Three ELF variable-length-array structures, three different
termination strategies — the DSL has no clean way to express
them uniformly:

| Struct | Termination |
|---|---|
| Verneed + Vernaux chains | Linked-list: walk until `.v*_next = 0`. Bounded by outer `maxCount` for totality. |
| SysV hash | Two count fields in the fixed header (`numBuckets`, `numChain`). |
| GNU hash | Four fields in the header (`maskwords`, `numBuckets`, `symndx`, `shift2`); chain length = total size - header - bloom - buckets. |

Forcing these into a single DSL idiom would require either (a)
per-struct trailing-array decoder syntax that's effectively "name
the hand-written decoder", which saves nothing; or (b) encoding
the termination strategy as a DSL-level enumeration
(chain / count-field / fill-rest), which adds a combinatorial
explosion of field-kind variants for minimal LOC win.

### Estimated impact if landed

Removes the 3 remaining hand-written variable-length writers in
`Schemas.lean` (~80 LOC).  Their byte-roundtrip proofs (which make
up the bulk of the LOC in Schemas.lean post-simplification pass)
already use the `merge_extract_at` tactic macro from `ByteLevel.lean`
and would benefit further.  No correctness change; DSL is ergonomic
only.

## Related infrastructure

### `ByteLevel.lean` — the primitive layer the DSL depends on

- `writeU{8,16,32,64}_size : (writeUN v).size = N` — emitted size
  lemmas for the primitive writers.
- `writeU{8,16,32,64}_readU{8,16,32,64}_extract` — the core
  per-width byte roundtrip: `writeUN (readUN bs off) = bs.extract
  off (off+N)` when the N-byte window fits.
- `ByteWidth α` — a bundled (size, write, read, write_size,
  roundtrip) record. `writeArray_of_width W bs off arr hFit hEach`
  lifts any `ByteWidth α` to the array-level roundtrip.
- `writeArray_fixed_extract` — the generic polymorphic lift the
  `ByteWidth`-based `writeArray_of_width` reduces to.

### ByteLevel per-width duplication (deferred cleanup)

ByteLevel.lean contains ~275 LOC of near-identical proof patterns
across `readU{N}_byte_{k}` (14 private lemmas) + `writeU{N}_getElem`
(3 helpers) + `writeU{N}_readU{N}_extract` (4 extract theorems),
plus thin `_decodeU{N}_extract` aliases. The u16 and u32 cases
share a uniform proof shape (`unfold readU{N} readU8; rw
[dif_pos h0..h{N-1}]; bv_decide`); the u64 case is different
because `readU64` is defined via `readU32` recursion, producing
non-uniform `off + 4 + k` hypothesis bookkeeping.

A width-parameterized `bit_codec uN N` macro could collapse these
but needs two templates (direct-readU8 for u16/u32; via-readU32
for u64). True LOC savings are ~120, not the ~300 initially
estimated, at a cost of ~100 LOC of metaprogramming that obscures
what is otherwise bottom-of-stack stable infrastructure.

**Decision**: deferred. The per-byte lemmas are mature and rarely
touched; deduplication is aesthetic rather than maintenance-
critical. Reevaluate if the proof strategy changes (e.g. if
`bv_decide` internals change such that all 14 lemmas need
revisiting).

### `DynTag.encodeU64` / `DynTag.decodeU64` in `Basic.lean`

The DSL's `codec` rule requires a UIntN-level identity lemma. ELF
specifies `d_tag` as `Int64`, but the primitive width is
`UInt64`. We lift via:

```lean
def DynTag.encodeU64 (t : DynTag) : UInt64 := t.encode.toUInt64
def DynTag.decodeU64 (u : UInt64) : DynTag := DynTag.decode u.toInt64
theorem DynTag.encodeU64_decodeU64 (u : UInt64) :
    (DynTag.decodeU64 u).encodeU64 = u := by
  unfold DynTag.encodeU64 DynTag.decodeU64
  rw [DynTag.decode_encode]
  bv_decide
```

This is strictly dual-lifting: the Int64-level `DynTag.decode_encode`
is proved exhaustively in Basic.lean; `bv_decide` discharges the
`toUInt64 ∘ toInt64 = id` (and symmetric) facts.

## References

- `Patchelf/Elf/SchemaDSL.lean` — elaborator source.
- `Patchelf/Elf/Schemas.lean` — all 7 struct schemas.
- `Patchelf/Elf/ByteLevel.lean` — primitive-layer lemmas.
- `lean/STATUS.md` — current state + history ledger.
- `REWRITE-ABI.md` §1 — file layout showing where each module
  lives.
