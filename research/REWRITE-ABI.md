# REWRITE-ABI: Parser / Encoder / CLI / Fixtures

> This document describes the implementation as it stands.  For
> live status see [`lean/STATUS.md`](../lean/STATUS.md); for active
> design work see
> [`REWRITE-PHASE-3-DESIGN.md`](REWRITE-PHASE-3-DESIGN.md).

## Two-tier architecture (byte layer + typed algebra)

- **Byte layer** provides the parser, encoder, and layout engine
  over a pure-IR `ElfFile { header, phdrs, sections }` where each
  section carries typed content.
- **Typed-section algebra** provides `ValidElfFile` with
  named typed sections indexed by `StringSection`.  All 14 mutating
  ops live on top of the typed algebra.  Cross-section coherence
  clauses are vacuous by construction (Fin-typed offsets).
- The **adapter** in `Patchelf/Elf/Adapter.lean` bridges both: `ofElfFile`
  produces `ValidElfFile` from a byte-layer `ElfFile`; `toElfFile`
  writes a typed result back onto a byte-layer template (reused for
  opaque sections).

### Byte-layer ElfFile

```
structure ElfFile where
  header   : ElfHeader
  phdrs    : Array ProgramHeader
  sections : Array Section

structure Section where
  name, type, flags, addr, offset, link, info, addralign, entsize  (metadata)
  content  : SectionContent

inductive SectionContent
  | raw (bytes : ByteArray)
  | strtab (st : StringTable)
  | dynamic (entries : Array DynEntry)
  | dynsym (syms : Array Symbol)
  | versym (entries : Array UInt16)
  | verneed (vns : Array Verneed)
  | sysvHash (ht : SysVHashTable)
  | gnuHash (ht : GnuHashTable)
  | nobits
```

No `bytes` field. No broken-out `Option` fields. No `*ShdrIdx` fields.
Section size is derived from `content` via `encodedSize` — no stored
`sh_size` to go stale.

### Typed-algebra ValidElfFile

```
structure ValidElfFile where
  header    : ElfHeader
  phdrs     : Array ProgramHeader
  dynstr    : StringSection
  dynsym    : Option (SymbolSection dynstr)
  dynamic   : Option (DynamicSection dynstr)
  versym    : Option (Array UInt16)
  verneed   : Option VerneedSection
  sysvHash  : Option SysVHashSection
  gnuHash   : Option GnuHashSection
  interp    : Option InterpSection
```

String-ref offsets in `DynamicSection ds` and `SymbolSection ds` are
`Fin ds.size`, so the byte layer's `dynamicWellFormed` and `dynsymNamesInBounds`
bounds clauses are vacuous.  Coherence tags (DT_STRTAB, DT_SYMTAB,
DT_HASH, DT_GNU_HASH, DT_VERNEED, DT_STRSZ) are DERIVED at encode
time via `assembleEntries` + `LayoutCtx`, not stored.

### Type-safety wrappers

`FileOffset`, `VirtualAddr`, `PhysicalAddr`, `ByteSize`, `Alignment`
wrap `Nat` so they can't be assigned to each other.  `.val` exposes
the underlying `Nat`.  Encode-time fits into `UInt64` are tracked as
decidable side-conditions (`headerFit_*`, `phdrFit`, `shdrFit`) on
the `EncodePreconditions` bundle (see `ByteRoundtrip.lean:2206`).

## 1. File / module layout

```
Patchelf/
├── Elf/
│   ├── Basic.lean          OsAbi, ElfIdent, ElfHeader, DynTag, DynEntry,
│   │                       ProgramHeader, SectionHeader, shared infra.
│   ├── Layout.lean         Byte offsets, fixed sizes, ShType/PhType codes.
│   ├── Reader.lean         ByteArray → UIntN primitives (LE).
│   ├── Writer.lean         UIntN → ByteArray primitives (LE).
│   ├── Serialize.lean      writeArray + uniform-size lemma.
│   ├── ByteLevel.lean      Per-width roundtrip lemmas + ByteWidth bundle;
│   │                       byte_codec_gen elaborator + merge_extract_at.
│   ├── SchemaDSL.lean      `elf_schema` command elaborator (6 field kinds).
│   ├── Schemas.lean        `elf_schema` invocations for 7 structs +
│   │                       hand-written Verneed/SysVHash/GnuHash writers +
│   │                       their byte-roundtrip theorems.
│   ├── Decode.lean         buildArray, decodeChain, decodeStringTable,
│   │                       decodeVersym, decodeSysVHash, decodeGnuHash.
│   ├── DynamicLemmas.lean  insertBeforeLast, hasTag, filter/map preservation.
│   ├── ElfFile.lean        ElfFile + IsValid (8 clauses) +
│   │                       IsLoadable + IsFullyValid.  Content
│   │                       accessors via section_content_accessor.
│   ├── SectionOps.lean     `updateSectionContent` def + 3 simp lemmas
│   │                       (header / phdrs / sections.size projections).
│   │                       Intentionally small — see ROADMAP §5.3.
│   ├── ParseHeader.lean    ParseError inductive + Parse.parseHeader.
│   ├── Splice.lean         Encoder.splice + splice_size.
│   ├── Parser.lean         parse : ByteArray → Except ParseError ParsedElf.
│   ├── LayoutEngine.lean   layoutForEncoding + layoutAlreadyValid.
│   ├── Encoder.lean        encode : ElfFile → ByteArray.
│   ├── ByteRoundtrip.lean  encode_size_eq + parse_encode_roundtrip
│   │                       (conditional on `EncodePreconditions`;
│   │                       `DecodeRoundtripWitness` is a sibling
│   │                       structure derivable from `EncodePreconditions`).
│   │  -- Typed-section algebra
│   ├── StringSection / DynamicSection / SymbolSection /
│   │       AuxSections / InterpSection  (typed section payloads)
│   ├── ValidElfFile.lean   record + growDynstr
│   ├── DynamicParse.lean   DynamicSection.parseFrom (bytes → typed)
│   ├── DynamicEncode.lean  DynamicSection.assembleEntries (typed → bytes)
│   ├── Adapter.lean        ofElfFile / toElfFile via per-section applyX helpers
│   ├── AdapterRoundtrip.lean  preservation theorems ofElfFile_*, toElfFile_*,
│   │                          roundtrip_*
│   ├── ObservableCombinators.lean  growDynstrDynamicOp + mapDynamicOp
│   └── Ops/                14 mutating ops: {OsAbi, Execstack,
│                           AddDebugTag, NoDefaultLib, AddNeeded,
│                           AddRpathEntry, Rpath, Soname,
│                           RemoveRPath, RemoveNeeded, ReplaceNeeded,
│                           ClearSymbolVersion, RenameDynamicSymbols,
│                           Interpreter}.lean
├── CLI.lean                parseArgs + dispatch (byte parser →
│                           adapter → typed op → adapter → byte encoder).
├── Main.lean               IO entry point.
└── Patchelf.lean           Root aggregator.

tests/
├── run.sh                  Harness.
├── fixtures/               hello-linux-x86_64 (et al.).
└── cases/                  One file per flag, 49 shell tests.
```

See [`RESEARCH-SCHEMA-DSL.md`](RESEARCH-SCHEMA-DSL.md) for the full
ByteLevel / SchemaDSL / Schemas design.

## 2. `Elf/Layout.lean` — constants module

Pure data, no proofs. Shared by parser and encoder so they agree on where
every field lives in bytes.

```lean
namespace Patchelf.Elf.Layout

/-- ELF64 fixed sizes. -/
def ehdrSize  : Nat := 64
def phdrSize  : Nat := 56
def shdrSize  : Nat := 64
def dynEntrySize : Nat := 16
def symEntrySize : Nat := 24

/-- e_ident indices. -/
def EI_MAG0    : Nat := 0
def EI_MAG1    : Nat := 1
def EI_MAG2    : Nat := 2
def EI_MAG3    : Nat := 3
def EI_CLASS   : Nat := 4
def EI_DATA    : Nat := 5
def EI_VERSION : Nat := 6
def EI_OSABI   : Nat := 7
def EI_ABIVERSION : Nat := 8
-- ...

def magic : ByteArray := ⟨#[0x7f, 0x45, 0x4c, 0x46]⟩  -- "\x7fELF"

def ELFCLASS64 : UInt8 := 2
def ELFDATA2LSB : UInt8 := 1

/-- ELF header field offsets (byte positions within the 64-byte header). -/
def ehdrOff : Ehdr → Nat
  | .ident     => 0
  | .objType   => 16
  | .machine   => 18
  | .version   => 20
  | .entry     => 24
  | .phoff     => 32
  | .shoff     => 40
  | .flags     => 48
  | .ehsize    => 52
  | .phentsize => 54
  | .phnum     => 56
  | .shentsize => 58
  | .shnum     => 60
  | .shstrndx  => 62

/-- Program header field offsets. -/
def phdrOff : Phdr → Nat  -- similar: type=0 flags=4 offset=8 vaddr=16 paddr=24 filesz=32 memsz=40 align=48

/-- Section header field offsets. -/
def shdrOff : Shdr → Nat  -- name=0 type=4 flags=8 addr=16 offset=24 size=32 link=40 info=44 addralign=48 entsize=56

/-- Section types we care about. -/
def SHT_NULL     : UInt32 := 0
def SHT_PROGBITS : UInt32 := 1
def SHT_SYMTAB   : UInt32 := 2
def SHT_STRTAB   : UInt32 := 3
def SHT_DYNAMIC  : UInt32 := 6
def SHT_DYNSYM   : UInt32 := 11

/-- Program types. -/
def PT_NULL      : UInt32 := 0
def PT_LOAD      : UInt32 := 1
def PT_DYNAMIC   : UInt32 := 2
def PT_INTERP    : UInt32 := 3
def PT_NOTE      : UInt32 := 4
def PT_PHDR      : UInt32 := 6
def PT_GNU_STACK : UInt32 := 0x6474e551

end Patchelf.Elf.Layout
```

## 3. `ParseError` — enumeration

Callers need structured errors for CLI reporting; parser returns `Except`.

```lean
inductive ParseError
  | tooShort (needed : Nat) (got : Nat)           -- file shorter than required
  | badMagic                                       -- EI_MAG0..3 ≠ 0x7f "ELF"
  | not64Bit                                       -- EI_CLASS ≠ ELFCLASS64
  | notLittleEndian                                -- EI_DATA ≠ ELFDATA2LSB
  | badPhentsize (got : UInt16)                    -- ≠ 56
  | badShentsize (got : UInt16)                    -- ≠ 64
  | phdrsOutOfBounds                               -- phoff + phnum*phentsize > file size
  | shdrsOutOfBounds                               -- shoff + shnum*shentsize > file size
  | badShstrndx (got : UInt16) (shnum : UInt16)    -- ≥ shnum
  | shstrtabNotFound                               -- section shstrndx not SHT_STRTAB
  | shstrtabNotNullTerminated
  | dynstrNotNullTerminated
  | dynamicMissingNull                             -- DT_DYNAMIC present but no terminating DT_NULL
  | dynamicOffsetOutOfBounds                       -- DT_NEEDED/SONAME/RPATH/RUNPATH → out of dynstr
  | dynsymOffsetOutOfBounds
  | sectionBytesOutOfBounds (shIdx : Nat)          -- sh_offset + sh_size > file size
  deriving Repr
```

Each case is designed so that **if parse returns `.ok`, the corresponding
`IsValid` clause is already established.** I.e., the parser's failure
modes line up with the 6 validity clauses. This gives:

```lean
theorem parse_ok_implies_valid (bs : ByteArray) (e : ElfFile) :
    parse bs = .ok e → e.IsValid
```

## 4. Parser signature

Bundle byte-layer validity into the result type so downstream
callers never need to re-derive it.  `ParsedElf` is the
ElfFile+IsValid bundle; it is NOT the same type as
`ValidElfFile` (the typed-section algebra record) — the
byte-layer ↔ typed conversion happens at the op boundary via
`Adapter.ofElfFile` / `Adapter.toElfFile`.

```lean
/-- A byte-layer ElfFile together with its validity proof. -/
structure ParsedElf where
  elf     : ElfFile
  isValid : elf.IsValid

def parse (bs : ByteArray) : Except ParseError ParsedElf
```

Callers that invoke ops write:

```lean
let ⟨elf, _hv⟩ ← parse bytes
-- All ops dispatch through the typed algebra:
match Adapter.ofElfFile elf with
| .ok typed =>
    let typed' := ValidElfFile.setOsAbi typed .linux
    let elf' := Adapter.toElfFile elf typed'
    ...
| .error ae => ...  -- adapter rejects genuinely broken input
```

## 5. Encoder signature

```lean
def encode (e : ElfFile) : ByteArray

/-- Round-trip on validated inputs.  Landed conditionally on an
    `EncodePreconditions` bundle (11 fields; 9 conceptual clauses).
    `DecodeRoundtripWitness` is a sibling structure that
    `EncodePreconditions` constructs via
    `decodeRoundtripWitness_of_preconditions`.  See
    ByteRoundtrip.lean. -/
theorem parse_encode_roundtrip
    (e : ParsedElf) (hPre : EncodePreconditions e.elf) :
    parse (encode e.elf) = .ok e

/-- Unconditional supporting theorem. -/
theorem encode_size_eq (e : ElfFile) :
    (encode e).size = encodedFileSize e
```

## 6. `ElfFile` field design

The pure-IR model stores every section as a typed `Section` in
`sections : Array Section`.  No `bytes` field on `ElfFile`; raw bytes
live only at the parse/encode boundary.

Section discriminates content via `SectionContent` (see ElfFile.lean):

- Structural sections (`.dynamic`, `.dynsym`, `.versym`, `.verneed`,
  `.sysvHash`, `.gnuHash`) decode to their typed structures.
- `.strtab`-type sections decode to `StringTable`.
- Everything else (PROGBITS text/data, NOTE, REL/RELA, SYMTAB without
  struct model, `.interp`) becomes `.raw` — the bytes verbatim.
- NOBITS sections use the `.nobits` variant (no file bytes).

Section lookup by type (for unique-structural types) uses
`findUniqueTypeIdx`; lookup by name (for `.dynstr`, `.interp`) uses
`findIdxByName` via shstrtab. Accessors `e.dynamic`, `e.dynstr`,
`e.dynsym`, etc. are thin wrappers over these lookups.

Section size is derived from `content` (via `Section.encodedSize`).
Offset is stored (parser fills; encoder's `layoutForEncoding` rewrites
it if overlapping). This eliminates the stale-`sh_size` bug class.

## 7. `Elf/Reader.lean` — LE read primitives

```lean
namespace Patchelf.Elf.Reader

def readU8  (bs : ByteArray) (off : Nat) : UInt8
def readU16 (bs : ByteArray) (off : Nat) : UInt16   -- LE, 2 bytes
def readU32 (bs : ByteArray) (off : Nat) : UInt32   -- LE, 4 bytes
def readU64 (bs : ByteArray) (off : Nat) : UInt64   -- LE, 8 bytes
def readBytes (bs : ByteArray) (off len : Nat) : ByteArray  -- bs.extract off (off+len)

-- All primitives return 0 on out-of-bounds (convention matches Lean stdlib).
-- Parser uses an explicit bounds check before reading.

end Patchelf.Elf.Reader
```

No proofs needed; parser wraps these with bounds checks.

## 8. `Elf/Writer.lean` — LE write primitives

```lean
namespace Patchelf.Elf.Writer

def writeU8  (v : UInt8)  : ByteArray          -- 1 byte
def writeU16 (v : UInt16) : ByteArray          -- LE, 2 bytes
def writeU32 (v : UInt32) : ByteArray          -- LE, 4 bytes
def writeU64 (v : UInt64) : ByteArray          -- LE, 8 bytes

-- Roundtrip lemmas:
theorem read_write_u8  (v : UInt8)  : Reader.readU8  (writeU8  v) 0 = v
theorem read_write_u16 (v : UInt16) : Reader.readU16 (writeU16 v) 0 = v
theorem read_write_u32 (v : UInt32) : Reader.readU32 (writeU32 v) 0 = v
theorem read_write_u64 (v : UInt64) : Reader.readU64 (writeU64 v) 0 = v

end Patchelf.Elf.Writer
```

## 9. CLI signature

```lean
namespace Patchelf.CLI

inductive Op
  | setOsAbi (abi : OsAbi)
  | setExecstack
  | clearExecstack
  | setRpath (policy : RpathTagPolicy) (path : String)
  | addRpath (policy : RpathTagPolicy) (path : String)
  | shrinkRpath (policy : RpathTagPolicy) (allowedPrefixes : List String)
  | removeRpath
  | addNeeded (lib : String)
  | removeNeeded (lib : String)
  | replaceNeeded (oldName newName : String)
  | setSoname (name : String)
  | removeSoname
  | setInterpreter (path : String)
  | addDebugTag
  | noDefaultLib
  | renameDynamicSymbol (oldName newName : String)
  | renameDynamicSymbols (mappingFile : System.FilePath)
  | clearSymbolVersion (sym : String)
  /-- Print-only operations (6 variants). -/
  | printOsAbi
  | printRpath
  | printNeeded
  | printSoname
  | printInterpreter
  deriving Repr

structure Invocation where
  op   : Op
  file : System.FilePath

inductive CliError
  | badArgs (message : String)
  | parseFailed (err : ParseError)
  | opPreconditionFailed (message : String)
  | ioError (e : IO.Error)
  deriving Repr

def parseArgs (args : List String) : Except CliError Invocation

/-- `v : ParsedElf` in the signature.  Each op dispatches through
    the typed-algebra hop (`Adapter.ofElfFile` / `toElfFile`). -/
def runOp (_opts : Options) (op : Op) (v : ParsedElf) :
    Except CliError ByteArray

def main (args : List String) : IO UInt32
  -- 0 = success, 1 = parse error, 2 = op precondition failed, 3 = IO error

end Patchelf.CLI
```

Each op dispatches through the typed layer: `Adapter.ofElfFile`
converts the parsed byte-layer `ElfFile` to a `ValidElfFile`;
the typed op runs on the typed representation;
`Adapter.toElfFile` writes the result back onto the byte-layer
`ElfFile` template (preserving opaque sections); the byte-layer
encoder splices out the final byte array.  For ops with
preconditions (e.g. `addNeeded` requires `e.dynamic.isSome`), the
CLI builds the precondition witness or returns
`.opPreconditionFailed` — no unchecked casts.

Flag mapping mirrors `src/patchelf.cc` argument parsing:

| Flag | Op |
|---|---|
| `--set-os-abi <abi>` | `setOsAbi` |
| `--set-rpath <path>` | `setRpath` |
| `--remove-rpath` | `removeRpath` |
| `--add-needed <lib>` | `addNeeded` |
| `--remove-needed <lib>` | `removeNeeded` |
| `--replace-needed <old> <new>` | `replaceNeeded` |
| `--set-soname <name>` | `setSoname` |
| `--set-interpreter <path>` | `setInterpreter` |
| `--add-debug-tag` | `addDebugTag` |
| `--no-default-lib` | `noDefaultLib` |
| `--set-execstack` / `--clear-execstack` | `modifyExecstack` |
| `--rename-dynamic-symbols <file>` | `renameDynamicSymbols` (fold) |
| `--clear-symbol-version <sym>` | `clearSymbolVersion` |
| `--add-rpath <path>` | `addRpathEntry` + `modifyRPath` dispatch |
| `--shrink-rpath [--allowed-rpath-prefixes p:...]` | `modifyRPath` (filter mode) |
| `--force-rpath` | sticky flag; retargets DT_RPATH instead of DT_RUNPATH |
| `--print-*` | print op (6 variants) |

## 10. Fixture harness

Upstream tests (`tests/*.sh`) target C patchelf binary via `PATH`
side-setting. We reuse the pattern: `tests/run.sh` runs `patchelf`
against pre-built fixtures, diffs against the golden output of C
patchelf on the same input.

```
tests/
├── run.sh                          # top-level: discover + run all cases
├── helpers.sh                      # common shell functions
├── fixtures/
│   └── build.sh                    # generate fixtures from tests/foo.c
├── cases/
│   ├── 01-set-os-abi.sh
│   ├── 02-remove-rpath.sh
│   └── ...
└── scratch/                        # per-case output dir (gitignored)
```

Each case follows the pattern:

```sh
#!/bin/sh -e
# tests/cases/01-set-os-abi.sh
SCRATCH="scratch/$(basename "$0" .sh)"
rm -rf "$SCRATCH" && mkdir -p "$SCRATCH"
cp ../fixtures/hello-linux-x86_64 "$SCRATCH/input"

# Run our binary
../../.lake/build/bin/patchelf --set-os-abi Linux "$SCRATCH/input"

# Run C patchelf on a second copy
cp ../fixtures/hello-linux-x86_64 "$SCRATCH/expected"
"$PATCHELF_C_BIN" --set-os-abi Linux "$SCRATCH/expected"

# Byte-diff
cmp "$SCRATCH/input" "$SCRATCH/expected"
```

**Golden-output strategy:** the golden binary is generated on the fly
by running C patchelf in each case. This avoids committing binary
fixtures with encoded transformations; only the source fixture is
committed. The C patchelf path comes from `$PATCHELF_C_BIN`.

**Smoke test:** the first case `00-identity.sh` runs no op — just
`parse → encode` — and verifies byte-for-byte equality with the input.
This gates the parser/encoder pair independently of any op.

**Skip e2e:** Darwin can't execute Linux ELF. The fixture bytes are
read/written; no execution. This matches how C patchelf is testable on
Darwin today.

## 11. Work order

1. **Layout.lean** — small, no dependencies. Land first.
2. **Reader.lean** — small, depends on Layout. Land second.
3. **Writer.lean** — small, dual of Reader. Land third.
4. **Parser.lean** — big. Writes the ~20 parse-time checks. First
   iteration can sorry the validity proof; downstream ops don't need it
   to compile. Second iteration closes `parse_ok_implies_valid`.
5. **Encoder.lean** — medium. Emits bytes for every section; reuses
   original bytes for sections we don't break out.
6. **CLI.lean** + **Main.lean** — medium. Dispatch + IO.
7. **lakefile.toml** — add `[[lean_exe]] name = "patchelf"`.
8. **tests/** — fixture builder + smoke case + per-op cases.

Commits land in that order. Each is testable:
- After (3): round-trip unit tests on bytes (smoke case 0).
- After (4): parse-only CLI mode (`patchelf --print-os-abi`).
- After (5): parse+encode round-trip (identity case).
- After (6): per-op cases start to pass.

## 12. Out of scope

- **Big-endian.** Read/Write primitives hard-code little-endian.
  Adding would require a flag in Layout.
- **32-bit ELF.** Structure sizes and offsets are 64-bit only.
- **Parallel parsing.** Sequential is fine for files <100MB.

## 13. Current state of proofs

- `parse_ok_implies_valid`: closed unconditionally. Parser runs the
  decidable byte-layer `IsValid` check; returns `.ok ⟨elf, hv⟩`
  only in the true branch.
- `parse_encode_roundtrip`: closed conditionally on an
  `EncodePreconditions` bundle (11 fields; 9 conceptual clauses;
  see `ByteRoundtrip.lean:2206`).  10 of 11 fields are
  parser-derivable via `encodePreconditions_of_parser`; the
  remaining `spliceDisjoint` clause is supplied by
  `LayoutEngine.layoutForEncoding_produces_spliceRegionsDisjoint`
  for the layout pass's *output*.  The legacy
  `DecodeRoundtripWitness` form is retained as a sibling derivable
  from `EncodePreconditions`.  Op-level wiring of the layout-pass
  branch is tracked in `research/ROADMAP.md` §1.3a / §5.1 and
  superseded by `REWRITE-PHASE-3-DESIGN.md` §3.
- Per-struct byte roundtrip: the DSL emits `write_decodeN_extract`
  theorems (one direction) for 7 fixed-layout structs. Variable-
  length structs (Verneed, SysVHash, GnuHash) have hand-written
  versions in `Schemas.lean` using the `merge_extract_at` tactic
  macro.
- Adapter preservation: `AdapterRoundtrip.lean` has
  `ofElfFile_{header,phdrs,dynstr,versym}`,
  `toElfFile_{header,phdrs}`, and composed `roundtrip_{header,phdrs}`
  theorems proved via `split at h` cascades.
- Typed-algebra ops each carry at least one observable theorem
  (see `Elf/Ops/*.lean`).  `renameDynamicSymbols_observable`
  landed at `Patchelf/Elf/Ops/RenameDynamicSymbols.lean:123`
  (alongside `_dynstr`, `_dynsym_isSome`, `_gnuHash` companions);
  the remaining Priority-2 observability gaps (addDebugTag /
  removeNeeded identity-on-no-op-input) are tracked in
  `lean/STATUS.md` §"Priority 2 gaps".

Shipped code has zero `sorry` and no quarantined WIP files.
