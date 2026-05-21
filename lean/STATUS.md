# patchelf (Lean 4 port) — status and known gaps

> **Active design work.** The next major arc — closing the
> PT_LOAD / DT_* coherence gap (the central correctness bug; see
> §"Known correctness gap" below) — is designed in
> [`research/REWRITE-PHASE-3-DESIGN.md`](../research/REWRITE-PHASE-3-DESIGN.md).
> That document is the load-bearing source of truth for the
> validator-and-atomic-write work, the (possibly skipped)
> unification refactor, and the `LayoutPlan` / `apply` machinery.
> Open compression decisions (runtime `decide` for `IsLoadable`,
> in-place-only scope, skip unification) are tracked there.
> STATUS.md and `research/ROADMAP.md` will be reconciled with the
> design doc once the validator work lands.

This document records the current state of the Lean 4 patchelf port.
Forward-looking work items live in `research/ROADMAP.md`.

The port has **two tiers** that live side by side under `lean/Patchelf/Elf/`:

- **Byte layer** — `ElfFile { header, phdrs, sections }` with
  typed section content (`SectionContent.raw | strtab | dynamic |
  dynsym | versym | nobits`).  `.gnu.version_r`, `.hash`, and
  `.gnu.hash` sections are stored as `.raw` at the byte layer;
  the typed-section algebra's `Adapter.ofElfFile` decodes them
  on demand.  No `bytes` field, no broken-out `Option` section
  fields, no `*ShdrIdx` fields.  Raw bytes exist only at the
  parse/encode boundary.  Provides `Parser` + `Encoder` +
  `LayoutEngine` for the wire codec, plus `ByteRoundtrip` for
  the `parse_encode_roundtrip` theorem.  The parser returns
  `ParsedElf = { elf : ElfFile, isValid : elf.IsValid }` — a
  plain ElfFile bundled with its IsValid witness.
- **Typed-section algebra** — `ValidElfFile` is a record of
  named typed sections (`dynstr : StringSection`, `dynamic :
  Option (DynamicSection dynstr)`, `dynsym : Option
  (SymbolSection dynstr)`, …).  Cross-section offset invariants
  are at the TYPE LEVEL: string-ref offsets are `Fin ds.size`,
  so bounds predicates are vacuous by construction.  All 14
  mutating ops (in `Elf/Ops/`) live here, along with their
  observable-correctness theorems.

The `Adapter` bridges the two: `ofElfFile : ElfFile → Except
AdapterError ValidElfFile` and `toElfFile : ElfFile → ValidElfFile →
ElfFile` (the byte-layer input is the "template" for opaque sections
the typed algebra doesn't model).  The CLI flow is bytes →
Parser → ParsedElf → Adapter.ofElfFile → ValidElfFile → op →
Adapter.toElfFile → ElfFile → Encoder → bytes.

**Two co-equal sources of truth.**  Both layers persist through
every op.  The typed algebra is the **edit surface**; the byte
layer is the **layout-pinned reference** for entries the typed
layer doesn't model (DT_RELA/REL/JMPREL addresses, DT_INIT/FINI,
ordering of pre-existing dynamic entries, opaque section
contents).  `Adapter.patchDynamicEntries` reads the byte side
positionally to preserve those verbatim while applying typed-side
edits.  Layout-sensitive ops (e.g. moving `.dynstr` to a new
vaddr) would need a byte-layer pass too; the current 14 ops don't.

---

## What works end-to-end

All 14 mutating ops plus 6 print ops work via `patchelf` against real
ELF fixtures:

| Flag | Status | Notes |
|---|---|---|
| `--set-os-abi <abi>` | works | numeric or canonical name |
| `--print-os-abi` | works | |
| `--set-execstack` / `--clear-execstack` | works | no-op when no PT_GNU_STACK |
| `--print-execstack` | works | prints `execstack: X/-/?` |
| `--remove-rpath` | works | filter-shaped dyn mutation |
| `--remove-needed <lib>` | works | |
| `--remove-soname` | works | |
| `--print-rpath` / `--print-needed` / `--print-soname` / `--print-interpreter` | works | |
| `--set-rpath <path>` | works | retag existing or insert new |
| `--add-rpath <path>` | works | composes with existing rpath |
| `--shrink-rpath [--allowed-rpath-prefixes p:...]` | works | pure prefix filter |
| `--force-rpath` | works | retargets DT_RPATH instead of DT_RUNPATH |
| `--add-needed <lib>` | works | grows `.dynstr` + inserts into `.dynamic` |
| `--replace-needed <old> <new>` | works | reuse-offset fast path + grow path |
| `--set-soname <name>` | works | |
| `--set-interpreter <path>` | works | single unified op (no in-slot/grow split) |
| `--add-debug-tag` | works | |
| `--no-default-lib` | works | |
| `--rename-dynamic-symbol <old> <new>` | works | rejects binaries with `.gnu.hash` |
| `--rename-dynamic-symbols <map-file>` | works | |
| `--clear-symbol-version <sym>` | works | retargets matching versym entries to VER_NDX_GLOBAL |

Global flags: `--output`, `--page-size`, `--version`, `--help`,
`--debug` (accepted, no trace output), `--no-sort` (accepted as no-op),
`--no-clobber-old-sections` (accepted as no-op), `@file` argument
resolution.

Multi-op invocations work by re-parsing the current bytes between ops.

**Test status:** all 49 shell tests in `tests/cases/` pass.

---

## Architecture

```
Patchelf/
├── Elf/
│   │  -- Shared primitives
│   ├── Basic.lean              OsAbi, ElfIdent, ElfHeader, DynTag, DynEntry,
│   │                           ProgramHeader, SectionHeader, DynEntry.isStringRef,
│   │                           StringTable, sysvHash, gnuHash
│   ├── Layout.lean             Byte offsets, fixed sizes, ShType/PhType codes
│   ├── Reader.lean             ByteArray → UIntN primitives (LE)
│   ├── Writer.lean             UIntN → ByteArray primitives (LE)
│   ├── Serialize.lean          writeArray + uniform-size lemma
│   ├── ByteLevel.lean          Per-width roundtrip lemmas + ByteWidth bundle;
│   │                           `byte_codec_gen` elaborator + `merge_extract_at`
│   │                           tactic macro
│   ├── SchemaDSL.lean          `elf_schema` command elaborator
│   │                           (6 field kinds / 8 syntax rules;
│   │                           up to 10 emitted artifacts per schema)
│   ├── Schemas.lean            `elf_schema` invocations for 7 structs +
│   │                           hand-written Verneed/SysVHash/GnuHash writers +
│   │                           their byte-roundtrip theorems
│   ├── Decode.lean             buildArray, decodeChain, decodeStringTable,
│   │                           decodeVersym, decodeSysVHash, decodeGnuHash
│   ├── DynamicLemmas.lean      insertBeforeLast, hasTag, filter/map preservation
│   │
│   │  -- Byte layer: pure-IR `ElfFile` + wire codec
│   ├── ElfFile.lean            ElfFile, SectionContent, IsValid (8 clauses),
│   │                           content accessors (via section_content_accessor
│   │                           macro), IsLoadable, IsFullyValid
│   ├── SectionOps.lean         Section update helpers + IsValid preservation
│   ├── ParseHeader.lean        ParseError + parseHeader (ELF header validation)
│   ├── Splice.lean             Encoder.splice + splice_size
│   ├── Parser.lean             parse : ByteArray → Except ParseError ParsedElf
│   ├── LayoutEngine.lean       layoutForEncoding: recompute offsets + update
│   │                           phdrs when current layout has overlaps
│   ├── Encoder.lean            encode : ElfFile → ByteArray.  Runs
│   │                           syncDtStrszInFile + conditional layoutForEncoding
│   │                           before splicing.
│   ├── ByteRoundtrip.lean      encode_size_eq (unconditional) +
│   │                           parse_encode_roundtrip (unconditional
│   │                           under EncodePreconditions bundle)
│   │
│   │  -- Typed-section algebra
│   ├── StringSection.lean      StringSection + NoNullBytes + lookup
│   ├── DynamicSection.lean     DynamicSection ds (indexed by StringSection)
│   ├── SymbolSection.lean      SymbolSection ds
│   ├── AuxSections.lean        VerneedSection, SysVHashSection, GnuHashSection
│   ├── InterpSection.lean      InterpSection (byte-terminated)
│   ├── ValidElfFile.lean       Record of typed sections + growDynstr
│   ├── DynamicParse.lean       DynamicSection.parseFrom (byte-layer → typed)
│   ├── DynamicEncode.lean      DynamicSection.assembleEntries (typed →
│   │                           byte-layer; coherence tags derived, not stored)
│   ├── Adapter.lean            ofElfFile / toElfFile — 8 applyX helpers +
│   │                           patchDynamicEntries (positional remap)
│   ├── AdapterRoundtrip.lean   8 preservation theorems
│   │                           (ofElfFile_*, toElfFile_*, roundtrip_*)
│   │                           proved via `split at h` cascades
│   ├── ObservableCombinators.lean   growDynstrDynamicOp + mapDynamicOp
│   │                                 + their master observable theorems
│   │
│   └── Ops/                    14 mutating ops
│       ├── OsAbi.lean, Execstack.lean, AddDebugTag.lean, NoDefaultLib.lean
│       ├── AddNeeded.lean, AddRpathEntry.lean, Rpath.lean, Soname.lean
│       ├── RemoveNeeded.lean, RemoveRPath.lean
│       ├── ClearSymbolVersion.lean, ReplaceNeeded.lean
│       ├── RenameDynamicSymbols.lean
│       └── Interpreter.lean
├── CLI.lean                    parseArgs + dispatch (byte parse → adapter →
│                               typed op → adapter → byte encode)
├── Main.lean                   IO entry point
└── Patchelf.lean               Root aggregator

tests/
├── run.sh                      harness
├── cases/                      49 shell tests (*.sh)
└── fixtures/                   hello-linux-x86_64 (et al.)
```

Total Lean source: ~13,700 LOC. Distribution by category:

| Category | LOC | What it is |
|---|---|---|
| Verification (`ByteRoundtrip` + `ByteLevel` + `LayoutEngine` + `Basic` proofs) | ~5,700 | Tier D `parse_encode_roundtrip` infrastructure |
| DSL + op-layer infra (`SchemaDSL` + `Schemas` + `Adapter` + `AdapterRoundtrip` + `ObservableCombinators`) | ~2,400 | `elf_schema` elaborator + 7 invocations + bridge |
| Wire codec + types (Splice, Layout, Decode, Parser, ParseHeader, Reader, Writer, Serialize, DynamicParse/Encode) | ~1,600 | Reader/Writer + Splice + parsing primitives |
| Typed-section types (DynamicSection, StringSection, SymbolSection, ValidElfFile, InterpSection, AuxSections) | ~610 | Typed algebra + StringSection lookup roundtrip |
| 14 ops (`Elf/Ops/*.lean` + ObservableCombinators) | ~1,000 | mutating operations |
| CLI + Main | ~840 | command-line tool |
| Misc (root, ElfFile, Encoder, surviving SectionOps + DynamicLemmas) | ~1,500 | structural |

`ByteRoundtrip.lean` (~2900 LOC) and `SchemaDSL.lean` (~1200 LOC) are
the two largest files.  Every file builds; zero `sorry`.

Comparison context: comparable verified-codec projects (EverParse,
HACL\*, CompCert, CakeML) sit at proof:code ratios of 2-7×.  At
13.7k Lean for a 3k-LOC C++ baseline (~4.5×), this codebase sits in
the 60th-70th percentile of healthy.  An EverParse-style fully-
automated approach has a floor around 6k-9k LOC for the same
functionality; closing that gap requires structural changes to the
codec abstraction (richer DSL, fewer hand-written `_decode_write`
lemmas), not surface-level cleanup.

---

## Invariants and theorems

### Byte-layer `IsValid` (8 clauses, decidable)

`header_counts`, `sections_wf`, `strtabs_wf`, `dynamic_wf`,
`dynsym_wf`, `content_wf`, `types_distinct`, `names_unique`.  See
`ElfFile.lean` for clause definitions.  `SectionOps.lean` exposes
preservation theorems for each shape of section update.
Typed-algebra ops don't carry `_preserves_valid` theorems —
`ValidElfFile` is typed, not predicate-bundled, so the type itself
IS the invariant.

### `IsLoadable` and `IsFullyValid` (decorative)

`IsLoadable` adds non-overlapping sections + PT_INTERP/PT_DYNAMIC
phdr offset agreement + PT_LOAD alignment congruence.
`IsFullyValid` further adds `dynamicAddressCoherent` — a single
record covering DT_STRTAB / DT_SYMTAB / DT_HASH / DT_GNU_HASH /
DT_VERNEED address-coherence plus DT_STRSZ size-coherence (the
latter is the `strsz_size` field of `dynamicAddressCoherent`,
not a separate clause).

Both are decidable and defined but **not established by `parse`,
not preserved by any op, not consumed downstream**.  Parser
returns `ParsedElf` (IsValid only).  See ROADMAP item 1.1.

### Tier D: `parse_encode_roundtrip` — UNCONDITIONAL

`Patchelf.Elf.parse_encode_roundtrip (e : ParsedElf)
(hPre : EncodePreconditions e.elf) : parse (encode e.elf) = .ok e`.

**What this theorem actually buys**: this is a **codec-asymmetry
guard for encoder/parser refactors**, not
a "byte-level correctness" theorem in any user-facing sense.  It rules
out the silent bug class where the encoder writes pattern A, the
parser reads pattern B, A ≠ B, and the round-trip cancels in shell
tests.  Empirically, 0 of ~10 historical bugs fixed in this codebase
would have been caught by this theorem (they all live one level up:
adapter logic, observable correctness, semantic ops).  The theorem
does NOT catch:
- the known PT_LOAD-stale-offset gap (see Known gaps below);
- wire-format / spec disagreement (`e_machine` set to a value the
  kernel rejects but Lean's parser accepts);
- DT_STRSZ drift between tag and table (faithfully encoded and read
  back; `ldd` would reject).

The 49 shell-test suite has **no external oracle** (no `readelf`, no
`ldd`, no `execve` of the produced binary).  Every test is
`lean-patchelf | lean-patchelf` — encoder bug E + parser bug P that
cancel are caught by `parse_encode_roundtrip` (asymmetry would
surface) but vacuously pass shell tests (which round-trip through
the same buggy pair).  Adding a `readelf -a` golden-diff harness
against real `/usr/bin/*` ELF inputs would catch a higher-yield
bug class than further investment in the byte-roundtrip proof.

The byte-level codec is verified end-to-end under the
`EncodePreconditions` bundle (11 explicit, decidable preconditions —
9 informally-grouped clauses, with `headerFit_*` exploded into 3
separate fields covering the Nat-wrapper-to-`UInt64`-fit conditions).
All decoder-inverse facts are proved:

- `parseHeader_encode` — header parser succeeds and recovers `e.header`.
- `phdrs_decode_encode` — `decodePhdrs` recovers `e.phdrs`.
- `shdrs_decode_encode` — `decodeShdrs` recovers `e.sections.map toShdr`.
- `section_decode_encode` — for every section, `decodeSectionContent`
  on `(toShdr s)` recovers `s.content`.

`EncodePreconditions e` packages 11 fields (9 conceptual facts;
the 3 `headerFit_*` fields are tracked separately):
- `syncOk` — `syncDtStrszInFile e = e` (DT_STRSZ already in sync).
- `spliceDisjoint` — all 4 splice region kinds are pairwise disjoint.
  Subsumes `layoutAlreadyValid e = true` via
  `layoutAlreadyValid_of_spliceRegionsDisjoint`; the derived
  `EncodePreconditions.layoutOk` view exposes the bool form.
- `identValid` — ELF magic + class + data ident bytes are spec-valid.
- `typesMatch` — section type matches content constructor (per
  `decodeSectionContent` dispatch).
- `sizeFit` — each `s.encodedSize < UInt64.size`.
- `nullEmpty` — SHT_NULL sections have `.raw ByteArray.empty` content.
- `headerFit_{entry,phoff,shoff}` — each ElfHeader wrap_nat field's
  `.val` fits in UInt64 (parser-derivable: came from `(readU64 ...).toNat`).
- `phdrFit` — every ProgramHeader wrap_nat field fits in UInt64.
- `shdrFit` — every Section's wrap_nat fields fit in UInt64.

`LayoutEngine.layoutAlreadyValid` was rewritten from imperative
`Id.run do` to declarative `decide (sectionsNonOverlapping ∧
shdrSectionDisjoint)` to make `layoutAlreadyValid_of_spliceRegionsDisjoint`
a one-line bridge.  Equivalent on real ELFs (49/49 tests confirm).

Bundle-form `parse_encode_roundtrip_witness (e : ParsedElf)
(hDRW : DecodeRoundtripWitness e.elf)` retained for backward
compatibility; derives from the unconditional theorem via
`decodeRoundtripWitness_of_preconditions`.

**Parser-output → EncodePreconditions bridge.**
`encodePreconditions_of_parser bs shdrs e` derives 10 of 11 fields
(`identValid`, `typesMatch`, `nullEmpty`, `sizeFit`, `syncOk`,
`headerFit_entry`, `headerFit_phoff`, `headerFit_shoff`, `phdrFit`,
`shdrFit`) from parser-output structural facts plus
`e.phdrs = decodePhdrs ...` and `shdrs = decodeShdrs ...`.
Caller still supplies `spliceDisjoint` directly — the parser doesn't
enforce pairwise region disjointness (and shouldn't; overlapping
sections are spec-valid).  ROADMAP item 1.3a has the per-clause
helper inventory.

`LayoutEngine.layoutForEncoding_produces_spliceRegionsDisjoint`
discharges `spliceDisjoint` for the layout-pass's *output* under
`section[0].type = SHT_NULL` and `ehdrSize ≤ phoff.val`.  Wiring it
into a `parse_encode_layout_roundtrip` for the not-already-valid
encoder branch is op-level Tier D (ROADMAP 5.1).

**Per-content forward roundtrips**: 5 of 6 `SectionContent` cases
(`raw`, `strtab`, `versym`, `dynsym`, `dynamic`) have explicit
`decodeX_encode_X` lemmas in `ByteRoundtrip.lean`; `nobits` writes
no bytes so the dispatch is trivial.  The `.dynamic` case uses
loop-induction via `decodeDynamic_writeArray_eq` + a strengthened
`dynamicTerminated` invariant (DT_NULL bookend + no early null)
split out from `dynamicWellFormed`.

**Per-struct forward roundtrips**: all 7 fixed-layout structs
(`ElfIdent`, `ElfHeader`, `ProgramHeader`, `SectionHeader`,
`DynEntry`, `Symbol`, `Vernaux`) have `_decode_write` lemmas
DSL-emitted from `elf_schema` declarations.  Window-form decoder
bridges (`decoder_eq_slice`) for `decodeHeader`, `decodePhdr`,
`decodeShdr`, `decodeSym`, `decodeDynEntry` decouple per-byte
preservation from buffer shape.

**`@[irreducible]` discipline** on `Encoder.encodeBody` and
`Encoder.encode` (with `_eq` unfolding lemmas) prevents the kernel
from re-elaborating the encoder pipeline on every per-byte access
proof — the convergent recommendation from EverParse / Narcissus /
Lean 4 PR #4061.

`.verneed` / `.hash` / `.gnu.hash` flow through
`section_decode_encode` as `.raw bs` (these were demoted at the
byte layer).  The typed-section algebra constructs them via
`Adapter.ofElfFile`'s on-demand decode.  Forward
`Verneed.write_decode` for the typed-side roundtrip is pending and
tracked in ROADMAP item 4.2.

Axiom dependencies: `[propext, Classical.choice, Quot.sound]` plus 3
`bv_decide` axioms for the readU/writeU primitives. No `sorryAx`.

### Typed-algebra invariants: type-level, not predicate-level

`ValidElfFile` exposes structure that makes the byte layer's
8-clause decidable `IsValid` *vacuous by construction* on its
fields:

- `dynstr : StringSection` — the `StringSection.wf` field requires
  either size 0 or a trailing NUL.  the byte layer's `strtabsWellFormed` clause
  is gone because no other representation is constructible.
- `dynamic : Option (DynamicSection dynstr)` — `DynamicSection ds`
  stores every string-ref offset as `Fin ds.size`, so the byte
  layer's `dynamicWellFormed` clause "every string-ref entry's
  value fits in `.dynstr`" is implied by the type.
- `dynsym : Option (SymbolSection dynstr)` — `TypedSymbol.st_name`
  is also `Fin dynstr.size`.  the byte layer's `dynsymNamesInBounds` clause is
  likewise vacuous.
- No `IsValid` predicate on `ValidElfFile` itself — the type IS
  the predicate.

DT_STRTAB / DT_SYMTAB / DT_HASH / DT_GNU_HASH / DT_VERNEED / DT_STRSZ
are NOT stored as DynamicSection fields; they're DERIVED at encode
time via `assembleEntries` + `LayoutCtx`.  the byte layer's 6 `dynAddressCoherent*`
clauses and `dynStrszCoherent` clause disappear.

### Typed-algebra observables: per-op semantic correctness theorems

Every op in `Elf/Ops/` has at least one `_observable` theorem stating the
post-condition a caller can observe.  The
`growDynstrDynamicOp_observable` and `mapDynamicOp_observable`
combinators in `ObservableCombinators.lean` supply the shared skeleton
(existential for the post dynamic section + the lookup-resolved
offset); each op proves its op-specific `P` predicate inline.

### Adapter round-trip

`Elf/AdapterRoundtrip.lean` carries 8 preservation theorems:
`toElfFile_{header,phdrs}` (`@[simp]`, rfl-trivial because `toElfFile` ends
in a record override), `ofElfFile_{header,phdrs,dynstr,versym}`
(proved via `split at h` cascades over the nested
match/Except binds in `ofElfFile`), and composed
`roundtrip_{header,phdrs}` chaining both sides.  The file is
imported by `Patchelf.lean` so the theorems ship in the
default build target.

---

## Encoder pipeline

`encode : ElfFile → ByteArray` is a 3-phase transform:

1. **`syncDtStrszInFile`**: rewrite every DT_STRSZ entry's `value` to
   `.dynstr.bytes.size`. No-op if either `.dynamic` or `.dynstr` is
   absent.
2. **Conditional `layoutForEncoding`**: if `layoutAlreadyValid e` is
   false (sections overlap or overlap the shdr table), repack sections
   contiguously after `max(ehdrSize, phdrTableEnd)`, respecting
   `addralign`. Place the shdr table after all sections. Update
   `header.shoff` and PT_INTERP/PT_DYNAMIC phdr offsets + sizes to
   match the new layout. Skipped when the existing layout is already
   valid (preserves byte-for-byte stability on no-growth ops).
3. **Splice pipeline**: allocate `zeroBytes (encodedFileSize e)`,
   splice header at 0, phdr table at `phoff`, shdr table at `shoff`,
   then each non-NOBITS non-NULL section at its offset.

---

## Known gaps and divergences

See `research/ROADMAP.md` for the full prioritized list.  Highlights:

### Correctness gap: PT_LOAD phdrs not updated by layout pass

`layoutForEncoding` rewrites every section's `offset` and updates
the `header.shoff` and the PT_INTERP / PT_DYNAMIC phdr offsets, but
**does NOT update PT_LOAD phdrs** (other than PT_INTERP/PT_DYNAMIC).
If the layout pass moves a section that's mapped by a PT_LOAD
segment, that segment's `p_offset`/`p_filesz`/`p_memsz` continue to
reference the OLD location — the resulting binary will load wrong
file bytes at runtime.

Why this isn't visible in the test suite: every test fixture is
hand-rolled with a PT_LOAD that covers only `[0, 64)` (the ELF
header) or similarly small windows that don't overlap the sections
that get reflowed.  Real Linux binaries' PT_LOADs span dynstr /
dynamic / etc., so this gap fires there.  C++ patchelf solves it by
reserving end-of-file space and rewriting PT_LOAD entries; we
don't have that machinery.  Tracked as part of ROADMAP §3.5/§3.6.

### Priority 1 gaps (verification depth)

- **Byte-layer `IsLoadable` / `IsFullyValid` decorative** — defined
  but never established or preserved.  The typed algebra obviates
  this at the type level for the dynamic/dynstr/dynsym clauses, but
  the phdr/shdr overlap + PT_LOAD alignment invariants still apply
  to the byte layer.
- **`syncDtStrszInFile` / `layoutForEncoding` preservation unproved** —
  pure functions that should preserve the byte layer's `IsValid`
  but no theorem says so.
- **`spliceDisjoint` from realistic inputs** — caller-supplied for
  parser output (parser shouldn't enforce, since overlapping
  sections are spec-valid).  `layoutForEncoding_produces_spliceRegionsDisjoint`
  in `LayoutEngine.lean` discharges this for the layout-pass's
  output unconditionally under two parser-derivable preconditions
  (`section[0].type = SHT_NULL` and `ehdrSize ≤ phoff.val`).
  Op-level Tier D (ROADMAP 5.1) is now unblocked.

### Priority 2 gaps (test / spec coverage)

- **Several observables satisfied by identity on no-op inputs**
  (addDebugTag on files with DT_DEBUG, removeNeeded on absent libs).
  Identity-adversary test doesn't bite.
- **No dedicated parse∘encode identity smoke test.**

### Priority 3 gaps (C++ patchelf parity)

- **Multi-op ordering.** CLI uses argv order; C++ uses canonical
  (prints first, mutations second).
- **`shrinkRPath` FS probing.** Takes a static prefix list instead
  of probing the filesystem.
- **`.gnu.hash` rebuild** in `--rename-dynamic-symbols` — rejected
  precondition, not implemented.
- **Verneed update in `--replace-needed`** — rewrites
  `.dynamic`+`.dynstr` but not `vn_file` in `.gnu.version_r`.
- **PT_GNU_STACK append** when missing — patchelf no-ops, C++ appends.
- **`--page-size`** parsed/stored but not consumed by layout pass.
- **`--debug`** trace output not wired.
- **Generic `shdrIdxMismatch` ParseError** — per-clause classification
  would surface specific IsValid violations.

---

See `research/ROADMAP.md` for forward-looking work items.
