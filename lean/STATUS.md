# patchelf (Lean 4 port) — status and known gaps

> **Layout work landed.** The PT_LOAD / DT_* coherence gap
> (formerly the central correctness bug) is closed by `growEOF`
> + `syncDtAddrTagsInFile` + a pre-write validator
> (`Patchelf/Elf/{GrowEOF,Validate}.lean`). `set-rpath` on real
> Linux ET_DYN binaries now produces output that runs.
> [`research/REWRITE-PHASE-3-DESIGN.md`](../research/REWRITE-PHASE-3-DESIGN.md)
> remains the planning document for the broader unification arc;
> the §"Known gaps" list below records what didn't land
> (BSS-collision binaries fall back to `layoutForEncoding`'s
> repack and are caught by the validator at write time).

This document records the **current state** of the Lean 4 patchelf
port — what works, what doesn't, what's verified, what isn't.

For the **architectural model** (three-layer stack, validity ladder,
pipeline, op convention, verification surface), see
[`ARCHITECTURE.md`](ARCHITECTURE.md).

For **forward-looking work items**, see [`research/ROADMAP.md`](../research/ROADMAP.md).

For a **complete inventory** of every theorem/definition by file, see
[`INVENTORY.md`](INVENTORY.md).

---

## What works end-to-end

The CLI is built on `lean4-cli` and is **subcommand-shaped** (e.g.
`patchelf set-rpath /a foo`), a deliberate divergence from C++
patchelf's argv-order flag stack. See `Patchelf/CLI.lean` for the
top-level command tree.

All 14 mutating ops plus 6 print ops work against real ELF fixtures:

| Subcommand | Status | Notes |
|---|---|---|
| `set-os-abi <abi> <file>` | works | numeric or canonical name |
| `print-os-abi <file>` | works | |
| `set-execstack` / `clear-execstack <file>` | works | no-op when no PT_GNU_STACK |
| `print-execstack <file>` | works | prints `execstack: X/-/?` |
| `remove-rpath <file>` | works | filter-shaped dyn mutation |
| `remove-needed <lib> <file>` | works | |
| `remove-soname <file>` | works | |
| `print-rpath` / `print-needed` / `print-soname` / `print-interpreter <file>` | works | `print-soname` emits nothing when DT_SONAME absent |
| `set-rpath [-f] <path> <file>` | works | retag existing or insert new |
| `add-rpath [-f] <path> <file>` | works | composes with existing rpath |
| `shrink-rpath [-f] [--allowed-prefixes p:...] <file>` | works | FS-existence filter by default; prefix filter with flag |
| `add-needed <lib> <file>` | works | inserts at FRONT of `.dynamic` (matches C++) |
| `replace-needed <old> <new> <file>` | works | reuse-offset fast path + grow path |
| `set-soname <soname> <file>` | works | |
| `set-interpreter <path> <file>` | works | single unified op (no in-slot/grow split) |
| `add-debug-tag <file>` | works | |
| `no-default-lib <file>` | works | |
| `rename-dynamic-symbol <old> <new> <file>` | works | rejects binaries with `.gnu.hash` |
| `rename-dynamic-symbols <map-file> <file>` | works | |
| `clear-symbol-version <sym> <file>` | works | retargets matching versym entries to VER_NDX_GLOBAL |
| `validate <file>` | works | runs the pre-write validator on a file as-is |
| `roundtrip <file>` | works | parse + re-encode (no semantic mutation; useful for codec testing) |
| `parse <file>` | works | brief structural summary on stdout |

`-f` is `--force-rpath` (emit DT_RPATH instead of DT_RUNPATH);
declared per-subcommand on the rpath ops.

**Per-subcommand flags on every mutating op** (injected by
`mutatingFlagsExt` in CLI.lean; read-only subcommands reject these):

- `--output PATH` / `-o` — write target override (default: in-place).
- `--no-validate` — skip the loader-coherence validator (UNSAFE; see
  `Validate.lean`).
- `--page-size N` — override the layout engine's PT_LOAD alignment
  (e.g. `0x10000` for AArch64). Threaded through `encodeWith` →
  `growEOFWith`.
- `--debug` — emit `  -> ...`-prefixed trace lines on stderr via
  `Patchelf.Log` (fully wired through `runWith` and
  `writeWithValidation`).

Global: `--help` / `--version` / `help <cmd>`; `@file` argument
resolution in `Main.resolveArg`.

Multi-op invocations: chain CLI calls via the shell
(`patchelf set-rpath /a foo && patchelf add-needed libbar.so foo`).
The single-process multi-op CLI was retired with the lean4-cli
migration.

**Test status:** all 49 shell tests in `tests/cases/` pass.

---

## Codebase size

For the file-by-file architecture, see
[`ARCHITECTURE.md` § File map](ARCHITECTURE.md#file-map). For the
exhaustive declaration inventory, see
[`INVENTORY.md`](INVENTORY.md).

Total Lean source: ~15,600 LOC. Distribution by category:

| Category | LOC | What it is |
|---|---|---|
| Verification (`ByteRoundtrip` + `ByteLevel` + `LayoutEngine` + `Basic` + `AdapterRoundtrip`) | ~5,900 | Tier D `parse_encode_roundtrip` infrastructure |
| DSL + op-layer infra (`SchemaDSL` + `Schemas` + `Adapter` + `ObservableCombinators`) | ~2,300 | `elf_schema` elaborator + 7 invocations + bridge |
| Wire codec + types (Splice, Layout, Decode, Parser, ParseHeader, Reader, Writer, Serialize, DynamicParse/Encode) | ~1,700 | Reader/Writer + Splice + parsing primitives + per-clause ParseError |
| Typed-section types (DynamicSection, StringSection, SymbolSection, ValidElfFile, InterpSection, AuxSections) | ~630 | Typed algebra + StringSection lookup roundtrip |
| Layout pipeline + validator (`Encoder` + `GrowEOF` + `Validate`) | ~1,500 | growEOF + syncDtAddrTagsInFile + pre-write validator + `syncDtStrszInFile_preserves_valid` |
| `SectionOps` | ~420 | `updateSectionContent` + projection / index-preservation / typed-accessor preservation helpers |
| 14 ops (`Elf/Ops/*.lean`) | ~1,000 | mutating operations |
| CLI + Main + Log | ~990 | lean4-cli subcommand tree + stderr trace logger |
| Tactic (`SpliceSimproc*`) | ~200 | `simp_splice` macro + `[splice_simp]` simp set |
| Misc (root, ElfFile, DynamicLemmas) | ~960 | structural |

`ByteRoundtrip.lean` (~3,000 LOC) and `SchemaDSL.lean` (~1,200 LOC) are
the two largest files.  Every file builds; zero `sorry`.

---

## Invariants and theorems

### Byte-layer `IsValid` (8 clauses, decidable)

`header_counts`, `sections_wf`, `strtabs_wf`, `dynamic_wf`,
`dynsym_wf`, `content_wf`, `types_distinct`, `names_unique`.  See
`ElfFile.lean` for clause definitions.  Typed-algebra ops don't
carry `_preserves_valid` theorems — `ValidElfFile` is typed, not
predicate-bundled, so the type itself IS the invariant.

### `IsLoadable` and `IsFullyValid`

`IsLoadable` adds non-overlapping sections + PT_INTERP/PT_DYNAMIC
phdr offset agreement + PT_LOAD alignment congruence.
`IsFullyValid` further adds `dynamicAddressCoherent` — a single
record covering DT_STRTAB / DT_SYMTAB / DT_HASH / DT_GNU_HASH /
DT_VERNEED address-coherence plus DT_STRSZ size-coherence (the
latter is the `strsz_size` field of `dynamicAddressCoherent`,
not a separate clause).

`IsLoadable` is consumed by `Validate.IsLoadableBytes` at the CLI
write boundary.  Parser still returns `ParsedElf` (`IsValid` only)
and no op carries an `_preserves_loadable` theorem; see ROADMAP
item 1.1 for the unfinished static-side threading.

### Tier D: `parse_encode_roundtrip` — UNCONDITIONAL

`Patchelf.Elf.parse_encode_roundtrip (e : ParsedElf)
(hPre : EncodePreconditions e.elf) : parse (encode e.elf) = .ok e`.

This is a **codec-asymmetry guard for encoder/parser refactors**, not
a "byte-level correctness" theorem in any user-facing sense.  It rules
out the silent bug class where the encoder writes pattern A and the
parser reads pattern B with A ≠ B such that the round-trip cancels in
shell tests.  It does NOT catch wire-format / spec disagreement
(`e_machine` set to a value the kernel rejects but Lean's parser
accepts) or any post-write loader-coherence violation — those live
in `Validate.IsLoadableBytes`, run at write time.

The byte-level codec is verified end-to-end under the
`EncodePreconditions` bundle (11 explicit, decidable preconditions —
9 conceptual clauses, with `headerFit_*` exploded into 3 separate
fields).  All decoder-inverse facts are proved:

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
- `sizeFit` — each `s.shdrSize < UInt64.size`.  For non-NOBITS
  sections this is `encodedSize`; for NOBITS it's the declared
  `memSize` carried on `SectionContent.nobits` (so the shdr table
  preserves the BSS allocation size after a parse/encode roundtrip).
- `nullEmpty` — SHT_NULL sections have `.raw ByteArray.empty` content.
- `headerFit_{entry,phoff,shoff}` — each ElfHeader wrap_nat field's
  `.val` fits in UInt64 (parser-derivable: came from `(readU64 ...).toNat`).
- `phdrFit` — every ProgramHeader wrap_nat field fits in UInt64.
- `shdrFit` — every Section's wrap_nat fields fit in UInt64.

**Parser-output → EncodePreconditions bridge.**
`encodePreconditions_of_parser bs shdrs e` derives 10 of 11 fields
(everything except `spliceDisjoint`) from parser-output structural
facts plus `e.phdrs = decodePhdrs ...` and `shdrs = decodeShdrs ...`.
Callers supply `spliceDisjoint` directly — the parser doesn't
enforce pairwise region disjointness (and shouldn't; overlapping
sections are spec-valid).  See ROADMAP item 1.3a for the per-clause
helper inventory.

`LayoutEngine.layoutForEncoding_produces_spliceRegionsDisjoint`
discharges `spliceDisjoint` for the BSS-collision-fallback branch
under `section[0].type = SHT_NULL` and `ehdrSize ≤ phoff.val`.  An
analog for the primary `growEOFWith` branch is the unblocker for
op-level Tier D (ROADMAP §5.1).

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

`Encoder.encodeBody` and `Encoder.encode` are `@[irreducible]` (with
`_eq` unfolding lemmas); removing the attribute makes per-byte access
proofs time out at >32M heartbeats.

`.verneed` / `.hash` / `.gnu.hash` flow through
`section_decode_encode` as `.raw bs` (demoted at the byte layer).
The typed-section algebra constructs them via `Adapter.ofElfFile`'s
on-demand decode.  Forward `Verneed.write_decode` for the typed-side
roundtrip is pending; ROADMAP item 4.2.

Axiom dependencies: `[propext, Classical.choice, Quot.sound]` plus 4
`bv_decide` axioms for the readU/writeU primitives. No `sorryAx`.

### Typed-algebra invariants and observables

For the structural picture (why `ValidElfFile` makes byte-layer
`IsValid` clauses vacuous, why DT_* coherence tags disappear, the
`<op> + _observable + _*_preserved` convention), see
[`ARCHITECTURE.md` § Layer 3](ARCHITECTURE.md#layer-3--typed-section-algebra)
and [§ Op convention](ARCHITECTURE.md#op-convention).

**Proved status:** every op in `Elf/Ops/` has at least one
`_observable` theorem stating its post-condition. The
`growDynstrDynamicOp_observable` and `mapDynamicOp_observable`
combinators in `ObservableCombinators.lean` supply the shared
skeleton; each op proves its op-specific `P` predicate inline.

### Adapter round-trip

`Elf/AdapterRoundtrip.lean` carries 8 preservation theorems:
`toElfFile_{header,phdrs}`, `ofElfFile_{header,phdrs,dynstr,versym}`,
and composed `roundtrip_{header,phdrs}`.  Imported by `Patchelf.lean`
so the theorems ship in the default build target.

---

## Encoder pipeline

For the diagram, see
[`ARCHITECTURE.md § Encoder pipeline (zoom-in)`](ARCHITECTURE.md#encoder-pipeline-zoom-in).
`Encoder.encode` and `Encoder.encodeWith pageSize?` (`Encoder.lean`)
implement:

1. **`syncDtStrszInFile`** — rewrite every DT_STRSZ entry's `value` to
   `.dynstr.bytes.size`. No-op if either `.dynamic` or `.dynstr` is
   absent.
2. **`prepLayoutForEncodeWith pageSize?`** — identity when
   `layoutAlreadyValid e = true` (preserves byte-for-byte stability on
   no-growth ops). Otherwise composes:
   1. **`growEOFWith pageSize?`** (`GrowEOF.lean`) — append-at-end
      strategy: identify "stale" sections (those whose `[offset,
      offset + encodedSize)` overlaps another section or the shdr
      table), append each to a new region rounded up from the last
      PT_LOAD's `(p_offset + p_memsz, p_vaddr + p_memsz)` to
      `max(pageSize?, maxPtLoadAlign)`. Each moved section gets
      matching `(offset, addr)` deltas so `p_offset ≡ p_vaddr
      (mod p_align)` survives. The last PT_LOAD's `filesz`/`memsz` are
      extended to cover the appended region; PT_INTERP/PT_DYNAMIC and
      `header.shoff` get retargeted at the moved sections.
      `pageSize?` defaults to auto-detection from existing PT_LOAD
      `p_align` values; passing `0x10000` is the AArch64 path.
      Falls back to `layoutForEncoding` (which doesn't preserve
      PT_LOAD coverage) when `canExtendLastPtLoad` rejects — typically
      because the last PT_LOAD has a large BSS that the appended
      region would clobber. The validator (step 3 below) rejects the
      resulting bytes at write time.
   2. **`syncDtAddrTagsInFile`** — rewrite `.dynamic`'s
      DT_STRTAB / DT_SYMTAB / DT_HASH / DT_GNU_HASH / DT_VERNEED /
      DT_VERSYM / DT_JMPREL / DT_REL / DT_RELA tags to point at the
      moved sections' new addresses (analog of C++ patchelf's
      DT_* update block). DT_JMPREL/REL/RELA look up by section
      name (`.rela.plt`, `.rel.dyn`, `.rela.dyn`).
3. **`encodeBody`** — allocate `zeroBytes (encodedFileSize e)`,
   splice header at 0, phdr table at `phoff`, shdr table at `shoff`,
   then each non-NOBITS non-NULL section at its offset.
4. **Pre-write validator (`Validate.lean`)** — at the CLI's I/O
   boundary, the post-encode bytes are re-parsed and checked against
   `IsLoadableBytes` (decidable: `IsValid + sectionsNonOverlapping +
   shdrSectionDisjoint + ptInterpAgreement + ptDynamicAgreement +
   segmentCongruence + sectionFileInSomePtLoad`). On failure the CLI
   exits 5 with the failing clause on stderr; the file is unchanged
   on disk. `--no-validate` opts out (UNSAFE).

`Encoder.encode` is `@[irreducible]`; use `encode_eq` for
propositional unfolding.

`SectionContent.nobits` carries `(memSize : Nat)` so the shdr table's
`size` field survives the parse/encode roundtrip even though no bytes
are written. `Section.shdrSize` returns `encodedSize` for non-NOBITS
and `memSize` for NOBITS.

---

## Known gaps and divergences

See `research/ROADMAP.md` for the full prioritized list.  Highlights:

### PT_LOAD layout — closed for the common case

The previous `layoutForEncoding` repack stomped on PT_LOAD coverage
when sections moved.  `growEOF` (`GrowEOF.lean`, ~410 LOC) replaces
it as the primary layout strategy: stale sections are appended at
file end, the last PT_LOAD's `filesz`/`memsz` are extended to cover
them, and `(offset, addr)` deltas are kept equal so segment
congruence survives.  `syncDtAddrTagsInFile` rewrites the matching
DT_* address tags.  `set-rpath` on real ET_DYN binaries (e.g.
`/usr/bin/hello`) now produces output that runs.

**Residual gap: large-BSS binaries.**  When the last PT_LOAD has
significant BSS (e.g. coreutils `ls` with ~0x97000 bytes of BSS),
`canExtendLastPtLoad` rejects the extension because the appended
region's vaddr would collide with already-allocated BSS.
`growEOFWith` falls back to `layoutForEncoding`'s repack, which
produces non-loadable bytes; the pre-write validator
(`Validate.lean`) catches this and refuses the write with exit 5.
Allocating a fresh PT_LOAD by growing the phdr table — the
fully-general fix — is left for a follow-up (see ROADMAP §3.5b).

### Priority 1 gaps (verification depth)

- **Parser doesn't establish `IsLoadable`** — `Parser.parse` still
  returns only `IsValid`.  `Validate.IsLoadableBytes` is run on
  encoder output at write time, but no op-level
  `_preserves_loadable` theorem exists, and there's no static link
  between parser output and validator success.
- **`growEOFWith`, `syncDtAddrTagsInFile`, `layoutForEncoding`
  preservation unproved.** `syncDtStrszInFile_preserves_valid`
  landed (`Encoder.lean`); the other three pre-encode pure functions
  still have no preservation theorems.
- **`spliceDisjoint` from realistic inputs — DONE.**
  `growEOFWith_produces_spliceRegionsDisjoint` (`GrowEOF.lean`)
  discharges all 3 branches (fast path / fallback / main path) under
  the structural input invariants `headerPhdrDisjoint` /
  `headerShdrDisjoint` / `phdrShdrDisjoint` / `headerSectionDisjoint` /
  `phdrSectionDisjoint` plus `hSection0Null`.  The unified
  `PlaceFold.{placeStep, placeFold, Placement, PairDisjoint, FoldInv}`
  scaffolding (`LayoutEngine.lean`) is parameterized over `verbatim`,
  `transform`, and `baseOffset`; both `layoutForEncoding` (with
  `Section.withOffset`, `baseOffset = 0`) and `growEOFWith`'s
  `appendStaleSections` (with addr-shifting transform,
  `baseOffset = startOffset`) are specializations.  Op-level Tier D
  (ROADMAP §5.1) is now unblocked.

### Priority 2 gaps (test / spec coverage)

(All landed: `addDebugTag_observable_strong`,
`removeNeeded_needed_size_lt`, and shell test 00.  See ROADMAP §2.)

### Priority 3 gaps (C++ patchelf parity)

- **`.gnu.hash` rebuild** in `rename-dynamic-symbols` — rejected
  precondition, not implemented.
- **Verneed update in `replace-needed`** — rewrites
  `.dynamic`+`.dynstr` but not `vn_file` in `.gnu.version_r`.
- **PT_GNU_STACK append** when missing — `Ops/Execstack.lean` only
  maps over existing PT_GNU_STACK phdrs; C++ appends when absent.
  Synthesizing a new phdr requires growing the phdr table.
- **Allocate a fresh PT_LOAD when extension is unsafe.** `growEOFWith`
  bails to `layoutForEncoding` (caught by the validator) when
  `canExtendLastPtLoad` rejects.  C++ patchelf's
  `rewriteSectionsLibrary` allocates a new PT_LOAD; that path needs
  phdr-table growth, which we don't have.
