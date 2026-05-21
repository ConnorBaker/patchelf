# Layout-engine data-model audit (Phase L0)

> **ARCHIVED — design path not taken.** Preparation for a
> layout-engine pivot that was subsequently bypassed.  The
> "M1-M7 data-model changes" proposed here (section-bytes
> accessor, full Elf64_Sym, verneed model, hash-table
> model+rebuild) were either superseded by the typed-section
> algebra or are no longer relevant.  The "L0/L1/L3/L5" phase
> plan never materialized.  The §W-class table of which sections
> grow/are rewritten by which patchelf op remains useful
> reference material about C++ `patchelf.cc` behavior.  Kept as
> historical record.

## Purpose

Before porting `rewriteSections` from `src/patchelf.cc`, enumerate every ELF
section the layout engine reads or writes, and categorize each against the
current Lean `ElfFile` data model. Any section the layout engine **touches**
needs to be represented in the model so op correctness can be proved at the
type level rather than delegated to the encoder convention.

Scope: sections referenced by any current op (including the 8 rejected
layout-engine ops: setRpath, addNeeded, replaceNeeded, setSoname,
addDebugTag, noDefaultLib, renameDynamicSymbols, and setInterpreter when
the path overflows the existing slot) or by the layout-engine pipeline
itself.

## Current model

`ElfFile` (lean-v2/PatchelfV2/Elf/ElfFile.lean:49):

| Field | Representation | Status |
|---|---|---|
| `bytes` | `ByteArray` | opaque raw file |
| `header` | `ElfHeader` | decoded |
| `phdrs` | `Array ProgramHeader` | decoded |
| `shdrs` | `Array SectionHeader` | decoded |
| `shstrtab` | `StringTable` | broken out |
| `dynstr` | `Option StringTable` | broken out |
| `dynamic` | `Option (Array DynEntry)` | broken out |
| `dynsym` | `Option (Array UInt32)` | **stub** — only `st_name` offsets, not full `Elf64_Sym` records |
| `interp` | `Option ByteArray` | broken out (added 2026-05-05) |

Everything else is represented only via `e.bytes` + `shdrs[i].offset / size`.

## Sections patchelf touches

Enumerated from `grep -nE 'findSectionHeader|replaceSection|tryGetSectionSpan' src/patchelf.cc`.

### R — read only (query, no mutation)

| Section | C++ site(s) | Layout-engine uses? | Current model |
|---|---|---|---|
| `.MIPS.xhash` | rewriteHeaders:1261 | yes (MIPS only) | opaque bytes |
| `.rel.plt` / `.rela.plt` / `.rela.IA_64.pltoff` | rewriteHeaders:1263-1266 (DT_JMPREL) | yes | opaque bytes |
| `.rel.dyn` / `.rel.got` | rewriteHeaders:1271-1274 (DT_REL) | yes | opaque bytes |
| `.rela.dyn` | rewriteHeaders:1281 (DT_RELA) | yes | opaque bytes |
| `.rld_map` | rewriteHeaders:1306 (DT_MIPS_RLD_MAP_REL) | yes (MIPS only) | opaque bytes |

**Verdict for R-class:** the layout engine reads their `sh_addr` / `sh_offset`
after the shift to patch DT_* entries. It does **not** read or write section
contents. Current opaque-bytes representation is sufficient *if* the shdr's
offset/addr are kept accurate — that's already part of the 6-clause validity.

### W — written (size or content modified)

| Section | C++ site(s) | Size-growing? | Current model |
|---|---|---|---|
| `.interp` | `setInterpreter` (1514) | no (replaceSection with new size; fits-in-slot or triggers layout) | broken out |
| `.dynstr` | all growing ops (1477, 1727, 1829, 1930, 2260) | **yes** | broken out |
| `.dynamic` | addNeeded/noDefaultLib/addDebugTag (1486, 1740, 1942, 2004, 2037) | **yes** (new entry inserted) | broken out |
| `.dynsym` | renameDynamicSymbols (implicit via dynsym st_name writes) | no (values only; size constant) | **stub** (st_name offsets only) |
| `.gnu.version_r` | replaceNeeded (1893): verneed string-offset rewrites | no (values only) | **not modeled** |
| verneed-strings section (usually = `.dynstr`) | replaceNeeded (1893): strings appended via `replaceSection` | yes | broken out if == `.dynstr`; otherwise **not modeled** |
| `.hash` | rebuildHashTable (2208) from renameDynamicSymbols (2266) | no — rebuilt in place, existing size unchanged per bucket/chain structure (but see note) | **not modeled** |
| `.gnu.hash` | rebuildGnuHashTable (2076) from renameDynamicSymbols (2265) | no — rebuilt in place | **not modeled** |

Note on hash tables: sizes CAN change if the number of dynsyms changes
(which happens when a rename removes a duplicate or adds a new symbol at
a new bucket). For `renameDynamicSymbols` specifically, the dynsym count
is constant (every rename maps 1:1), so hash-table bucket sizes stay stable.
The bucket/chain contents change. C++ rebuilds both tables from scratch
using the new `.dynstr`.

**Verdict for W-class:**
- `.dynsym` is **partially modeled**. The full `Elf64_Sym` record is
  `{st_name, st_info, st_other, st_shndx, st_value, st_size}`. We keep only
  `st_name`. That's enough for `renameDynamicSymbols` and for validating
  string-offset bounds (clause 6). But **`rewriteSymbolTable`** in the
  layout engine (C++ lines 1321-1347) rewrites every symbol's `st_shndx`
  and `st_value` after a shift — which the stub cannot represent. **Blocker
  for L5.**
- `.gnu.version_r` (verneed table) is **not modeled**. `replaceNeeded`
  rewrites `Elf_Verneed` entries' `vn_file` fields to point at the new
  string offsets in `.dynstr` (or in a separate version-r-strings
  section). Currently the op doesn't touch verneed; our `replaceNeeded`
  is known-incomplete for binaries that carry verneed entries for the
  renamed libraries. **Blocker for replaceNeeded correctness**, orthogonal
  to the layout engine.

### S — spatial-only (sh_offset moves, content unchanged)

All other sections. `rewriteSections` computes new offsets for every
non-SHT_NOBITS section and (in the library case) splices them into the
appended region, or (in the executable case) shifts the entire file.

**Verdict:** the opaque-bytes model works for these, provided:
1. We can read a section's bytes at `e.bytes[shdrs[i].offset..offset+size)`.
2. After a shift, those bytes get copied to the new offset.
3. Shdr entries get their `sh_offset` rewritten.

All three are mechanical and don't require modeling the section contents.

## Phdrs patchelf touches

| Phdr type | C++ site | Modeled? |
|---|---|---|
| `PT_INTERP` | setInterpreter phdr update (already implemented) | yes (phdr offset/filesz/memsz) |
| `PT_DYNAMIC` | writeReplacedSections:725 (phdr offset sync with `.dynamic`) | yes |
| `PT_NOTE` | writeReplacedSections:744, normalizeNoteSegments:1116 | yes (phdr field access) |
| `PT_MIPS_ABIFLAGS` | writeReplacedSections:776 (phdr follows `.MIPS.abiflags` section) | yes |
| `PT_GNU_PROPERTY` | writeReplacedSections:788 (phdr follows `.note.gnu.property`) | yes |
| `PT_PHDR` | rewriteSectionsExecutable (1029): phdr 0 offset/vaddr may shift | yes |
| `PT_LOAD` | rewriteSectionsExecutable: boundaries may grow a page | yes |

All phdr fields are already in the model. The layout engine manipulates them
by index, which is straightforward.

## Special cases

### Section layout invariants

The layout engine reorders the shdr table. Some invariants:

- Shdr[0] must be `SHT_NULL` (clause 3 of IsValid — already enforced).
- `.shstrtab` index is stored in `header.shstrndx` (clause 1 — already enforced).
- Within a PT_LOAD, sh_offset must be monotone. The layout engine preserves this.
- PT_NOTE phdrs may cover multiple SHT_NOTE sections; `normalizeNoteSegments`
  splits them. Not currently modeled in the 6-clause validity.

### `replacedSections` map

C++ maintains `std::map<SectionName, std::string>` tracking which sections
have been rewritten in memory. On `writeReplacedSections`, it walks this
map and splices each replaced section into the new file layout. In Lean this
would be a `Std.HashMap` or an `Array (SectionName × ByteArray)` passed
through the layout pipeline — it's transient state within the engine, not
part of `ElfFile`.

### SHT_NOBITS

`.bss` and similar SHT_NOBITS sections have `sh_size` but no file bytes. The
encoder must not splice bytes for them. Currently this is not tested; the
encoder's `spliceSectionByName` is only called for `.dynstr`, `.dynamic`,
`.interp` which are all SHT_PROGBITS/SHT_STRTAB/SHT_DYNAMIC (non-NOBITS).
The layout engine walks ALL sections, so it must check `sh_type != SHT_NOBITS`
before reading file bytes.

## Required data-model changes for the layout engine

Ordered by how load-bearing each is for the phases named in the session plan.

### Mandatory for L1-L5

**M1. Opaque section-bytes accessor.** The layout engine needs to read the
content of every non-broken-out, non-SHT_NOBITS section (to shift them to
new offsets). Currently expressed implicitly via `e.bytes.extract
shdrs[i].offset shdrs[i].offset+size`. A thin helper `sectionBytes : ElfFile
→ Fin shdrs.size → Option ByteArray` that respects SHT_NOBITS would make
the layout-engine code much cleaner. No new field, just a definition.

**M2. Full `.dynsym` model (full `Elf64_Sym`, not just st_name).**
`rewriteSymbolTable` (C++ 1321-1347) rewrites `st_shndx` and `st_value` for
every symbol after a shift — values change per-symbol because sections have
moved. The current `dynsym : Option (Array UInt32)` stub (st_name offsets
only) cannot represent this transformation. Replace with
`dynsym : Option (Array Symbol)` where `Symbol` is the full 24-byte ELF64
record. Fallout: `renameDynamicSymbols` and clause 6 (`dynsymNamesInBounds`)
both need to be updated to read `.st_name` off the full struct.

**M3. `RSCfg` / replacedSections state.** Layout-engine internal state
threading the "which sections have been replaced" map through the splice
pipeline. A pure record threaded by `structure RSCfg where replaced :
Std.HashMap SectionName ByteArray; curOff : Nat; ...`. Not part of `ElfFile`;
local to the engine.

### Mandatory for replaceNeeded correctness (orthogonal to layout engine)

**M4. Verneed model.** Add `verneed : Option (Array Verneed)` where
`Verneed` carries the `vn_file` offset (and a link to the strings section).
Fallout: the existing `replaceNeeded` is known-incomplete for binaries that
have verneed entries for renamed libraries; this is pre-existing not a
new bug.

### Mandatory for renameDynamicSymbols correctness (orthogonal to layout engine)

**M7. Hash-table model + rebuild.** `renameDynamicSymbols` rebuilds both
`.hash` (SysV-hash) and `.gnu.hash` (GNU-hash) from scratch after mutating
`st_name` offsets (C++ 2208, 2076). Current `.hash` and `.gnu.hash` are
opaque bytes in our model, so the rebuilt bucket contents are not in scope
— any real-world binary goes through `renameDynamicSymbols` and then the
loader's hash lookup fails because the bucket/chain structure still
references old name hashes. Requires modeling both tables as `HashTable`
and `GnuHashTable` records, plus the rebuild algorithm. Sizing: ~300 LOC
(parse + rebuild + size preservation theorem). Blocks
`renameDynamicSymbols` correctness at runtime even without the layout
engine.

### Optional (nice-to-have, unblocks specific correctness proofs)

**M5. Raw section data per shdr.** Carry the non-broken-out section bytes
as `sectionData : Array ByteArray` (one entry per shdr). Would let us drop
the `e.bytes` opaque representation entirely and make encode a pure
struct-to-bytes operation. Large refactor; the current prototype hasn't
needed it. Defer until M1 turns out to be insufficient.

**M6. Note-section structure.** Currently PT_NOTE splitting
(`normalizeNoteSegments`) reads note headers by raw byte access. A
`Array NoteSection` field would make the normalizer pure over the struct.
Only needed if we want to prove `normalizeNoteSegments_preserves_valid`
structurally.

## Recommended L0 outcome

Land **M1** and **M2** as precursor commits. Defer M3 until L1 (it's
engine-local state, not ElfFile structure). Defer M4 as an orthogonal
correctness fix for `replaceNeeded`. Defer M5/M6 until concretely needed.

**M1 sizing:** ~20 LOC (one definition + one lemma that it agrees with the
existing section bounds check).

**M2 sizing:** ~80-150 LOC. The `Symbol` record has 6 fields; need new
decoders/encoders plus updates to `renameDynamicSymbols` (field access
changes from `syms[i]` to `syms[i].st_name`) and to the parser (which
currently discards 5 of the 6 fields). The 6-clause IsValid's
`dynsymNamesInBounds` adapts trivially.

**Size-growing ops post-M2:** `renameDynamicSymbols` still grows `.dynstr`
but not `.dynsym` (value writes, not entry insertions). The CLI currently
rejects it with layout-engine; after M2 it needs the full layout engine
because the `.dynstr` growth shifts subsequent sections.

## What NOT to model

- **`.rela.*` / `.rel.*` internals.** Layout engine moves them but doesn't
  inspect them. No op rewrites their contents.
- **`.eh_frame`, `.text`, `.rodata`, `.data`, `.bss`, `.plt`, `.got`.** No
  patchelf op reads or writes these. Opaque-bytes pass-through is always
  sufficient.
- **`.hash` / `.gnu.hash` internals** — UNTIL we want `renameDynamicSymbols`
  to be correct. See M7 for the minimum viable modeling if/when that op
  becomes a priority. The rest of the ops are indifferent to hash-table
  contents (they only care about `sh_addr` / `sh_offset`, both already
  modeled via `shdrs`).

## Summary

Per the user's rule ("sections should be modeled if we need to touch or
modify them so we can enforce invariants"):

- Add M1 (section-bytes accessor) — minimal, unblocks layout-engine-clean code.
- Add M2 (full `.dynsym` model) — mandatory for `rewriteSymbolTable`.
- Add M4 (verneed model) — independent correctness fix for `replaceNeeded`.
- Add M7 (hash tables) — independent correctness fix for `renameDynamicSymbols`.
- Leave all other sections opaque. Their `sh_offset`/`sh_addr` are already
  in the model via `shdrs`, and that's all the layout engine inspects.

**Dependency graph:**

```
L1 (shiftFile) ────────┐
                       ├─> L3 (rewriteSectionsLibrary) ──> L5 (rewriteHeaders)
M1 (section accessor) ─┤                                   ──> L4 (rewriteSectionsExecutable)
M2 (full dynsym) ──────┘
M4 (verneed)      ─── orthogonal: unblocks replaceNeeded
M7 (hash tables)  ─── orthogonal: unblocks renameDynamicSymbols
```

Recommended ordering for the first layout-engine session: M1 + M2 first
(~200 LOC combined, no behavior change), then L1 (~100 LOC), then L3
(~150 LOC). That's ~450 LOC of the ~1000-LOC total and unblocks `setRpath`
+ `setSoname` + `addNeeded` + `addDebugTag` + `noDefaultLib` end-to-end
(the library-side ops). Executable-side ops (`setInterpreter` oversize,
binaries where shift happens) and hash-affected ops (`renameDynamicSymbols`)
stay rejected until L4 / M7 respectively.
