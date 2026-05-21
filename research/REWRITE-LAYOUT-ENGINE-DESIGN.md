# Layout Engine Design

> **ARCHIVED — design path not taken.** Written when size-growing
> ops were blocked on a layout-engine pivot.  The "broken-out
> sections" model + 7-phase
> `reserveEndOfFileRegion`/`writeReplacedSections`/`rewriteDynamicAddresses`
> decomposition proposed here was bypassed.  Today
> `layoutForEncoding` (in `lean/Patchelf/Elf/LayoutEngine.lean`)
> repacks sections only when the current layout has overlaps, and
> the typed-section algebra handles the rest without needing the
> full layout-engine apparatus.  All 14 size-growing ops
> (`setRpath`, `addNeeded`, `setSoname`, `renameDynamicSymbols`,
> …) work today.  The `IsValid` "clause 7c shdrSizesCoherent" /
> "clause 7d rawSectionBytesCoherent" references no longer apply.
> The §1 C++ pseudocode walkthroughs remain useful reference
> material about `rewriteSections`.  Kept for historical context.

**Status:** design pass, pre-implementation.

The "layout engine" is what unblocks size-growing ops in the V2 rewrite:
`setRpath`, `addNeeded`, `setSoname`, `renameDynamicSymbols`, and the
size-growing branches of `replaceNeeded`, `addDebugTag`, and
`noDefaultLib` (the last two fall back here only when the tag is
absent and must be inserted).

This doc answers:

1. **What does the C++ layout engine actually do?**
2. **What does our Lean model make easy vs. hard?**
3. **What's the minimum viable engine?**
4. **How should we simplify existing code first?**

Scope: shared-library ELFs (position-independent, movable sections).
Executables have a fundamentally harder problem (absolute references
to replaced sections become stale) and should be deferred.

## 1. What the C++ engine does

`rewriteSections(force)` in `src/patchelf.cc:1184`. Dispatches to one
of two paths based on `hdr()->e_type`:

- **Library** (`ET_DYN`): `rewriteSectionsLibrary()` — place replaced
  sections in a NEW region at the end of the file, load it via a new
  PT_LOAD segment at a fresh virtual-address page. Because the
  library is PIC, all references are relative/GOT-mediated; moving
  sections doesn't corrupt them.
- **Executable** (`ET_EXEC`): `rewriteSectionsExecutable()` — must
  keep replaced sections at their original virtual addresses
  (absolute refs); use `shiftFile` to prepend space at the start.
  Much harder. Defer.

The `force` parameter (`rewriteSections(true)` at line 2360) tells it
to run even when `replacedSections` is empty — used when no op grew
sections but the caller wants to re-emit. Rarely needed; skip.

### 1a. `rewriteSectionsLibrary` (src/patchelf.cc:806-971)

Pseudocode:

```
1. Scan phdrs, find:
     startPage = roundUp(max(p_vaddr + p_memsz) over all segments, align)
     firstPage = PT_PHDR.p_vaddr - PT_PHDR.p_offset  (virtual base)
     alignStartPage = max(PAGE_SIZE, max(p_align) over segments)

2. Pessimistic space estimate (treating all SHT_NOTE as possibly splitting):
     phtSize = roundUp((phnum + numNotes + 1) * phdrSize + ehdrSize, sectionAlignment)
     shtSize = roundUp(shnum * shdrSize, sectionAlignment)

3. Decide whether to relocate the PHT:
     relocatePht := any shdr at start of file that isn't
                    in replacedSections AND isn't replaceable
   (Old kernels buggy if PHDRs weren't at file start; try to keep them
    there unless forced to move.)

4. If NOT relocating PHT, claim every shdr whose offset ≤ phtSize as a
   replaceable section (moves their contents to the end-of-file region).

5. Compute neededSpace = shtSize + (phtSize if relocatePht) + sum of
   (replaced sections, rounded up to sectionAlignment).

6. Append neededSpace bytes (+1 for binutils readelf quirk) to file at
   startOffset = roundUp(fileContents->size(), alignStartPage).

7. Grow-or-reuse a final PT_LOAD segment covering [startPage, startPage+neededSpace)
   pointing at startOffset. (Optimization: extend the last PT_LOAD if it
   already ends at startOffset with PF_R|PF_W.)

8. If relocatePht: reserve phtSize at the start of the appended region
   and update header.e_phoff.

9. normalizeNoteSegments() — split each PT_NOTE covering N note sections
   into N single-section PT_NOTEs (the replaced-section loop below
   assumes 1-to-1).

10. writeReplacedSections(curOff := start of replaced-section region,
                          startAddr := lastSegAddr,
                          startOffset := appended region start):
    For each replaced section, in shdr sort order:
      - Optionally clobber old bytes with 'Z' (clobberOldSections flag).
      - memcpy new bytes at curOff.
      - Update shdr: sh_offset=curOff, sh_addr=startAddr+(curOff-startOffset),
                     sh_size=newBytes.size, sh_addralign=sectionAlignment.
      - Sync partnering phdr (PT_INTERP for .interp, PT_DYNAMIC for
        .dynamic, PT_NOTE for SHT_NOTE, PT_MIPS_ABIFLAGS, PT_GNU_PROPERTY).
      - curOff += roundUp(newBytes.size, sectionAlignment).

11. rewriteHeaders(newPhdrAddr):
    - Update every DT_* address entry in .dynamic that points at a
      replaced section (DT_STRTAB, DT_SYMTAB, DT_HASH, DT_GNU_HASH,
      DT_JMPREL, DT_REL(A), DT_VERNEED, DT_VERSYM, DT_MIPS_RLD_MAP_REL,
      DT_MIPS_XHASH).
    - Update every DT_STRSZ to the new dynstr size.
    - For each dynsym entry: if its st_shndx points at a replaced
      section, update st_value to the new sh_addr.
    - Serialize shdrs table at hdr.e_shoff.
    - Serialize phdrs table at newPhdrAddr-translated file offset.
    - Serialize header at offset 0.
```

### 1b. `writeReplacedSections` details (src/patchelf.cc:672-802)

Takes a running cursor `curOff` passed by reference. For each section
in `replacedSections` (iterated in shdr-sort order for stable
output), it:

- Clobbers the old bytes with `Z` if `clobberOldSections`.
- `memcpy`s new bytes to `fileContents->data() + curOff`.
- Updates the shdr in-place.
- Syncs the partnering phdr (if any).
- Rounds `curOff` up to `sectionAlignment`.

After the loop, `replacedSections.clear()`. Residual C++ side effect:
`curOff` is used by the caller to assert total space == `neededSpace`.

### 1c. Sections that get replaced

`replacedSections` is a `map<string, string>` populated by:

- `replaceSection(name, newSize)` when an op wants to resize a
  section (keeps the old contents padded with `\0` if newSize > old).
- `setReplacedSection(name, newContent)` when an op wants to write
  new contents directly.

Size-growing ops call these helpers. Examples:

- `modifySoname` → `setReplacedSection(".dynstr", newDynstr)` and
  `setReplacedSection(".dynamic", newDynamic)`.
- `addNeeded` → same two.
- `renameDynamicSymbols` → `.dynstr`, `.dynsym`, and optionally
  `.hash` / `.gnu.hash`.

### 1d. `shiftFile` (executable path only, src/patchelf.cc:491)

Not needed for library path. Shifts the entire file contents down by
N pages, splitting the straddling PT_LOAD segment into two. This is
the hard part that we defer.

### 1e. `normalizeNoteSegments` (src/patchelf.cc:1116)

When a single PT_NOTE segment covers multiple SHT_NOTE sections,
split it into one PT_NOTE per section (maintaining file-offset
ordering). `writeReplacedSections` assumes 1-to-1 PT_NOTE ↔
SHT_NOTE after this step.

## 2. What the Lean model makes easy vs. hard

### Easy

- **Typed phdrs/shdrs**: `e.phdrs : Array ProgramHeader`, `e.shdrs :
  Array SectionHeader`. Mutating these is just `Array.push`,
  `Array.map`, `Array.set`. No raw-byte math.
- **Broken-out sections**: `.dynstr`, `.dynamic`, `.dynsym`,
  `.interp`, etc. already live as separate fields. Swapping them
  with new-sized bytes doesn't corrupt any other typed field.
- **Encoder re-splices everything**: `encode` doesn't assume the
  splice is size-preserving anymore — it just splices at each
  shdr's recorded `sh_offset`. If we grow `e.bytes` AND update the
  shdrs' `sh_offset` values to point at the new slots, the encoder
  DTRTs without further changes.
- **`Encoder.splice_size` guarantees preservation**: any op that
  grows `e.bytes` via explicit `ByteArray.++` stays within the
  decidable-size budget.
- **Clause-7c (`shdrSizesCoherent`)**: the invariant we need to
  *preserve* after the layout pass. Every op that grows a section
  updates the matching shdr's `sh_size`; the engine additionally
  rewrites `sh_offset` on the relocated shdrs. No new invariant.
- **Clause-7d (`rawSectionBytesCoherent`)**: a layout-engine pass
  that writes the new bytes into `e.bytes` at the relocated offsets
  satisfies this for the three raw-bytes sections (.shstrtab,
  .dynstr, .interp), via `splice_extract_eq`. Same machinery as
  `setInterpreterLockstep`.

### Hard

- **The PHT relocation decision**: whether to move PHT to end-of-file
  depends on whether the start-of-file shdrs are replaceable. This
  is a coupled decision across many sections. Not hard to model,
  but introduces a boolean that propagates through the layout
  computation.
- **Page alignment**: `p_vaddr % p_align == p_offset % p_align`.
  `startPage % alignStartPage == startOffset % alignStartPage`. We
  haven't proved any alignment invariants yet; the engine introduces
  them. Concrete targets: `Nat.mod_add_mod` for page arithmetic.
- **DT_* address rewriting**: `rewriteHeaders` walks `.dynamic` and
  updates `d_un.d_ptr` for the 12 address-valued tags. Our
  `DynEntry` is tag-indiscriminate (`value : UInt64`); we don't know
  which tags carry addresses vs. offsets vs. counts. Either model
  this typed (introduce `DynValue` with address/size/offset/flags
  variants) or use a whitelist pattern-match in the rewrite.
- **Dynsym `st_shndx` / `st_value` rewriting**: after `.dynstr`
  moves, every dynsym with `st_shndx == <relocated section>` needs
  `st_value` bumped to the new `sh_addr`. We have `st_shndx` but
  don't currently track which shdr indices were relocated. Need a
  "relocation map" output from the layout pass.
- **PT_LOAD extension logic**: can we extend the last PT_LOAD or
  must we allocate a new one? Depends on `p_flags` match, alignment,
  and adjacency. Straightforward but easy to get wrong.
- **normalizeNoteSegments**: splits one phdr into N. Changes `phnum`.
  Our invariants (clause 2: `phdrs.size = phnum`) handle this, but
  each split is an `Array.insertIdx`-style op on `phdrs`.
- **Clause-7d for structured sections**: `.dynamic`, `.dynsym`,
  verneed, hash tables are NOT in scope for clause 7d today. After
  relocation, `e.bytes` at each relocated slot must match the
  encoded-form of the struct field. We'd need `<section>.write = raw
  bytes` lemmas per section type — this is the bigger preservation
  proof obligation.

### Neutral / new

- **A new `IsLayoutCoherent` invariant** (or clause 7e) that asserts
  phdrs and shdrs agree on which segments cover which sections. This
  is implicit in C++ via memory layout conventions; in Lean we'd
  either encode it structurally or prove it from the engine's
  output.

## 3. Minimum viable engine

Scope reduction strategy: do the **library path only**, skip the
noSort/sortShdrs feature, skip `clobberOldSections`, skip the PHT-
relocation optimization (always relocate PHT at end), skip
normalizeNoteSegments (assume 1 PT_NOTE per SHT_NOTE in input —
reject otherwise).

### Minimum input/output

Input: `ValidElfFile e` + `replacedSections : List (String × ByteArray)`
(name → new content).

Output: `ValidElfFile e'` with:
- `e'.bytes.size ≥ e.bytes.size + Σ newContent.size` (rounded up).
- Every named section's shdr updated: `sh_offset`, `sh_addr`,
  `sh_size`, `sh_addralign`.
- A new PT_LOAD phdr appended (or the last one extended) covering
  the new region.
- DT_STRTAB / DT_SYMTAB / DT_STRSZ / DT_HASH / DT_GNU_HASH updated to
  new addresses.
- Dynsym `st_value` updated for relocated sections.
- `e'.bytes` contains the new contents at the new offsets.

### Decomposition

Three free-standing functions, each with its own preservation theorem:

1. `reserveEndOfFileRegion (e : ElfFile) (neededSpace : Nat) : ElfFile × Nat`
   - Appends `neededSpace` zeros to `e.bytes`.
   - Adds or extends a PT_LOAD segment.
   - Returns the file offset where the new region starts.
   - Preserves `IsValid`; grows `e.bytes` but shdrs unchanged (no
     replaced section yet points here).

2. `writeReplacedSections (e : ElfFile) (startOff : Nat) (startAddr : UInt64)
                            (replacements : List (String × ByteArray))
                            : ElfFile × Nat`
   - Walks `replacements` in order.
   - For each (name, newBytes): splice newBytes into `e.bytes` at
     current cursor, update name's shdr (`sh_offset = cursor`,
     `sh_addr = startAddr + (cursor - startOff)`, `sh_size`,
     `sh_addralign`), sync partnering phdr (PT_INTERP / PT_DYNAMIC /
     PT_NOTE / PT_MIPS_ABIFLAGS / PT_GNU_PROPERTY).
   - Returns cursor after the last replacement.
   - Preserves `IsValid` + clause 7c (sh_sizes match).

3. `rewriteDynamicAddresses (e : ElfFile) (relocMap : Nat → Option UInt64)
                             : ElfFile`
   - For each DT_* entry whose tag is address-valued:
     look up the shdr it points at; if relocMap says "moved", update.
   - For each dynsym entry: if `st_shndx` is in the relocMap, update
     `st_value`.
   - Preserves `IsValid`.

Then `rewriteSectionsLibrary e replacements` is:

```
  e1, startOff := reserveEndOfFileRegion e neededSpace
  startAddr    := pickFreshVirtualPage e1
  e2, _        := writeReplacedSections e1 startOff startAddr replacements
  relocMap     := replacements.map (·.fst) → new sh_addr
  e3           := rewriteDynamicAddresses e2 relocMap
  return e3
```

Each step is independently verifiable; the composition plugs into
the existing `IsValid → IsEncodable → IsByteCoherent` tower.

### What we defer

- `noSort`/`sortShdrs` — just iterate `replacements` in insertion
  order. Breaks C++ compatibility on corner cases; revisit if an op
  needs it.
- `clobberOldSections` — skip. Old bytes remain in `e.bytes` but
  nothing references them. Cosmetic; revisit if compliance requires.
- PHT-at-file-start preservation — unconditionally move PHT to end.
  Slightly worse on old kernels (<2022-03-02 Linux); fine for modern
  targets.
- `normalizeNoteSegments` — for the prototype, require input ELFs
  to have 1 PT_NOTE per SHT_NOTE (reject via precondition otherwise).
- Executable path — ET_DYN only.
- Additional `Ok`-struct fits-in-UInt64 preconditions — bake into
  `IsValid` that `bytes.size + growth ≤ UInt64.size` as an op-level
  precondition.

## 4. Pre-engine simplification opportunities

Before landing the engine, simplify foundations so the engine's
preservation proofs don't inherit cruft.

### 4a. Hoist `ifDec` + `ifSome`

`ifDec` lives as a private combinator in `Ops/Interpreter.lean`;
`ifSome` existed briefly there before being inlined. The engine's
runtime builders will have multi-level decidable preconditions —
PHT placement, alignment checks, relocation-fit, DT_* presence.
Move `ifDec` to `Elf/PreservationTactics.lean` or a new
`Util/OptionCPS.lean` so engine builders can share.

### 4b. Parametrize `spliceOptSection` for growth

`Encoder.spliceOptSection bs shdrs shstrtab name opt encode` assumes
newBytes fits at the OLD shdr offset. The engine needs a variant that
splices at a CALLER-supplied offset (because the shdr will have been
updated by that point). Introduce `spliceSectionAt (bs : ByteArray)
(off : Nat) (newBytes : ByteArray) : ByteArray` — thin wrapper over
`Encoder.splice` — and use it in both the existing encoder and the
engine's `writeReplacedSections`.

### 4c. Introduce a `DynValue` sum type (OR stay untyped)

C++ has a weakly-typed `d_un.d_ptr`/`d_un.d_val`. The engine's
`rewriteHeaders` needs to know which DT_* carry addresses. Options:

- **Whitelist + Nat value**: `isAddressTag : DynTag → Bool` + keep
  `DynEntry.value : UInt64`. Simpler, matches C++. ✓ **Recommended.**
- **Sum type**: `DynValue | addr UInt64 | size UInt64 | offset UInt64
  | flags UInt64 | count UInt64 | raw UInt64`. More type-safe, but
  requires refactoring every op touching `.dynamic`.

Keep it untyped; add one `isAddressTag` predicate that the engine
consumes. Minimal disruption.

### 4d. Extract "update shdr" helpers

Every growing op does a two-step shdr update: `sh_size` via
`updateShdrSizeAt`, then the engine later overrides `sh_offset` and
`sh_addr`. We have the size helper; add:

- `updateShdrOffsetAt (shdrs : Array SectionHeader) (i : Nat) (newOff : UInt64)`
- `updateShdrAddrAt`
- `updateShdrSlotAt (shdrs) (i) (newOff) (newAddr) (newSize)` — the
  composed variant the engine actually uses.

Each gets `_size`, `_length`, `_getElem` lemmas; `updateShdrSlotAt`
gets a compound one.

### 4e. Separate "ops produce replacements" from "engine applies them"

Size-growing ops currently update `e.dynstr`, `e.dynamic` directly.
After the engine lands, this stays the same IF the engine re-reads
those fields at the end to compute replacements. Concretely, the
pipeline becomes:

```
  e' := growingOp e h   -- updates struct fields, NOT e.bytes
  replacements := [
    (".dynstr",  e'.dynstr.get  !.bytes),
    (".dynamic", writeArray DynEntry.write (e'.dynamic.get !)),
    ... etc.
  ]
  e'' := rewriteSectionsLibrary e' replacements
```

No code change to existing ops is required! They already produce a
valid ElfFile with stale `e.bytes`. The engine's job is exactly to
re-materialize `e.bytes` with the grown sections at new offsets.

### 4f. Clause-7c already does the heavy lifting

`shdrSizesCoherent` is stated as "for each broken-out section, the
shdr size matches the section's encoded byte size." After the
engine, this HOLDS — the engine updates each relocated shdr's
`sh_size` to `newBytes.size`. No extension to the invariant needed
for the library path.

### 4g. Alignment utilities

We have `Layout` constants but no `roundUp` or `isAligned`:

- `Nat.roundUp (n : Nat) (align : Nat) : Nat := (n + align - 1) / align * align`
- `Nat.isAligned (n : Nat) (align : Nat) : Prop := n % align = 0`

Plus a handful of `roundUp_ge`, `roundUp_mod_eq_zero`, `roundUp_le_add_align`
lemmas. 20-30 LOC; the engine uses these 10+ times.

## 5. Recommended implementation order

1. **Hoist `ifDec`** (5 LOC) — prerequisite for cleaner runtime builders.
2. **Alignment utilities** (30 LOC) — `Nat.roundUp` + 3 lemmas.
3. **`updateShdrSlotAt`** (15 LOC + 5 lemmas) — compound shdr update.
4. **`reserveEndOfFileRegion`** (40 LOC + 2 preservation theorems) —
   first engine piece, independently verifiable.
5. **`writeReplacedSections`** (80 LOC + 3 preservation theorems) —
   the cursor walk; preserves clauses 1-7c.
6. **`rewriteDynamicAddresses`** (60 LOC + 2 preservation theorems) —
   DT_* rewriting + dynsym `st_value` bumps.
7. **`rewriteSectionsLibrary`** (40 LOC of glue) — composition.
8. **CLI wire-up** for `--set-rpath`, `--add-needed`, `--set-soname`.
9. **Smoke test**: add/replace/remove rpath via the engine; verify
   re-parse + semantic queries.

Estimated total: ~350 LOC of implementation + ~15 preservation
theorems. Realistic delivery: 3-4 focused sessions.

## 6. Simplifications that pay off regardless

Even before the engine, these simplifications stand on their own:

- **Hoist `ifDec`** — cleaner `trySetInterpreterLockstepOk`.
- **`Nat.roundUp`** — used by alignment proofs elsewhere.
- **`updateShdrSlotAt`** — if I add `--set-rpath-in-slot` as an
  interim fast path (rpath fits in existing DT_RUNPATH string), it
  uses this.

## 7. Outstanding research questions

- **Does `startAddr` matter for library-path correctness?** C++
  computes `startPage = roundUp(max p_vaddr+p_memsz, align)`, but
  a pristine `ET_DYN` where the loader ignores absolute vaddrs
  might tolerate arbitrary fresh addresses. If so, we can pick a
  constant (e.g., `0x100_000_000` above the input's max) without
  scanning phdrs. Worth verifying with a glibc `ld.so` test.
- **Is the `binutilsQuirkPadding = 1` ELF-spec-compliant?** C++
  adds it to avoid a readelf warning. If we don't, does
  `objdump`/`ld` care? Probably fine to skip in v1.
- **Can we express clause 7d for structured sections?** Requires
  per-section `write = raw-bytes` lemmas. Orthogonal to the engine
  itself but blocks extending byte-coherence to `.dynamic`/`.dynsym`
  post-engine.
