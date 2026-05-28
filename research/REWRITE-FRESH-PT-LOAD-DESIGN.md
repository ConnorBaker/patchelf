# Fresh-PT_LOAD allocation design (ROADMAP §3.5a)

Forward-looking design for the only feature gap that blocks a real
binary class today: BSS-heavy ELFs (e.g. `coreutils ls`, ~0x97000
bytes of BSS) where `growEOFWith`'s "extend the last PT_LOAD"
strategy is unsafe, the engine falls back to `layoutForEncoding`'s
unaware repack, and the pre-write validator catches the resulting
non-loadable bytes (exit 5).

C++ patchelf handles this by allocating a brand-new PT_LOAD segment
in `rewriteSectionsLibrary` (`src/patchelf.cc:806–966`).  This
document is the porting plan for the equivalent Lean code path.

## What's wrong today

`Patchelf/Elf/GrowEOF.lean:482–489` decides between three branches:

```
if no PT_LOAD :  layoutForEncoding (unaware repack)
elif canExtendLastPtLoad : growEOFWithMainBody (extend last PT_LOAD)
else                     : layoutForEncoding (unaware repack)
```

The third branch is the BSS-heavy fallback.  `canExtendLastPtLoad`
(`GrowEOF.lean:430`) rejects when extending the last PT_LOAD's
`filesz`/`memsz` would clobber already-allocated BSS or fall
outside the existing alignment.  In that case we want a fourth
branch: **append a fresh PT_LOAD** that covers the moved sections.

## What changes

### Layer 1 — file-level layout (`GrowEOF.lean`)

New entry point `growEOFWithFreshPtLoad pageSize? e : ElfFile` that:

1. Identifies stale sections (same predicate as the existing main
   body — `sectionStale e i`).
2. Computes `startOffset = roundUp (currentFileEnd e) alignStartPage`
   and `startPage = roundUp (maxPtLoadVaddrEnd e.phdrs) alignStartPage`.
3. Appends each stale section at `(startOffset + relOff,
   startPage + relOff)` for the appropriate `relOff`.
4. **Grows `e.phdrs` by one** — appends a new `PT_LOAD` covering
   `[startOffset, startOffset + appendedBytes)` with `filesz =
   memsz = appendedBytes`, flags `PF_R | PF_W`, align
   `alignStartPage`.
5. **Updates `e.header.phnum`** to `e.phdrs.size`.
6. **Repacks the phdr table location** if the original phdr table
   no longer fits in its existing region (the table grew by 56 bytes
   for one new entry, which may push past the gap before the first
   section).  Two sub-cases:
    - **Phdr fits in place** (gap before first section is ≥ 56
      bytes more than the original phdr table size): keep
      `e.header.phoff` unchanged, the appended PT_LOAD just lives
      at the file end.
    - **Phdr table doesn't fit**: the C++ code calls this
      `relocatePht = true` (`patchelf.cc:848`).  Move the phdr
      table itself to the new region appended at file end, set
      `e.header.phoff` to the new location.  Note: this also
      requires the original location to be inside an existing
      PT_LOAD that covers the phdr (otherwise the loader can't
      reach the new phdrs — the kernel reads phdrs at boot using
      `e_phoff` directly).

The simpler sub-case (phdr fits in place) is the common path for
small binaries.  The harder sub-case (relocate phdr table) is the
one that matters for ELFs whose phdr-table neighborhood is densely
packed.

### Layer 2 — splice region tracking (`ElfFile.lean` + `Layout.lean`)

`spliceRegionsDisjoint` currently bounds 7 region kinds:
`hdr_phdr`, `hdr_shdr`, `phdr_shdr`, `hdr_sec`, `phdr_sec`,
`shdr_sec`, `sections_disjoint`.  No changes required — the new
PT_LOAD doesn't add a splice region to the encoder (sections are
already accounted for individually by `sections_disjoint`).  The
phdr table region is already tracked via `phoff + phnum *
phdrSize`, and `phdrs.size` increasing by 1 just changes the
upper bound.

What WILL break: if the phdr table moves (relocatePht case), the
`phdr_shdr_disjoint` and `phdr_sec_disjoint` clauses now reference
a different region.  The proof must be re-derived on the output —
specifically the `growEOFWithFreshPtLoad_produces_spliceRegionsDisjoint`
theorem.

### Layer 3 — proof (`growEOFWithFreshPtLoad_produces_spliceRegionsDisjoint`)

Proof structure mirrors `growEOFWithMainBody_produces_spliceRegionsDisjoint`
(GrowEOF.lean:934).  Key differences:

* `hOutPhdrsSize` becomes `e.phdrs.size + 1` rather than
  `e.phdrs.size`.
* `hdr_phdr_disjoint`: if phoff is unchanged (common case), the
  output phdr table extends from `phoff` to `phoff + (phnum + 1)
  * phdrSize`.  Need a new precondition that the original gap had
  room for one more phdr.
* If phoff IS relocated, the output phdr table is at
  `startOffset + relPhdrOff`; need to argue this is disjoint from
  the existing header / shdr / sections.

### Layer 4 — encoder pipeline (`Encoder.lean`)

`prepLayoutForEncodeWith pageSize? e` adds the fresh-PT_LOAD path:

```lean
if layoutAlreadyValid e then e
else match lastPtLoadIdx e.phdrs with
  | none => layoutForEncoding e
  | some lastIdx =>
    if canExtendLastPtLoad ... then growEOFWithMainBody pageSize? e lastIdx
    else if canAddFreshPtLoad ... then growEOFWithFreshPtLoad pageSize? e
    else layoutForEncoding e  -- fully unaware repack; validator will reject
```

`canAddFreshPtLoad` checks: there's room in the phdr-bearing region
for one more entry (or the binary admits phdr-table relocation).

### Layer 5 — validator (`Validate.lean`)

`IsLoadableBytes` already handles arbitrary phdr counts.  No
changes — the validator naturally accepts the extra PT_LOAD as
long as it's congruent with the section layout.

## Estimated work

| Layer | LOC | Effort |
|---|---|---|
| 1 (file-level layout) | ~200 | ~half day for the in-place sub-case; full day for relocatePht |
| 2 (splice region) | 0 | none |
| 3 (proof) | ~300 | day+ — mirrors `growEOFWithMainBody`'s proof complexity |
| 4 (encoder dispatch) | ~30 | half hour |
| 5 (validator) | 0 | none |

**Total: ~530 LOC, ~3 days** for the in-place sub-case (matches the
ROADMAP's ~600 LOC estimate).  The relocatePht sub-case adds
another ~150 LOC and a day.

## Pickup checklist

1. Add `canAddFreshPtLoad e startOffset alignStartPage` decidable
   predicate.
2. Add `growEOFWithFreshPtLoad pageSize? e` for the in-place
   sub-case.
3. Add `growEOFWithFreshPtLoad_produces_spliceRegionsDisjoint`
   following the `growEOFWithMainBody` proof template.
4. Wire into `prepLayoutForEncodeWith` and
   `prepLayoutForEncodeWith_produces_spliceRegionsDisjoint`.
5. Add a shell test: `coreutils ls` set-rpath should round-trip
   without exit 5.
6. (follow-up) relocatePht sub-case for phdr-table-pressure cases.

## Test fixtures

The test fixture `/tmp/lean-pe-fixtures/ls` (a copy of `coreutils
ls`) is the canonical BSS-heavy binary.  Currently `set-rpath`
exits 5; after the fresh-PT_LOAD path lands, it should produce a
binary that runs.

## Why this isn't shipping now

This is a multi-day project gated on §1.2's `growEOFWith_preserves_loadable`
(ROADMAP §1.2) and §1.1 (parser → IsLoadable).  Doing it before
those means the proof has to bridge across an unfamiliar invariant
chain.  Post-§1.1 the work is straightforward extension of the
existing layout engine.
