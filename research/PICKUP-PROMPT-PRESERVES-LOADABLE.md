# Pickup prompt: ROADMAP §1.2 `growEOFWith_preserves_loadable`

Single-shot agent prompt for closing the `_preserves_loadable`
ladder in the patchelf Lean 4 port (ROADMAP §1.2 follow-up).
Paste the fenced block below into a fresh agent that has shell
access, build environment, and read access to the repo, but no
other context.

The §1.2 `_preserves_valid` ladder is fully closed.
`layoutForEncoding_preserves_loadable` shipped last session
(covers the no-PT_LOAD branch of `growEOFWith`'s dispatch).  The
three growEOFWith branches plus the top-level dispatch theorem
remain.  This prompt is the handoff for closing them.

---

```
You are picking up ROADMAP §1.2 in the patchelf Lean 4 port:
proving `growEOFWith_preserves_loadable` and its three named-body
predecessors.  The byte-layer `_preserves_valid` ladder is already
complete; this is the deeper claim that the encoder pipeline preserves
loader-coherence (`IsLoadable = IsValid + sectionsNonOverlapping +
ptInterpAgreement + ptDynamicAgreement + segmentCongruence`).  Today
only `layoutForEncoding_preserves_loadable` ships; the three
growEOFWith branches and the top-level dispatch are open.

## First reads, in this order

1. `/home/cbaker2/ext-sources/patchelf/lean/STATUS.md` — current
   state (top banner, "What works end-to-end").
2. `/home/cbaker2/ext-sources/patchelf/research/ROADMAP.md` —
   "Picking up work" + §1.2 in detail.
3. `/home/cbaker2/ext-sources/patchelf/lean/Patchelf/Elf/LayoutEngine.lean`
   — the existing `layoutForEncoding_preserves_loadable` is your
   structural template (search for `_preserves_loadable`).  Mirror
   its shape for the three growEOFWith branches.
4. `/home/cbaker2/ext-sources/patchelf/lean/Patchelf/Elf/GrowEOF.lean`
   — read `updatePhdrsAfterMove` (around line 533) carefully.
   It's the function the new per-phdr facts need to characterize.

## Working directory and environment

    cd /home/cbaker2/ext-sources/patchelf/lean
    nix develop ..#lean -c lake build              # baseline must be clean
    nix develop ..#lean -c bash tests/run.sh       # 54/54 shell tests
    grep -rn "sorry\b" Patchelf/                   # zero matches; keep it

`lake build` from cold is a few minutes — set a generous timeout.

## What's already in place

`Patchelf/Elf/LayoutEngine.lean`:

* `Section.withOffset_*` per-field rfl simp lemmas (all 8: `name`,
  `flags`, `link`, `info`, `addralign`, `entsize`, `content`, `type`).
* `relocatePhdr_*` per-phdr facts: `_type`, `_align`, `_vaddr`
  (preserved always); `_of_not_interp_dynamic` (identity for
  PT_LOAD and other non-retargeted types); `_pt_interp` /
  `_pt_dynamic` (output offset = section offset for the two
  retargeted types).
* `layoutForEncoding_*` accessor preservations (size, header
  fields, dynamic/dynsym/dynstr/shstrtab/findIdxByName/etc.).
* `layoutForEncoding_phdrs_getElem` bridge lemma:
  output's i-th phdr = `relocatePhdr ... (input.phdrs[i])`.
* `layoutForEncoding_preserves_loadable` (the goal to mirror).

`Patchelf/Elf/GrowEOF.lean`:

* `growEOFWithMainBody_*` accessor preservations (sections size,
  header fields, dynamic/etc.).  Same shape for `growEOFWithFreshPtLoad_*`
  and `growEOFWithFreshPtLoadReloc_*`.
* `growEOFWith_preserves_valid` top-level dispatch (your template).

## What you need to add

### Layer 1: `updatePhdrsAfterMove` per-phdr facts (~150 LOC)

Three lemmas mirroring `relocatePhdr_pt_interp` /
`relocatePhdr_pt_dynamic` / `relocatePhdr_of_not_interp_dynamic`:

```lean
theorem updatePhdrsAfterMove_pt_load_offset_vaddr_align
    (phdrs lastIdx? newLastFilesz newLastMemsz interpIdx? dynamicIdx? newSections)
    (i : Nat)
    (hi : i < (updatePhdrsAfterMove ...).size)
    (hiE : i < phdrs.size)
    (hPhT : (phdrs[i]'hiE).type = PhType.PT_LOAD) :
    let outPh := (updatePhdrsAfterMove ...)[i]'hi
    outPh.type = (phdrs[i]'hiE).type ∧
    outPh.offset = (phdrs[i]'hiE).offset ∧
    outPh.vaddr = (phdrs[i]'hiE).vaddr ∧
    outPh.align = (phdrs[i]'hiE).align

theorem updatePhdrsAfterMove_pt_interp ...  -- offset = newSections[interpIdx].offset
theorem updatePhdrsAfterMove_pt_dynamic ... -- offset = newSections[dynamicIdx].offset
```

The proofs are 4-level case-bash:
* `cases lastIdx? with | none => ... | some lastIdx`
* `by_cases hLI : i = lastIdx`
* The `i = lastIdx` branch's `phLast = { ph with filesz, memsz }` —
  use `have hPhLastType : phLast.type = ph.type := rfl` to thread
  the type identity through.
* `by_cases hT1 : phLast.type = PT_INTERP` and similar for PT_DYNAMIC.
* Inner `match interpIdx?`/`dynamicIdx?` + `dif_pos`/`dif_neg`.

**Tactic gotcha**: `rw [if_neg hT, ...]` chains under nested
matches don't always normalize as expected.  Use
`simp only [..., ↓reduceDIte]` for the `dif_pos h` / `dif_neg h`
forms; use explicit `rw [if_pos h]` for the if/else; combine
sparingly.

The previous attempt at these lemmas used a long `<;> first | rfl
| ...` chain that fell over.  The structurally cleanest move is to
mirror `relocatePhdr_pt_interp`'s pattern (line ~1280 in
LayoutEngine.lean): `unfold updatePhdrsAfterMove; rw [Array.getElem_mapIdx]`
then case-bash with `rfl` at each leaf.

If three days of effort don't crack the case-bash, the alternate
strategy is to **refactor `updatePhdrsAfterMove`** into a flat
two-pass shape:

```lean
def updatePhdrsAfterMove := mapIdx phdrs (fun i ph => ...)
                          |>.map (retargetInterpDynamic ...)
```

This loses the test 53/54 / `_produces_spliceRegionsDisjoint`
proof (which you'd then need to re-do).  Don't take this path
unless the case-bash is truly unworkable.

### Layer 2: three `growEOFWith*_preserves_loadable` theorems (~150 LOC each)

Mirror `layoutForEncoding_preserves_loadable`.  For each of the
three named bodies (`growEOFWithMainBody`, `growEOFWithFreshPtLoad`,
`growEOFWithFreshPtLoadReloc`), the four IsLoadable clauses
dispatch:

* `sections_nonoverlapping`: from the matching
  `_produces_spliceRegionsDisjoint.sections_disjoint`.
* `ptInterpAgreement`: `interpIdx` preserved (already proven) →
  output's PT_INTERP phdrs retargeted via `updatePhdrsAfterMove_pt_interp`.
* `ptDynamicAgreement`: parallel.
* `segmentCongruence`: PT_LOADs unchanged in offset/vaddr/align via
  `updatePhdrsAfterMove_pt_load_offset_vaddr_align`.  For
  `growEOFWithFreshPtLoad` / `growEOFWithFreshPtLoadReloc`, ALSO
  need to discharge the FRESHLY-APPENDED PT_LOAD's congruence:
  fresh PT_LOAD has `offset = startOffset = roundUp ... align`,
  `vaddr = startPage = roundUp ... align`, both 0 mod align —
  trivially congruent.

For `growEOFWithFreshPtLoadReloc`, additionally: PT_PHDR is
retargeted via `retargetPtPhdr`.  PT_PHDR isn't PT_LOAD so doesn't
enter `segmentCongruence`.  Add a `retargetPtPhdr_*` lemma family
similar to `relocatePhdr_*`.

### Layer 3: top-level `growEOFWith_preserves_loadable` (~80 LOC)

Mirror `growEOFWith_preserves_valid` exactly: 5-way dispatch via
`layoutAlreadyValid` / `lastPtLoadIdx` / `canExtendLastPtLoad` /
`canAddFreshPtLoad`.

The fresh-PT_LOAD branches will need the same
`(e.phdrs.size + 1) < UInt16.size` precondition the
`_preserves_valid` version uses.

## Hard constraints

- Don't refactor unrelated code.  This is additive proof work.
- Don't add `sorry`s, even temporarily.  If a proof obstacle blocks
  you, stop and write up what you tried.  See "If you get stuck".
- Don't change `updatePhdrsAfterMove`'s shape unless the case-bash
  is genuinely unworkable.  Refactoring it cascades through the
  existing `_produces_spliceRegionsDisjoint` proofs.
- Don't break any existing test or theorem.  All 54 shell tests
  must still pass; all 108 lake jobs must still build clean.

## Success criteria

1. `lake build` clean, zero `sorry`s.
2. All 54 existing shell tests pass; do not weaken any of them.
3. The three `growEOFWith*_preserves_loadable` theorems shipped
   (`Patchelf/Elf/GrowEOF.lean`).
4. Top-level `growEOFWith_preserves_loadable` shipped, composing
   the four branches via `growEOFWith`'s dispatch.  Same shape as
   `growEOFWith_preserves_valid`.
5. STATUS.md and ROADMAP.md updated to reflect §1.2's
   `_preserves_loadable` ladder closing.

## If you get stuck

- Document the obstacle inline as `-- TODO §1.2-loadable: <what you
  tried, what failed>` and stop.
- Save partial progress in a commit (don't push unless asked).
- Hand back a status summary: which layers landed, where you hit
  the obstacle, what you'd try next.

## Patterns from the previous session

- The prior pickup attempted `updatePhdrsAfterMove_type` as a
  full-coverage helper and ran into ~100 LOC of case-bash that
  trips over `rw [if_neg ...]` pattern matching.  The fix is
  almost certainly to (a) factor narrower lemmas (e.g.,
  PT_LOAD-specific, not generic), (b) use `simp only [hLI,
  ↓reduceIte]` instead of `rw` for if-then-else reductions, and
  (c) mirror the structurally simpler `relocatePhdr_pt_interp`
  proof shape — `unfold; rw [getElem_mapIdx]; cases lastIdx?;
  by_cases` — without trying to do everything in one giant
  `<;> first | ...`.

- For `growEOFWithFreshPtLoad` and `growEOFWithFreshPtLoadReloc`,
  the fresh PT_LOAD's congruence is the new sub-clause.  Critical
  fact: `freshPtLoad startOffset startPage appendedBytes
  alignStartPage` has `offset.val = startOffset`, `vaddr.val =
  startPage`, `align.val = alignStartPage`.  Both `startOffset`
  and `startPage` are `roundUp ... alignStartPage`.  Lemma you
  may need: `roundUp_mod : roundUp n k % k = 0` (probably
  available as `Nat.roundUp_mod` or similar).

## Output

Commits in the existing style (see `git log --oneline -10`).
Small focused commits — ideally one per phase (per-phdr lemmas,
each named-body theorem, top-level dispatch).  Each commit
message names what landed, which file paths changed.

At the end, update STATUS.md, ROADMAP.md, and remove this pickup
prompt (or replace it with a note pointing at the next open work).
```

---

## Notes for the human (not the agent)

The previous session got `layoutForEncoding_preserves_loadable`
landed cleanly but bounced off `updatePhdrsAfterMove`'s case-bash
when trying to land per-phdr helpers.  The function has 4 nesting
levels (mapIdx → match lastIdx? → if i=lastIdx → if phLast.type =
PT_INTERP/PT_DYNAMIC).  The `relocatePhdr` template in place
covers the simpler 2-level case; the `updatePhdrsAfterMove`
template needs to handle the lastIdx pre-update.

If the agent reports back stuck on the case-bash, the right
intervention is one of:

1. **Take the refactor.** Split `updatePhdrsAfterMove` into two
   passes — first do the lastIdx filesz/memsz update (mapIdx with
   only that effect), then map `relocatePhdr`-style for the
   PT_INTERP/PT_DYNAMIC retargeting.  This makes the helper
   lemmas trivial but breaks the existing
   `_produces_spliceRegionsDisjoint` proofs (which would need to
   compose through the two passes instead of one).  Net cost:
   ~200 LOC redo across the four `_produces_spliceRegionsDisjoint`
   theorems.  Probably worth it.

2. **Inline the case-bash inside each `_preserves_loadable`
   proof body** rather than factoring per-phdr helpers.  Three
   ~150 LOC proofs of repetitive case-bash, no abstraction
   payoff.  Faster to write, harder to read.

3. **Use mvcgen / grind-style automation.**  Lean 4.21+ has
   `grind` which sometimes navigates nested ifs cleanly.  Worth
   trying as a first move on the helper lemmas before falling
   back to manual case-bash.
