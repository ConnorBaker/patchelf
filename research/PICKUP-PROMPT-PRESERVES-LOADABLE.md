# Pickup prompt: ROADMAP §1.2 `growEOFWith_preserves_loadable` — CLOSED

**This work is complete.**  The `_preserves_loadable` ladder for the
encoder's primary layout pass shipped in five commits (search
`git log --oneline --grep "loadable L"`):

- **L1** `updatePhdrsAfterMove` per-phdr facts
  (`_pt_load_offset_vaddr_align`, `_pt_interp`, `_pt_dynamic`,
  `_type`, `_size`).
- **L2a** `growEOFWithMainBody_preserves_loadable`.
- **L2b** `growEOFWithFreshPtLoad_preserves_loadable` (+ shared
  helpers `roundUp_mod_self`, `array_getElem_at_base_size`,
  `freshPtLoad_roundUp_congruence`).
- **L2c** `growEOFWithFreshPtLoadReloc_preserves_loadable` (+
  `retargetPtPhdr_*` / composed `retarget_update_*`).
- **L3** top-level `growEOFWith_preserves_loadable`.

All in `lean/Patchelf/Elf/GrowEOF.lean`.  `#print axioms
growEOFWith_preserves_loadable` → `[propext, Classical.choice,
Quot.sound]` (no `sorryAx`).  108 lake jobs build; 54 shell tests
pass.

## The tactic that unblocked the previous stuck attempt

`updatePhdrsAfterMove` has 4 nesting levels (mapIdx → match
`lastIdx?` → `if i = lastIdx` → PT_INTERP/PT_DYNAMIC type tests).
The previous session bounced off `rw [if_neg …]` pattern-matching
under the nested `dif`.  The fix: **`subst` the `i = lastIdx` and
`interpIdx?`/`dynamicIdx?` equation witnesses rather than `rw`-ing
them.**  `subst` eliminates the variable (`lastIdx := i`, or
`interpIdx? := some iS`) so the input phdr/index survives and the
dependent motive stays well-typed; `rw` on the same equation trips
the motive checker.  Type-test reduction then closes each leaf with
`simp only [↓reduceDIte]` / `if_pos` / `if_neg` (the `relocatePhdr`
template's idiom).

One context gotcha: the top-level dispatch's
`simp only [hExt, Bool.not_true, …, ↓reduceIte]` reduction (cloned
from `growEOFWith_preserves_valid`) fires in `GrowEOF.lean` but NOT
when the same theorem is elaborated in a standalone scratch file
importing the olean.  Develop branch lemmas in scratch for the fast
loop, but transplant the top-level dispatch into the file before
expecting the `if`-cascade `simp` to reduce.

## Next open work

The remaining loader-coherence gap is **per-op**, not layout-pass:
see ROADMAP §5.1 (op-level Tier D / per-op `_preserves_loadable`).
The §1.2 `updatePhdrsAfterMove_*` / `retargetPtPhdr_*` lemma
families are reusable for any op whose post-encode routes through
`growEOFWith`.
