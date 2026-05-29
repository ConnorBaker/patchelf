# Plan: refactor OpToElfFactor.lean — generic over `mapDynamicOp`

Every load-bearing claim below was **verified by compiling it in scratch** against
the current tree (commit 15aebb2), not by grep or speculation. Scratch proofs are
cited as "✓ compiled". Baseline: 110 lake jobs, 54/54 tests, 0 sorry.

---

## 0. Verified ground truth (read the source)

The four shrinking ops are all `mapDynamicOp e f` (read the op files):

| Op | `f` | source |
|---|---|---|
| `removeRpath` | `(·.stripRpath)` | RemoveRPath.lean:17 |
| `modifyRPath .remove` | `(·.stripRpath)` — **identical f** | Rpath.lean:25 |
| `removeNeeded lib` | `(·.filterNeededBy lib.toUTF8)` | RemoveNeeded.lean:20 |
| `modifySoname .remove` | `(·.removeSoname)` | Soname.lean:30 |

`mapDynamicOp e f = { e with dynamic := e.dynamic.map f }` (ObservableCombinators.lean:104):
changes ONLY `.dynamic`; `mapDynamicOp_fields` (9 other fields `rfl`, `.dynamic = map f`) ✓ compiled.

### What is `f`-agnostic (factoring + transport machinery) — all ✓ compiled
- `applyDynamic_factor_general` : `applyDynamic e₀ (some td') = (applyDynamic e₀ (some td)).update iDyn (.dynamic (patch bd td'))` for ANY `td' td`. Pure `set_set`.
- `toElfFile_mapDynamicOp_factor` : the FULL master factoring over arbitrary `f` — ✓ compiled end-to-end (the keystone). Sections bullet closes via `rw [hTd]; simp only [Option.map_some]; rw [innerChain_factor_general …]`; header/phdrs bullets need a trailing `rfl`.
- `applyTypeOpt_{dynamic_comm, dynamicIdx, content_at, sections_size}` : the 4 type-based outer applies (versym/sysv/gnu/verneed) collapse to ONE generic lemma each, keyed on `ty ≠ SHT_DYNAMIC`. ✓ all 4 compiled.
- `outerChain_dynamic_comm`'s 4 index hyps reduce to `hIdx0` alone. ✓ compiled (`outerChain_slim`).

### What is GENUINELY per-`f` (size bound) — corrected from the original review
`SectionOps.*Disjoint_shrink` consume `(patch bd (f td)).size ≤ (patch bd td).size`.
Each `f` shrinks a DIFFERENT field, so the relation differs:
- `stripRpath`: clears rpath/runpath → shrink is in the two rpath/runpath TAIL `unless`-blocks. Current `ShrinkRel` (cursor EQUAL) + `tail_shrink_rpath`. ALREADY LANDED (`patchDynamicEntries_stripRpath_size_le`, Adapter.lean).
- `filterNeededBy`: filters `needed` → shrink is in the LOOP `.needed` arm. Needs a **potential-function relation** `result.size + (needed.size − cursor)`, NOT `ShrinkRel` (cursors are unequal). `patchStep_filterNeeded` with this relation ✓ compiled (the crux `.needed` arm closes by `omega` after the 4-way cursor split).
- `removeSoname`: clears soname → shrink in the soname tail block; a third `ShrinkRel`-like relation.

So the size bound stays per-op; only `modifyRPath.remove` shares one verbatim (same `f`).

### Dead / redundant (read the file)
- `RemoveRpathFactorData.hb0` (line 765): declared, **never referenced** anywhere. Dead.
- `outerChain_dynamic_comm` index hyps `hIdxS/G/N` (lines 349–351): derivable.
- Bundle chain-fields `hbN`/`hContentN`/`hDsN`: derivable from e₀-level facts (`hbN` from `hb0` by `simpa` ✓; `hContentN` is `toElfFile_content_at_dynamicIdx` minus one peel). Optional shrink.

### Structural (read the file): 24 `namespace Patchelf.Elf{,.Adapter}` blocks + 43 `open` lines for 49 decls. Pure scratch-append artifact.

---

## 1. Commit plan (5 commits, each build+test green before the next)

### Commit 1 — structural cleanup (no proof changes)
**Changes:**
- Collapse 24 namespace blocks → 2 sections: one `namespace Patchelf.Elf … end`,
  one `namespace Patchelf.Elf.Adapter … end`. The `Patchelf.Elf`-namespace decls
  (`updateSectionContent_comm`, `getElem_content_congr{,_sections}`,
  `updateSectionContent_content_self`, `_set_set`, `_sections_eq_of_sections`,
  `with_header_phdrs_updateSectionContent`, `type_at_dynamicIdx`,
  `updateSectionContent_dynamic_findUniqueTypeIdx`, `findUniqueTypeIdx_ne_dynamicIdx`,
  `updateSectionContent_findUniqueTypeIdx_both_ne`) go in block 1; everything in
  `Adapter` in block 2. One `open Patchelf.Elf (…)` + `open …Layout (ShType)` per block.
  CAVEAT (verified): `applyOpt_dynamicIdx` and `updateSectionContent_findUniqueTypeIdx_both_ne`
  are declared inside `namespace Adapter` but the latter is an `ElfFile.` lemma — Lean
  accepts `ElfFile.foo` decls inside `Adapter` (full name resolves), so moving them is safe
  but verify no name now needs requalifying.
- Delete `RemoveRpathFactorData.hb0` + its now-unused position (line 765).
- `outerChain_dynamic_comm`: drop params `hIdxS hIdxG hIdxN`, derive inside:
  ```
  (by rw [applySysvHash_dynamicIdx, applyVersym_dynamicIdx]; exact hIdxV)  -- etc.
  ```
  Update its 1 call site in `innerChain_removeRpath_factor` (lines 542–548) to drop those 3 args.
**Risk:** low. **Verify:** `lake build` (110 jobs), 54/54 tests, `#print axioms` on the capstone unchanged.

### Commit 2 — collapse the type-based outer-apply duplication
**Changes:** add the 4 generic lemmas (all ✓ compiled):
```lean
theorem applyTypeOpt_dynamic_comm {α} (e iDyn d) (ty) (hTyNe : ty ≠ SHT_DYNAMIC) (val? mk) (hIdx) :
  applyOpt (e.update iDyn (.dynamic d)) ((e.update …).findUniqueTypeIdx ty) val? mk
    = (applyOpt e (e.findUniqueTypeIdx ty) val? mk).update iDyn (.dynamic d)
  := applyOpt_updateSectionContent_dynamic_comm … (updateSectionContent_dynamic_findUniqueTypeIdx …) (fun i hi => findUniqueTypeIdx_ne_dynamicIdx … hTyNe …)
theorem applyTypeOpt_dynamicIdx … := applyOpt_dynamicIdx … (intro …; rw [hTy]; exact hTyNe)
theorem applyTypeOpt_content_at … := applyOpt_content_at_ne … (fun i hi => findUniqueTypeIdx_ne_dynamicIdx … hTyNe …)
theorem applyTypeOpt_sections_size … := by simp
```
Then **rewrite** the 16 `apply{Versym,SysvHash,GnuHash,Verneed}_*` as thin wrappers:
```lean
theorem applyVersym_dynamic_comm e iDyn d hIdx vs? : … := by
  unfold applyVersym ElfFile.versymIdx; exact applyTypeOpt_dynamic_comm e iDyn d _ (by decide) vs? _ hIdx
```
(Keep the wrapper NAMES — `outerChain`/`content_at`/`toElfFile_content_at_dynamicIdx`
call them by name, so wrappers avoid touching those call sites.)
`applyInterp_*` and `applyDynamic_*` stay as-is (interp = findIdxByName, not type-based).
**Risk:** medium (16 lemma bodies change; signatures stay). **Verify:** build + tests + axioms.

### Commit 3 — genericize the factoring + transport over `f`
**Changes:**
- Add `applyDynamic_factor_general` + `innerChain_factor_general` (✓ compiled).
- Add `toElfFile_mapDynamicOp_factor` (the master, ✓ compiled).
- Rename `RemoveRpathFactorData` → `MapDynamicOpFactorData` (drop `hb0`; otherwise
  identical — it is already `f`-agnostic except it hardcodes `(some td)` for the
  no-op, which is correct for any op). Add `f` + `td' := f td` is NOT needed; the
  bundle is about the no-op chain, so `f` enters only at the transport.
- Add `mapDynamicOp_structural_transport` generic over `f`, taking
  `hSizeBound : (patch bd (f td)).size ≤ (patch bd td).size` as a hypothesis.
  Body is `removeRpath_structural_transport` verbatim with `td.stripRpath → f td`
  and `patchDynamicEntries_stripRpath_size_le D.bd D.td → hSizeBound`.
- Add generic capstone `toElfFile_mapDynamicOp_tierD_roundtrip_derived` (the §E body
  with `removeRpath → mapDynamicOp f`, `hSizeBound` threaded in).
**Risk:** medium-high (keystone). **Verify:** the existing `removeRpath` capstone re-derives
as an instantiation (Commit 4) — that IS the regression test. Build + tests + axioms.

### Commit 4 — re-land removeRpath + add modifyRPath.remove as instantiations
**Changes:**
- `toElfFile_removeRpath_tierD_roundtrip_derived` becomes:
  ```lean
  toElfFile_mapDynamicOp_tierD_roundtrip_derived template typed (·.stripRpath) … (patchDynamicEntries_stripRpath_size_le …) …
  ```
  Statement UNCHANGED (so downstream / docs / axiom check are stable).
- Add `toElfFile_modifyRPath_remove_tierD_roundtrip_derived` reusing the SAME
  `patchDynamicEntries_stripRpath_size_le` (identical `f`). Near-free second op.
**Risk:** low. **Verify:** build + tests; `#print axioms` on removeRpath capstone == previous.

### Commit 5 — removeNeeded (proves the generalization paid off)
**Changes:**
- New size bound in Adapter.lean: `patchDynamicEntries_filterNeededBy_size_le`
  `(patch bd (d.filterNeededBy t)).size ≤ (patch bd d).size`, via the potential
  relation `NeededRel` + `patchStep_filterNeeded` (✓ crux compiled) + a tail bound
  (surplus realizes the remaining potential; cursor-end case analysis). See §2 sketch.
- Instantiate the generic capstone for `removeNeeded`.
**Risk:** medium (new size bound — the `NeededRel` tail composition is the only un-compiled
piece; the step lemma is ✓). **Verify:** build + tests + axioms.

---

## 2. Fleshed-out sketch — the `filterNeededBy` size bound (Commit 5, the one real unknown)

`patchStep_filterNeeded` (step lemma, **✓ compiled in scratch**):
```lean
abbrev NeededRel (n2 n1 : Nat) (st2 st1 : PatchState ds) : Prop :=
  st2.result.size + (n2 - st2.typedNeededIdx) ≤ st1.result.size + (n1 - st1.typedNeededIdx) ∧
  st2.typedNeededIdx ≤ n2 ∧ st1.typedNeededIdx ≤ n1 ∧
  st2.flags1Applied = st1.flags1Applied ∧ st2.debugApplied = st1.debugApplied ∧
  st2.rpathApplied = st1.rpathApplied ∧ st2.runpathApplied = st1.runpathApplied ∧
  st2.sonameApplied = st1.sonameApplied
-- proof: cases d.tag; .needed arm: by_cases on each cursor<size (4-way) then omega; rest trivial.
```
Loop: `Array.foldl_rel NeededRel … byteDyn` with init `⟨by omega (0+(n2-0) ≤ 0+(n1-0) since n2≤n1), …⟩`
— needs `n2 ≤ n1` i.e. `(d.filterNeededBy t).needed.size ≤ d.needed.size` = `Array.size_filter_le` (already used in RemoveNeeded.lean:45).

Tail: at loop end, state `st2 st1` satisfy `NeededRel n2 n1`. The full `patchDynamicEntries`
tail = `appendSurplusNeeded … (push remaining needed) + 5 unless + null push`.
- `appendSurplusNeeded typed r cursor` pushes exactly `(typed.needed.size − cursor)` entries
  (each `i = cursor+k < size` fires) → its output size = `r.size + (needed.size − cursor)`.
  Need `appendSurplusNeeded_size_exact` (currently only `_mono` exists). Sketch:
  `(List.range (n−cursor)).foldl (push if i<n)` — since `cursor+k < n` for all `k < n−cursor`,
  every step pushes → size = base + (n − cursor). Prove by `List.foldl` length induction.
- The 5 `unless` blocks: for filterNeededBy, rpath/runpath/soname/flags1/debug are UNCHANGED
  between st2 and st1 (NeededRel tracks all 5 applied-flags equal), and the typed values are
  equal (filterNeededBy changes only `needed`), so each `unless` adds the SAME amount to both →
  use `appendUnless_size_mono` (exists) with the running ≤.
- Combine: `st2.result.size + (n2 − cur2)` (the surplus-exact bound) ≤ `st1.result.size + (n1 − cur1)`
  (= the NeededRel potential) → after equal unless-blocks + equal null push, op output ≤ no-op output.

The ONLY new helper vs. the stripRpath case is `appendSurplusNeeded_size_exact`; everything
else reuses `appendUnless_size_{mono,le,ge,none}` + `Array.foldl_rel`. Estimated ~80 LOC.

---

## 3. Net effect (measured against the file)
- Commit 1: −~22 namespace/open noise lines, −1 dead field, −3 redundant hyps.
- Commit 2: 16 lemmas (~12 lines each ≈ 190 LOC) → 4 generic (~7 lines) + 16 one-line
  wrappers ≈ net −80 LOC AND removes the 4× duplication.
- Commit 3: factoring/transport/capstone genericized (~same LOC, but now reusable).
- Commit 4: removeRpath capstone shrinks to ~3 lines; +modifyRPath.remove ~5 lines.
- Commit 5: removeNeeded ~80 LOC (size bound) + ~5 (instantiation), vs. ~900 if cloned.

Behaviour-preserving: the `removeRpath` capstone STATEMENT is unchanged across commits 1–4,
so 54 shell tests + the axiom check are the standing regression gate. Each commit builds green.

## 4. Decisions still open for the human
- Commit 5 (removeNeeded) — do it now, or stop after Commit 4 (generalization landed,
  removeNeeded deferred to next session)? Commit 5 is the only one with a non-compiled piece
  (the surplus-exact tail), though the crux step lemma is ✓.
- Bundle shrink to e₀-level fields (Q2) — worth it, or leave the chain-shaped bundle?
  Recommend: leave it (works; shrinking is cosmetic and adds derivation lemmas).

---

# EXECUTION PROMPT (self-contained — paste into a fresh agent)

You are refactoring `Patchelf/Elf/OpToElfFactor.lean` in the patchelf Lean 4 port to
make its `removeRpath`-specific machinery generic over `mapDynamicOp f`, then add
`modifyRPath.remove` and `removeNeeded` as instantiations.  All the new proofs below
were already COMPILED against the current tree; transcribe them, don't re-derive.

## Environment
    cd /home/cbaker2/ext-sources/patchelf/lean
    nix develop ..#lean -c lake build                 # baseline: 110 jobs clean
    nix develop ..#lean -c bash tests/run.sh          # 54/54
    grep -rnE "(:= *sorry|by *sorry| sorry$)" Patchelf/   # must stay zero
Develop in `Patchelf/Scratch.lean` (`module` + `public import Patchelf.Elf.OpToElfFactor`
+ `@[expose] public section`); DELETE it before committing (gitignored).
Axiom check: temporarily point `AxiomCheck.lean` at a theorem, `lake env lean AxiomCheck.lean`,
restore it.  Headline theorems must show only `[propext, Classical.choice, Quot.sound]` +
3 `bv_decide` axioms — no `sorryAx`.

## Hard constraints
- No `sorry`, ever (even transiently in a commit).
- Don't change the STATEMENT of `toElfFile_removeRpath_tierD_roundtrip_derived` or
  `removeRpath_structural_transport` — they are the regression gate. After Commit 4 they
  must still typecheck verbatim and `#print axioms` must be unchanged.
- 110+ lake jobs, 54/54 tests after every commit. Commit style: `git log --oneline -5`;
  end messages with the repo's Co-Authored-By line. Branch is `vibe-coding/pure-ir-migration`
  (not master); commit there.
- Lean 4.29, NO Mathlib: `set` tactic and `Array.getElem_congr_coll`/`getElem_of_eq` do
  NOT exist. For "array eq → getElem eq": `cases a; cases b; subst; rfl`.

## Commit 1 — structural cleanup (no proof-content change)
1. Collapse the ~24 `namespace`/`open` blocks into two: one `namespace Patchelf.Elf … end`
   (the `ElfFile.*` lemmas: `updateSectionContent_comm`, `getElem_content_congr{,_sections}`,
   `updateSectionContent_content_self`, `_set_set`, `_sections_eq_of_sections`,
   `with_header_phdrs_updateSectionContent`, `type_at_dynamicIdx`,
   `updateSectionContent_dynamic_findUniqueTypeIdx`, `findUniqueTypeIdx_ne_dynamicIdx`,
   `updateSectionContent_findUniqueTypeIdx_both_ne`), then one
   `namespace Patchelf.Elf.Adapter … end` (everything else). One `open Patchelf.Elf (…)`
   + `open Patchelf.Elf.Layout (ShType)` per block. NOTE: `applyOpt_dynamicIdx` /
   `updateSectionContent_findUniqueTypeIdx_both_ne` are `ElfFile.`/plain names currently
   inside `Adapter` — keep them building (Lean resolves full names; just ensure the `open`s
   cover `ElfFile`, `applyOpt`, etc.). Build after this sub-step alone before continuing.
2. Delete the `hb0` field from `RemoveRpathFactorData` (declared, referenced nowhere — grep
   `\.hb0` and `hb0 :` to confirm zero uses, then remove the field).
3. Slim `outerChain_dynamic_comm`: drop the three params `hIdxS hIdxG hIdxN`; derive them
   inside from `hIdxV` (rename to `hIdx0`) — the body already shows the pattern. Then its
   ONE caller `innerChain_removeRpath_factor` drops those three `(by rw […]; exact hIdxBase)`
   arguments (the remaining `hIdxBase` covers it). Build + tests.

## Commit 2 — collapse the 4× type-based outer-apply duplication
Add these FOUR generic lemmas (COMPILED — transcribe verbatim), in `namespace Adapter`:

```lean
theorem applyTypeOpt_dynamic_comm {α : Type} (e : ElfFile) (iDyn : Nat) (d : Array DynEntry)
    (ty : ShType) (hTyNe : ty ≠ ShType.SHT_DYNAMIC) (val? : Option α) (mk : α → SectionContent)
    (hIdx : e.dynamicIdx = some iDyn) :
    applyOpt (e.updateSectionContent iDyn (.dynamic d)) ((e.updateSectionContent iDyn (.dynamic d)).findUniqueTypeIdx ty) val? mk
      = (applyOpt e (e.findUniqueTypeIdx ty) val? mk).updateSectionContent iDyn (.dynamic d) :=
  applyOpt_updateSectionContent_dynamic_comm e iDyn d (fun f => f.findUniqueTypeIdx ty) val? mk
    (ElfFile.updateSectionContent_dynamic_findUniqueTypeIdx e iDyn d hIdx ty)
    (fun i hi => ElfFile.findUniqueTypeIdx_ne_dynamicIdx e ty hTyNe iDyn hIdx i hi)

theorem applyTypeOpt_dynamicIdx {α : Type} (e : ElfFile) (ty : ShType) (hTyNe : ty ≠ ShType.SHT_DYNAMIC)
    (val? : Option α) (mk : α → SectionContent) (hmk : ∀ v, (mk v).type ≠ ShType.SHT_DYNAMIC) :
    (applyOpt e (e.findUniqueTypeIdx ty) val? mk).dynamicIdx = e.dynamicIdx := by
  apply applyOpt_dynamicIdx e (e.findUniqueTypeIdx ty) val? mk hmk
  intro i hi hb
  obtain ⟨_, hTy⟩ := ElfFile.findUniqueTypeIdx_section_type e ty i hi
  rw [hTy]; exact hTyNe

theorem applyTypeOpt_content_at {α : Type} (e : ElfFile) (ty : ShType)
    (hTyNe : ty ≠ ShType.SHT_DYNAMIC) (val? : Option α) (mk : α → SectionContent)
    (iDyn : Nat) (hIdx : e.dynamicIdx = some iDyn) (hb : iDyn < e.sections.size)
    (hb' : iDyn < (applyOpt e (e.findUniqueTypeIdx ty) val? mk).sections.size) :
    ((applyOpt e (e.findUniqueTypeIdx ty) val? mk).sections[iDyn]'hb').content
      = (e.sections[iDyn]'hb).content :=
  applyOpt_content_at_ne e (e.findUniqueTypeIdx ty) val? mk iDyn
    (fun i hi => ElfFile.findUniqueTypeIdx_ne_dynamicIdx e ty hTyNe iDyn hIdx i hi) hb hb'
```
(Generic `sections_size` is just `by simp`, so the existing per-apply `@[simp]` ones can stay.)

Then re-express the 4×3 lemmas `apply{Versym,SysvHash,GnuHash,Verneed}_{dynamic_comm,dynamicIdx,content_at}`
as one-line wrappers — KEEP THE NAMES (callers use them). Pattern (versym shown):
```lean
theorem applyVersym_dynamic_comm (e : ElfFile) (iDyn : Nat) (d : Array DynEntry)
    (hIdx : e.dynamicIdx = some iDyn) (vs? : Option (Array UInt16)) :
    applyVersym (e.updateSectionContent iDyn (.dynamic d)) vs?
      = (applyVersym e vs?).updateSectionContent iDyn (.dynamic d) := by
  unfold applyVersym ElfFile.versymIdx
  exact applyTypeOpt_dynamic_comm e iDyn d ShType.SHT_GNU_VERSYM (by decide) vs? _ hIdx
```
For `_dynamicIdx` the `hmk` arg is `(fun v => by simp only [SectionContent.type]; decide)`.
The ShTypes: versym→SHT_GNU_VERSYM, sysvHash→SHT_HASH, gnuHash→SHT_GNU_HASH, verneed→SHT_GNU_VERNEED.
Build + tests + axiom check on the removeRpath capstone (must be unchanged).

## Commit 3 — genericize factoring + transport over `f`
Add `applyDynamic_factor_general`, `innerChain_factor_general`, `toElfFile_mapDynamicOp_factor`,
`mapDynamicOp_structural_transport` (all COMPILED — bodies in `/tmp/verified-generic-chain.lean`
and `/tmp/verified-filterneeded.lean`, OR re-derive from the existing `*_removeRpath_*` bodies by
the substitution `td.stripRpath → f td`, `removeRpath → mapDynamicOp f`,
`removeRpath_dynamic/fields → mapDynamicOp_fields`, and `patchDynamicEntries_stripRpath_size_le → hSizeBound`).
KEY proven facts:
- `applyDynamic_factor_general`: `unfold applyDynamic; rw [hIdx, hByte, ElfFile.updateSectionContent_set_set]`.
- `toElfFile_mapDynamicOp_factor` sections bullet: `rw [toElfFile_expand, toElfFile_expand]`, then a
  `show … (typed.dynamic.map f) …`, then `rw [hTd]; simp only [Option.map_some];
  rw [innerChain_factor_general …]; exact ElfFile.updateSectionContent_sections_eq_of_sections _ _ iDyn _ rfl`.
  Header/phdrs bullets end with `; rfl`.
- `mapDynamicOp_structural_transport`: takes `(f) (D : RemoveRpathFactorData …)
  (hSizeBound : (patchDynamicEntries D.bd (f D.td)).size ≤ (patchDynamicEntries D.bd D.td).size)`
  + the 7 no-op structural hyps; body is `removeRpath_structural_transport` verbatim with
  `toElfFile_removeRpath_factor → toElfFile_mapDynamicOp_factor … f …` and
  `patchDynamicEntries_stripRpath_size_le D.bd D.td → hSizeBound`.
Add a generic capstone `toElfFile_mapDynamicOp_tierD_roundtrip_derived` (the §E body with
`removeRpath → mapDynamicOp f`, threading `hSizeBound`). Build + tests.

## Commit 4 — re-derive removeRpath + add modifyRPath.remove (regression gate)
- Replace the bodies (NOT statements) of `removeRpath_structural_transport` and
  `toElfFile_removeRpath_tierD_roundtrip_derived` with instantiations:
  `mapDynamicOp_structural_transport template typed h (fun d => d.stripRpath) D
     (patchDynamicEntries_stripRpath_size_le D.bd D.td) hHP …`. This TYPECHECKS because
  `removeRpath typed h` is definitionally `mapDynamicOp typed (·.stripRpath)` (VERIFIED:
  the `exact` closes with no coercion). The old `innerChain_removeRpath_factor` /
  `toElfFile_removeRpath_factor` / `removeRpath_{dynstr,fields,dynamic}` become dead — delete them.
- Add `toElfFile_modifyRPath_remove_tierD_roundtrip_derived` (modifyRPath .remove = same `f`,
  reuse `patchDynamicEntries_stripRpath_size_le`). `modifyRPath` signature:
  `modifyRPath e forceRpath .remove newRpath h` (Ops/Rpath.lean) — and
  `modifyRPath e fr .remove p h = mapDynamicOp e (·.stripRpath)` by `rfl`.
- Build + tests + axiom check (removeRpath capstone axioms == pre-refactor).

## Commit 5 — removeNeeded (the payoff; ONLY genuinely new proof work)
The new per-`f` size bound `patchDynamicEntries_filterNeededBy_size_le`:
`(patchDynamicEntries bd (d.filterNeededBy t)).size ≤ (patchDynamicEntries bd d).size`.
ALL ingredients COMPILED (in `/tmp/verified-filterneeded.lean`):
- `appendSurplusNeeded_size_exact` (proved): `(appendSurplusNeeded typed result startIdx).size
  = result.size + (typed.needed.size - startIdx)` — generalize over a range bound `n` with
  `startIdx + n ≤ size`, induct, `rw [List.range_succ, List.foldl_append, List.foldl_cons,
  List.foldl_nil]; simp only [dif_pos hh, Array.size_push, ih acc (by omega)]; omega`.
- `NeededRel` (potential `result.size + (needed.size − cursor)`, + cursor bounds + 5 applied flags)
  and `patchStep_filterNeeded` (proved): `cases d.tag`; `.needed` arm = `by_cases` on each
  cursor<size (4-way) then `refine ⟨by omega,…⟩`; other arms `(try split) <;> refine ⟨…⟩ <;>
  first | (simp only [Array.size_push]; omega) | omega | assumption | rfl | simp_all`.
- `loop_filterNeeded` (proved): `Array.foldl_rel NeededRel …`; init needs
  `Array.size_filter_le` (= `unfold DynamicSection.filterNeededBy; exact Array.size_filter_le`).
REMAINING (not yet composed, but every ingredient above is proven; mirrors `tail_shrink_rpath`):
  the tail bound combining `loop_filterNeeded` + `appendSurplusNeeded_size_exact` (both sides)
  + equal `appendUnless` blocks (filterNeededBy leaves rpath/runpath/soname/flags1/debug AND
  their applied-flags equal — use `appendUnless_size_mono` per layer) + equal null push.
  Shape: `final2.size = surplus2 + (5 equal unless deltas) + 1`, and `surplus2 = result2 + (n2−cur2)`,
  `surplus1 = result1 + (n1−cur1)`, with `result2+(n2−cur2) ≤ result1+(n1−cur1)` from `NeededRel`.
Then `removeNeeded` capstone = `toElfFile_mapDynamicOp_tierD_roundtrip_derived` instantiated at
`(·.filterNeededBy lib.toUTF8)` + this size bound. (`modifySoname.remove` is an OPTIONAL third
op: a `removeSoname` size bound, shrink in the soname tail block — a `ShrinkRel`-shaped variant.)

## Reference artifacts (this session)
`/tmp/verified-generic-chain.lean` and `/tmp/verified-filterneeded.lean` hold the COMPILED bodies
of every lemma above EXCEPT the Commit-5 tail composition and the capstones. If those /tmp files
are gone (new machine/session), re-derive from the substitution recipe — all shapes are proven.

## Final docs (after Commit 5)
Update STATUS.md / ROADMAP.md / INVENTORY.md / PICKUP-PROMPT-OP-TIER-D.md: removeRpath +
modifyRPath.remove + removeNeeded derived; the generic `mapDynamicOp` machinery; new lake job count.
