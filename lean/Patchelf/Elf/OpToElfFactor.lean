/-
  Op-through-`toElfFile` factoring for shrinking ops (ROADMAP §5.1).

  Goal: factor `toElfFile template (removeRpath typed h)` as a single
  `(toElfFile template typed).updateSectionContent iDyn (.dynamic newDyn)`
  on the NO-OP adapter output, with `newDyn.size ≤` the no-op's dynamic
  content size — so the reusable shrink-monotonicity lemmas in
  `SectionOps.lean` transport the 6 structural disjointness invariants +
  section-0-NULL from the no-op output to the op output, *deriving* them
  rather than hypothesizing.

  `removeRpath` changes only `typed.dynamic` (via `stripRpath`), leaving every
  other typed field `rfl`-equal.  So `eo` and `base := toElfFile template typed`
  share the whole `applyX` chain except the `applyDynamic` argument; pushing
  that single content update out through the outer applies
  (`applyVersym`…`applyInterp`, each at a section index ≠ the dynamic index)
  yields the factoring.

  Structure (two namespace blocks):
  * `namespace Patchelf.Elf` — generic `updateSectionContent` algebra
    (`_comm`, `_set_set`, content congruences, `findUniqueTypeIdx` facts).
  * `namespace Patchelf.Elf.Adapter` — the `applyOpt`-commutation primitive,
    per-apply commutation / `dynamicIdx`-preservation / `sections.size`-
    preservation / content-at-`iDyn` lemmas, the chain factoring
    (`toElfFile_removeRpath_factor`), content extraction
    (`toElfFile_content_at_dynamicIdx`), and the structural-invariant transport
    (`removeRpath_structural_transport`) composing the factoring + content + the
    `patchDynamicEntries` size bound (`Adapter.patchDynamicEntries_stripRpath_size_le`,
    `Adapter.lean`) with the `SectionOps.updateSectionContent_*Disjoint_shrink`
    family, plus the §E Tier-D capstone.

  The `applyInterp` commutation/content lemmas take the interp-vs-dynamic index
  distinctness as a hypothesis (`hInterpNe`); the `RemoveRpathFactorData` bundle
  packages the per-op facts about the intermediate `applyX` files (the prefix
  file's dynamic index/content witnesses + interp distinctness).
-/
module
public import Patchelf.Elf.OpAdapterPreservation
@[expose] public section

namespace Patchelf.Elf
open Patchelf.Elf.Layout (ShType)

-- Sections of a double update, via getElem characterization (no rw under dep bound).
theorem ElfFile.updateSectionContent_comm (e : ElfFile) (i j : Nat) (ci cj : SectionContent)
    (hij : i ≠ j) :
    (e.updateSectionContent i ci).updateSectionContent j cj
      = (e.updateSectionContent j cj).updateSectionContent i ci := by
  have key : ∀ (a b : ElfFile), a.header = b.header → a.phdrs = b.phdrs →
      a.sections = b.sections → a = b := by
    intro a b h1 h2 h3; cases a; cases b; simp_all
  apply key _ _ (by simp) (by simp)
  apply Array.ext
  · simp [ElfFile.updateSectionContent_sections_size]
  · intro k hk1 _hk2
    -- characterize each side's k-th section
    have hkLeft : k < ((e.updateSectionContent i ci).updateSectionContent j cj).sections.size := hk1
    by_cases hki : k = i <;> by_cases hkj : k = j
    · exact absurd (hki.symm.trans hkj) hij
    · -- k = i ≠ j : left = {orig_i with ci}, right = {orig_i with ci}
      subst hki
      have hbi : k < e.sections.size := by
        rwa [ElfFile.updateSectionContent_sections_size, ElfFile.updateSectionContent_sections_size] at hk1
      have hbi1 : k < (e.updateSectionContent k ci).sections.size := by
        rwa [ElfFile.updateSectionContent_sections_size]
      have hbi2 : k < (e.updateSectionContent j cj).sections.size := by
        rwa [ElfFile.updateSectionContent_sections_size]
      rw [ElfFile.updateSectionContent_getElem_ne _ j cj k hbi1 hkj,
          ElfFile.updateSectionContent_getElem_self _ k ci hbi hbi1,
          ElfFile.updateSectionContent_getElem_self _ k ci hbi2 (by rwa [ElfFile.updateSectionContent_sections_size]),
          ElfFile.updateSectionContent_getElem_ne _ j cj k hbi hkj hbi2]
    · subst hkj
      have hbj : k < e.sections.size := by
        rwa [ElfFile.updateSectionContent_sections_size, ElfFile.updateSectionContent_sections_size] at hk1
      have hbj1 : k < (e.updateSectionContent i ci).sections.size := by rwa [ElfFile.updateSectionContent_sections_size]
      have hbj2 : k < (e.updateSectionContent k cj).sections.size := by rwa [ElfFile.updateSectionContent_sections_size]
      rw [ElfFile.updateSectionContent_getElem_self _ k cj hbj1 hk1,
          ElfFile.updateSectionContent_getElem_ne _ i ci k hbj hki hbj1,
          ElfFile.updateSectionContent_getElem_ne _ i ci k hbj2 hki (by rwa [ElfFile.updateSectionContent_sections_size]),
          ElfFile.updateSectionContent_getElem_self _ k cj hbj hbj2]
    · -- k ≠ i, k ≠ j
      have hb : k < e.sections.size := by
        rwa [ElfFile.updateSectionContent_sections_size, ElfFile.updateSectionContent_sections_size] at hk1
      have hb1 : k < (e.updateSectionContent i ci).sections.size := by rwa [ElfFile.updateSectionContent_sections_size]
      have hb2 : k < (e.updateSectionContent j cj).sections.size := by rwa [ElfFile.updateSectionContent_sections_size]
      rw [ElfFile.updateSectionContent_getElem_ne _ j cj k hb1 hkj,
          ElfFile.updateSectionContent_getElem_ne _ i ci k hb hki hb1,
          ElfFile.updateSectionContent_getElem_ne _ i ci k hb2 hki,
          ElfFile.updateSectionContent_getElem_ne _ j cj k hb hkj hb2]

-- Content at i after updating i with c is c.content-of (bound-free conclusion).
theorem ElfFile.getElem_content_congr_sections (a b : ElfFile) (i : Nat)
    (hs : a.sections = b.sections) (hi : i < a.sections.size) :
    (a.sections[i]'hi).content = (b.sections[i]'(hs ▸ hi)).content := by
  -- generalize the two section arrays, then subst the equality.
  obtain ⟨_, _, sa⟩ := a
  obtain ⟨_, _, sb⟩ := b
  simp only at hs ⊢
  subst hs
  rfl

theorem ElfFile.getElem_content_congr (a b : ElfFile) (i : Nat) (hab : a = b)
    (hi : i < a.sections.size) :
    (a.sections[i]'hi).content
      = (b.sections[i]'(hab ▸ hi)).content := by
  subst hab; rfl

theorem ElfFile.updateSectionContent_content_self (e : ElfFile) (i : Nat) (c : SectionContent)
    (hi' : i < (e.updateSectionContent i c).sections.size) :
    ((e.updateSectionContent i c).sections[i]'hi').content = c := by
  have hi : i < e.sections.size := by rwa [ElfFile.updateSectionContent_sections_size] at hi'
  have he : ((e.updateSectionContent i c).sections[i]'hi')
      = { e.sections[i]'hi with content := c } :=
    ElfFile.updateSectionContent_getElem_self e i c hi hi'
  exact congrArg Section.content he

-- set-set at same index: last wins.
theorem ElfFile.updateSectionContent_set_set (e : ElfFile) (i : Nat) (a b : SectionContent) :
    (e.updateSectionContent i a).updateSectionContent i b = e.updateSectionContent i b := by
  have key : ∀ (x y : ElfFile), x.header = y.header → x.phdrs = y.phdrs →
      x.sections = y.sections → x = y := by
    intro x y h1 h2 h3; cases x; cases y; simp_all
  apply key _ _ (by simp) (by simp)
  by_cases hi : i < e.sections.size
  · apply Array.ext
    · simp [ElfFile.updateSectionContent_sections_size]
    · intro k hk1 _
      have hb : k < e.sections.size := by
        rwa [ElfFile.updateSectionContent_sections_size, ElfFile.updateSectionContent_sections_size] at hk1
      have hbb : k < (e.updateSectionContent i b).sections.size := by
        rwa [ElfFile.updateSectionContent_sections_size]
      have hba : k < (e.updateSectionContent i a).sections.size := by
        rwa [ElfFile.updateSectionContent_sections_size]
      by_cases hki : k = i
      · subst hki
        rw [ElfFile.updateSectionContent_getElem_self _ k b hba hk1,
            ElfFile.updateSectionContent_getElem_self _ k a hb hba,
            ElfFile.updateSectionContent_getElem_self _ k b hb hbb]
      · rw [ElfFile.updateSectionContent_getElem_ne _ i b k hba hki hk1,
            ElfFile.updateSectionContent_getElem_ne _ i a k hb hki hba,
            ElfFile.updateSectionContent_getElem_ne _ i b k hb hki hbb]
  · simp only [ElfFile.updateSectionContent, dif_neg hi]

-- If iDyn is the dynamic index, the section there has type SHT_DYNAMIC.
theorem ElfFile.type_at_dynamicIdx (e : ElfFile) (iDyn : Nat) (h : e.dynamicIdx = some iDyn) :
    ∃ hb : iDyn < e.sections.size, (e.sections[iDyn]'hb).type = ShType.SHT_DYNAMIC := by
  unfold dynamicIdx at h
  exact ElfFile.findUniqueTypeIdx_section_type e _ _ h

-- A `.dynamic` update at iDyn preserves findUniqueTypeIdx for ANY type
-- (the updated section keeps type SHT_DYNAMIC = its original type).
theorem ElfFile.updateSectionContent_dynamic_findUniqueTypeIdx (e : ElfFile)
    (iDyn : Nat) (d : Array DynEntry) (hIdx : e.dynamicIdx = some iDyn) (ty : ShType) :
    (e.updateSectionContent iDyn (.dynamic d)).findUniqueTypeIdx ty = e.findUniqueTypeIdx ty := by
  obtain ⟨hb, hTy⟩ := ElfFile.type_at_dynamicIdx e iDyn hIdx
  apply ElfFile.updateSectionContent_findUniqueTypeIdx
  intro hi
  rw [hTy]; rfl

-- A findUniqueTypeIdx for a NON-dynamic type cannot equal the dynamic index.
theorem ElfFile.findUniqueTypeIdx_ne_dynamicIdx (e : ElfFile) (ty : ShType)
    (hTyNe : ty ≠ ShType.SHT_DYNAMIC) (iDyn : Nat) (hDyn : e.dynamicIdx = some iDyn)
    (i : Nat) (hi : e.findUniqueTypeIdx ty = some i) : i ≠ iDyn := by
  intro hEq; subst hEq
  obtain ⟨hb, hTyD⟩ := ElfFile.type_at_dynamicIdx e i hDyn
  obtain ⟨hb', hTyI⟩ := ElfFile.findUniqueTypeIdx_section_type e ty i hi
  rw [hTyD] at hTyI; exact hTyNe hTyI.symm

-- Record header/phdrs override commutes with a sections update.
theorem ElfFile.updateSectionContent_sections_eq_of_sections (a b : ElfFile) (i : Nat)
    (c : SectionContent) (hs : a.sections = b.sections) :
    (a.updateSectionContent i c).sections = (b.updateSectionContent i c).sections := by
  by_cases hi : i < a.sections.size
  · rw [ElfFile.updateSectionContent_sections a i c hi,
        ElfFile.updateSectionContent_sections b i c (hs ▸ hi)]
    simp only [hs]
  · have hi' : ¬ i < b.sections.size := by rw [← hs]; exact hi
    simp only [updateSectionContent, dif_neg hi, dif_neg hi']
    exact hs

theorem ElfFile.with_header_phdrs_updateSectionContent (e : ElfFile)
    (hdr : ElfHeader) (phs : Array ProgramHeader) (i : Nat) (c : SectionContent) :
    ({ e with header := hdr, phdrs := phs } : ElfFile).updateSectionContent i c
      = { e.updateSectionContent i c with header := hdr, phdrs := phs } := by
  unfold updateSectionContent
  by_cases hi : i < e.sections.size <;> simp [hi]

-- updateSectionContent preserves findUniqueTypeIdx ty when BOTH the new content
-- and the original content at i have type ≠ ty.
theorem ElfFile.updateSectionContent_findUniqueTypeIdx_both_ne (e : ElfFile)
    (i : Nat) (c : SectionContent) (ty : ShType)
    (hcNe : c.type ≠ ty)
    (hOrigNe : ∀ hi : i < e.sections.size, (e.sections[i]'hi).type ≠ ty) :
    (e.updateSectionContent i c).findUniqueTypeIdx ty = e.findUniqueTypeIdx ty := by
  unfold ElfFile.findUniqueTypeIdx
  by_cases hi : i < e.sections.size
  · rw [show (e.updateSectionContent i c).sections =
            e.sections.set i { e.sections[i]'hi with content := c } hi from
          ElfFile.updateSectionContent_sections e i c hi]
    apply ElfFile.firstIdxWhereIn_update_both_false _ _ i hi
    · show decide (({ e.sections[i]'hi with content := c } : Section).type = ty) = false
      simp [Section.type, hcNe]
    · exact decide_eq_false_iff_not.mpr (hOrigNe hi)
  · simp [ElfFile.updateSectionContent, dif_neg hi]

end Patchelf.Elf


namespace Patchelf.Elf.Adapter
open Patchelf.Elf (ElfFile StringTable DynEntry DynTag SectionContent EncodePreconditions
                     parse encode prepLayoutForEncode syncDtStrszInFile IdentBytesValid
                     prepLayout_syncDtStrsz_preserves_valid)
open Patchelf.Elf.Layout (ShType)

-- Generic: applyOpt with a FIXED type-based index commutes with a dynamic update
-- at iDyn, provided (a) the index recomputed on the updated file equals the same
-- target, and (b) that target ≠ iDyn.
theorem applyOpt_updateSectionContent_dynamic_comm {α : Type}
    (e : ElfFile) (iDyn : Nat) (dDyn : Array DynEntry)
    (idxOf : ElfFile → Option Nat) (val? : Option α) (mk : α → SectionContent)
    (hIdxPres : idxOf (e.updateSectionContent iDyn (.dynamic dDyn)) = idxOf e)
    (hNe : ∀ i, idxOf e = some i → i ≠ iDyn) :
    applyOpt (e.updateSectionContent iDyn (.dynamic dDyn)) (idxOf (e.updateSectionContent iDyn (.dynamic dDyn))) val? mk
      = (applyOpt e (idxOf e) val? mk).updateSectionContent iDyn (.dynamic dDyn) := by
  rw [hIdxPres]
  unfold applyOpt
  cases hIdx : idxOf e with
  | none => simp
  | some i =>
      cases val? with
      | none => simp
      | some v =>
          simp only
          exact ElfFile.updateSectionContent_comm e iDyn i (.dynamic dDyn) (mk v) (Ne.symm (hNe i hIdx))

-- applyDynamic on stripRpath td = applyDynamic on td, then re-update iDyn with
-- the stripRpath patch (last-wins set-set).
theorem applyDynamic_stripRpath_factor (e₀ : ElfFile) {ds : StringSection}
    (td : DynamicSection ds) (iDyn : Nat) (hIdx : e₀.dynamicIdx = some iDyn)
    (bd : Array DynEntry) (hByte : e₀.dynamic = some bd) :
    applyDynamic e₀ (ds := ds) (some td.stripRpath)
      = (applyDynamic e₀ (ds := ds) (some td)).updateSectionContent iDyn
          (.dynamic (patchDynamicEntries bd td.stripRpath)) := by
  unfold applyDynamic
  rw [hIdx, hByte]
  -- both sides: e₀.updateSectionContent iDyn (.dynamic (patch bd stripRpath))
  --   vs (e₀.update iDyn (.dynamic (patch bd td))).update iDyn (.dynamic (patch bd stripRpath))
  rw [ElfFile.updateSectionContent_set_set]

-- Generic type-based outer-apply commutation: an `applyOpt` keyed on
-- `findUniqueTypeIdx ty` (ty ≠ SHT_DYNAMIC) commutes with a `.dynamic` update at
-- iDyn.  The four per-type applies (versym/sysv/gnu/verneed) are thin wrappers.
theorem applyTypeOpt_dynamic_comm {α : Type} (e : ElfFile) (iDyn : Nat) (d : Array DynEntry)
    (ty : ShType) (hTyNe : ty ≠ ShType.SHT_DYNAMIC) (val? : Option α) (mk : α → SectionContent)
    (hIdx : e.dynamicIdx = some iDyn) :
    applyOpt (e.updateSectionContent iDyn (.dynamic d)) ((e.updateSectionContent iDyn (.dynamic d)).findUniqueTypeIdx ty) val? mk
      = (applyOpt e (e.findUniqueTypeIdx ty) val? mk).updateSectionContent iDyn (.dynamic d) :=
  applyOpt_updateSectionContent_dynamic_comm e iDyn d (fun f => f.findUniqueTypeIdx ty) val? mk
    (ElfFile.updateSectionContent_dynamic_findUniqueTypeIdx e iDyn d hIdx ty)
    (fun i hi => ElfFile.findUniqueTypeIdx_ne_dynamicIdx e ty hTyNe iDyn hIdx i hi)

-- Commutation of applyVersym with a dynamic update at iDyn.
theorem applyVersym_dynamic_comm (e : ElfFile) (iDyn : Nat) (d : Array DynEntry)
    (hIdx : e.dynamicIdx = some iDyn) (vs? : Option (Array UInt16)) :
    applyVersym (e.updateSectionContent iDyn (.dynamic d)) vs?
      = (applyVersym e vs?).updateSectionContent iDyn (.dynamic d) := by
  unfold applyVersym ElfFile.versymIdx
  exact applyTypeOpt_dynamic_comm e iDyn d ShType.SHT_GNU_VERSYM (by decide) vs? _ hIdx

theorem applySysvHash_dynamic_comm (e : ElfFile) (iDyn : Nat) (d : Array DynEntry)
    (hIdx : e.dynamicIdx = some iDyn) (x? : Option SysVHashSection) :
    applySysvHash (e.updateSectionContent iDyn (.dynamic d)) x?
      = (applySysvHash e x?).updateSectionContent iDyn (.dynamic d) := by
  unfold applySysvHash ElfFile.sysvHashIdx
  exact applyTypeOpt_dynamic_comm e iDyn d ShType.SHT_HASH (by decide) x? _ hIdx

theorem applyGnuHash_dynamic_comm (e : ElfFile) (iDyn : Nat) (d : Array DynEntry)
    (hIdx : e.dynamicIdx = some iDyn) (x? : Option GnuHashSection) :
    applyGnuHash (e.updateSectionContent iDyn (.dynamic d)) x?
      = (applyGnuHash e x?).updateSectionContent iDyn (.dynamic d) := by
  unfold applyGnuHash ElfFile.gnuHashIdx
  exact applyTypeOpt_dynamic_comm e iDyn d ShType.SHT_GNU_HASH (by decide) x? _ hIdx

theorem applyVerneed_dynamic_comm (e : ElfFile) (iDyn : Nat) (d : Array DynEntry)
    (hIdx : e.dynamicIdx = some iDyn) (x? : Option VerneedSection) :
    applyVerneed (e.updateSectionContent iDyn (.dynamic d)) x?
      = (applyVerneed e x?).updateSectionContent iDyn (.dynamic d) := by
  unfold applyVerneed ElfFile.verneedIdx
  exact applyTypeOpt_dynamic_comm e iDyn d ShType.SHT_GNU_VERNEED (by decide) x? _ hIdx

-- interpIdx is preserved under a `.dynamic` update at iDyn, and ≠ iDyn,
-- given a content-dynamic witness + dynstr witness at iDyn (so iDyn ≠ shstrndx).
theorem applyInterp_dynamic_comm (e : ElfFile) (iDyn : Nat) (d : Array DynEntry)
    (hb : iDyn < e.sections.size) (dyn : Array DynEntry)
    (hContent : (e.sections[iDyn]'hb).content = .dynamic dyn)
    {dsT : StringTable} (hDs : e.dynstr = some dsT)
    (hInterpNe : ∀ i, e.interpIdx = some i → i ≠ iDyn)
    (interp? : Option InterpSection) :
    applyInterp (e.updateSectionContent iDyn (.dynamic d)) interp?
      = (applyInterp e interp?).updateSectionContent iDyn (.dynamic d) := by
  have hShstrNe : iDyn ≠ e.header.shstrndx.toNat :=
    ElfFile.shstrndx_ne_of_content_dynamic_of_dynstr e hb hContent hDs
  unfold applyInterp ElfFile.interpIdx
  have hIdxPres : (e.updateSectionContent iDyn (.dynamic d)).findIdxByName ".interp".toUTF8
      = e.findIdxByName ".interp".toUTF8 :=
    ElfFile.updateSectionContent_findIdxByName e iDyn (.dynamic d) _ hShstrNe
  exact applyOpt_updateSectionContent_dynamic_comm e iDyn d
    (fun f => f.findIdxByName ".interp".toUTF8) interp? _ hIdxPres
    (fun i hi => hInterpNe i hi)

-- applyOpt with a non-dynamic content type preserves dynamicIdx, given the
-- original section at the target (if in range) isn't DYNAMIC either.
theorem applyOpt_dynamicIdx {α : Type} (e : ElfFile) (idx? : Option Nat) (val? : Option α)
    (mk : α → SectionContent) (hmk : ∀ v, (mk v).type ≠ ShType.SHT_DYNAMIC)
    (hOrig : ∀ i, idx? = some i → ∀ hi : i < e.sections.size,
      (e.sections[i]'hi).type ≠ ShType.SHT_DYNAMIC) :
    (applyOpt e idx? val? mk).dynamicIdx = e.dynamicIdx := by
  unfold applyOpt
  cases hidx : idx? with
  | none => simp
  | some i =>
    cases val? with
    | none => simp
    | some v =>
      simp only
      unfold ElfFile.dynamicIdx
      exact ElfFile.updateSectionContent_findUniqueTypeIdx_both_ne e i (mk v) _
        (hmk v) (hOrig i hidx)

-- applyDynamic (some _) preserves dynamicIdx (updates the dynamic section in place,
-- keeping type SHT_DYNAMIC).
theorem applyDynamic_dynamicIdx (e : ElfFile) {ds : StringSection}
    (dynamic? : Option (DynamicSection ds)) (iDyn : Nat) (hIdx : e.dynamicIdx = some iDyn) :
    (applyDynamic e (ds := ds) dynamic?).dynamicIdx = e.dynamicIdx := by
  have hudyn : ∀ d, (e.updateSectionContent iDyn (.dynamic d)).dynamicIdx = e.dynamicIdx := by
    intro d
    unfold ElfFile.dynamicIdx
    exact ElfFile.updateSectionContent_dynamic_findUniqueTypeIdx e iDyn d hIdx _
  unfold applyDynamic
  cases dynamic? with
  | none => simp
  | some td =>
    rw [hIdx]
    cases hb : e.dynamic with
    | none => simp only; exact (hudyn _).trans hIdx
    | some bd => simp only; exact (hudyn _).trans hIdx

-- Generic: a type-based outer-apply (ty ≠ SHT_DYNAMIC) targets a section of
-- type `ty`, so it preserves dynamicIdx.  The four per-type applies are wrappers.
theorem applyTypeOpt_dynamicIdx {α : Type} (e : ElfFile) (ty : ShType) (hTyNe : ty ≠ ShType.SHT_DYNAMIC)
    (val? : Option α) (mk : α → SectionContent) (hmk : ∀ v, (mk v).type ≠ ShType.SHT_DYNAMIC) :
    (applyOpt e (e.findUniqueTypeIdx ty) val? mk).dynamicIdx = e.dynamicIdx := by
  apply applyOpt_dynamicIdx e (e.findUniqueTypeIdx ty) val? mk hmk
  intro i hi hb
  obtain ⟨_, hTy⟩ := ElfFile.findUniqueTypeIdx_section_type e ty i hi
  rw [hTy]; exact hTyNe

-- Each outer apply targets a section of its OWN type (≠ DYNAMIC), so it
-- preserves dynamicIdx.
theorem applyVersym_dynamicIdx (e : ElfFile) (vs? : Option (Array UInt16)) :
    (applyVersym e vs?).dynamicIdx = e.dynamicIdx := by
  unfold applyVersym ElfFile.versymIdx
  exact applyTypeOpt_dynamicIdx e ShType.SHT_GNU_VERSYM (by decide) vs? _ (fun v => by simp only [SectionContent.type]; decide)

theorem applySysvHash_dynamicIdx (e : ElfFile) (x? : Option SysVHashSection) :
    (applySysvHash e x?).dynamicIdx = e.dynamicIdx := by
  unfold applySysvHash ElfFile.sysvHashIdx
  exact applyTypeOpt_dynamicIdx e ShType.SHT_HASH (by decide) x? _ (fun v => by simp only [SectionContent.type]; decide)

theorem applyGnuHash_dynamicIdx (e : ElfFile) (x? : Option GnuHashSection) :
    (applyGnuHash e x?).dynamicIdx = e.dynamicIdx := by
  unfold applyGnuHash ElfFile.gnuHashIdx
  exact applyTypeOpt_dynamicIdx e ShType.SHT_GNU_HASH (by decide) x? _ (fun v => by simp only [SectionContent.type]; decide)

theorem applyVerneed_dynamicIdx (e : ElfFile) (x? : Option VerneedSection) :
    (applyVerneed e x?).dynamicIdx = e.dynamicIdx := by
  unfold applyVerneed ElfFile.verneedIdx
  exact applyTypeOpt_dynamicIdx e ShType.SHT_GNU_VERNEED (by decide) x? _ (fun v => by simp only [SectionContent.type]; decide)

/-- Outer-chain commutation: the whole `applyInterp ∘ applyVerneed ∘ applyGnuHash
    ∘ applySysvHash ∘ applyVersym` suffix commutes with a dynamic update at iDyn,
    given the dynamic index is preserved across the chain and interp ≠ iDyn.
    The three intermediate `dynamicIdx = some iDyn` facts are derived internally
    from `hIdxV` via the `applyX_dynamicIdx` preservation lemmas. -/
theorem outerChain_dynamic_comm (e₀ : ElfFile) (iDyn : Nat) (newD : Array DynEntry)
    (vs? : Option (Array UInt16)) (sh? : Option SysVHashSection)
    (gh? : Option GnuHashSection) (vn? : Option VerneedSection)
    (ip? : Option InterpSection)
    (hIdxV : e₀.dynamicIdx = some iDyn)
    (hbN : iDyn < (applyVerneed (applyGnuHash (applySysvHash (applyVersym e₀ vs?) sh?) gh?) vn?).sections.size)
    (dynN : Array DynEntry)
    (hContentN : ((applyVerneed (applyGnuHash (applySysvHash (applyVersym e₀ vs?) sh?) gh?) vn?).sections[iDyn]'hbN).content = .dynamic dynN)
    {dsN : StringTable}
    (hDsN : (applyVerneed (applyGnuHash (applySysvHash (applyVersym e₀ vs?) sh?) gh?) vn?).dynstr = some dsN)
    (hInterpNe : ∀ i, (applyVerneed (applyGnuHash (applySysvHash (applyVersym e₀ vs?) sh?) gh?) vn?).interpIdx = some i → i ≠ iDyn) :
    applyInterp (applyVerneed (applyGnuHash (applySysvHash (applyVersym
      (e₀.updateSectionContent iDyn (.dynamic newD)) vs?) sh?) gh?) vn?) ip?
      = (applyInterp (applyVerneed (applyGnuHash (applySysvHash (applyVersym
          e₀ vs?) sh?) gh?) vn?) ip?).updateSectionContent iDyn (.dynamic newD) := by
  rw [applyVersym_dynamic_comm e₀ iDyn newD hIdxV vs?,
      applySysvHash_dynamic_comm _ iDyn newD (by rw [applyVersym_dynamicIdx]; exact hIdxV) sh?,
      applyGnuHash_dynamic_comm _ iDyn newD (by rw [applySysvHash_dynamicIdx, applyVersym_dynamicIdx]; exact hIdxV) gh?,
      applyVerneed_dynamic_comm _ iDyn newD (by rw [applyGnuHash_dynamicIdx, applySysvHash_dynamicIdx, applyVersym_dynamicIdx]; exact hIdxV) vn?,
      applyInterp_dynamic_comm _ iDyn newD hbN dynN hContentN hDsN hInterpNe ip?]

@[simp] theorem applyOpt_sections_size {α : Type} (e : ElfFile) (idx? : Option Nat)
    (val? : Option α) (mk : α → SectionContent) :
    (applyOpt e idx? val? mk).sections.size = e.sections.size := by
  unfold applyOpt
  cases idx? <;> cases val? <;> simp [ElfFile.updateSectionContent_sections_size]

@[simp] theorem applyVersym_sections_size (e : ElfFile) (vs? : Option (Array UInt16)) :
    (applyVersym e vs?).sections.size = e.sections.size := by unfold applyVersym; simp
@[simp] theorem applySysvHash_sections_size (e : ElfFile) (x? : Option SysVHashSection) :
    (applySysvHash e x?).sections.size = e.sections.size := by unfold applySysvHash; simp
@[simp] theorem applyGnuHash_sections_size (e : ElfFile) (x? : Option GnuHashSection) :
    (applyGnuHash e x?).sections.size = e.sections.size := by unfold applyGnuHash; simp
@[simp] theorem applyVerneed_sections_size (e : ElfFile) (x? : Option VerneedSection) :
    (applyVerneed e x?).sections.size = e.sections.size := by unfold applyVerneed; simp
@[simp] theorem applyInterp_sections_size (e : ElfFile) (ip? : Option InterpSection) :
    (applyInterp e ip?).sections.size = e.sections.size := by unfold applyInterp; simp
@[simp] theorem applyDynamic_sections_size (e : ElfFile) {ds : StringSection}
    (dynamic? : Option (DynamicSection ds)) :
    (applyDynamic e (ds := ds) dynamic?).sections.size = e.sections.size := by
  unfold applyDynamic
  cases dynamic? with
  | none => simp
  | some td =>
    cases e.dynamicIdx with
    | none => simp
    | some i =>
      cases e.dynamic with
      | none => simp [ElfFile.updateSectionContent_sections_size]
      | some bd => simp [ElfFile.updateSectionContent_sections_size]

-- toElfFile expanded with the prefix file e₀ named, and the outer chain explicit.
theorem toElfFile_expand (template : ElfFile) (typed : ValidElfFile) :
    toElfFile template typed
      = { applyInterp (applyVerneed (applyGnuHash (applySysvHash (applyVersym
            (applyDynamic (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym)
              (ds := typed.dynstr) typed.dynamic) typed.versym) typed.sysvHash)
              typed.gnuHash) typed.verneed) typed.interp
          with header := typed.header, phdrs := typed.phdrs } := rfl

-- removeRpath agrees with typed on every field except dynamic (which is mapped).
theorem removeRpath_dynstr (typed : ValidElfFile) (h : typed.dynamic.isSome) :
    (removeRpath typed h).dynstr = typed.dynstr := rfl
theorem removeRpath_fields (typed : ValidElfFile) (h : typed.dynamic.isSome) :
    (removeRpath typed h).dynsym = typed.dynsym ∧ (removeRpath typed h).versym = typed.versym ∧
    (removeRpath typed h).sysvHash = typed.sysvHash ∧ (removeRpath typed h).gnuHash = typed.gnuHash ∧
    (removeRpath typed h).verneed = typed.verneed ∧ (removeRpath typed h).interp = typed.interp ∧
    (removeRpath typed h).header = typed.header ∧ (removeRpath typed h).phdrs = typed.phdrs :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem removeRpath_dynamic (typed : ValidElfFile) (h : typed.dynamic.isSome) :
    (removeRpath typed h).dynamic = typed.dynamic.map (fun d => d.stripRpath) := rfl

-- Inner-chain factoring (no header/phdrs override): the applyInterp∘…∘applyDynamic
-- chain on stripRpath td equals the no-op chain, updated at iDyn.
theorem innerChain_removeRpath_factor (template : ElfFile) (typed : ValidElfFile)
    (td : DynamicSection typed.dynstr) (iDyn : Nat)
    (hIdx0 : (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym).dynamicIdx = some iDyn)
    (bd : Array DynEntry)
    (hByte0 : (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym).dynamic = some bd)
    (hbN : iDyn < (applyVerneed (applyGnuHash (applySysvHash (applyVersym
              (applyDynamic (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym)
                (ds := typed.dynstr) (some td)) typed.versym) typed.sysvHash) typed.gnuHash) typed.verneed).sections.size)
    (dynN : Array DynEntry)
    (hContentN : ((applyVerneed (applyGnuHash (applySysvHash (applyVersym
              (applyDynamic (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym)
                (ds := typed.dynstr) (some td)) typed.versym) typed.sysvHash) typed.gnuHash) typed.verneed).sections[iDyn]'hbN).content = .dynamic dynN)
    {dsN : StringTable}
    (hDsN : (applyVerneed (applyGnuHash (applySysvHash (applyVersym
              (applyDynamic (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym)
                (ds := typed.dynstr) (some td)) typed.versym) typed.sysvHash) typed.gnuHash) typed.verneed).dynstr = some dsN)
    (hInterpNe : ∀ i, (applyVerneed (applyGnuHash (applySysvHash (applyVersym
              (applyDynamic (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym)
                (ds := typed.dynstr) (some td)) typed.versym) typed.sysvHash) typed.gnuHash) typed.verneed).interpIdx = some i → i ≠ iDyn) :
    applyInterp (applyVerneed (applyGnuHash (applySysvHash (applyVersym
        (applyDynamic (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym)
          (ds := typed.dynstr) (some td.stripRpath)) typed.versym) typed.sysvHash) typed.gnuHash) typed.verneed) typed.interp
      = (applyInterp (applyVerneed (applyGnuHash (applySysvHash (applyVersym
          (applyDynamic (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym)
            (ds := typed.dynstr) (some td)) typed.versym) typed.sysvHash) typed.gnuHash) typed.verneed) typed.interp).updateSectionContent
        iDyn (.dynamic (patchDynamicEntries bd td.stripRpath)) := by
  rw [applyDynamic_stripRpath_factor _ td iDyn hIdx0 bd hByte0]
  have hIdxBase : (applyDynamic (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym)
      (ds := typed.dynstr) (some td)).dynamicIdx = some iDyn :=
    (applyDynamic_dynamicIdx _ _ iDyn hIdx0).trans hIdx0
  rw [outerChain_dynamic_comm _ iDyn (patchDynamicEntries bd td.stripRpath)
        typed.versym typed.sysvHash typed.gnuHash typed.verneed typed.interp
        hIdxBase
        hbN dynN hContentN hDsN hInterpNe]

-- Master factoring: eo = base.updateSectionContent iDyn (.dynamic newDyn).
theorem toElfFile_removeRpath_factor (template : ElfFile) (typed : ValidElfFile)
    (h : typed.dynamic.isSome) (td : DynamicSection typed.dynstr) (hTd : typed.dynamic = some td)
    (iDyn : Nat)
    (hIdx0 : (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym).dynamicIdx = some iDyn)
    (bd : Array DynEntry)
    (hByte0 : (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym).dynamic = some bd)
    (hbN : iDyn < (applyVerneed (applyGnuHash (applySysvHash (applyVersym
              (applyDynamic (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym)
                (ds := typed.dynstr) (some td)) typed.versym) typed.sysvHash) typed.gnuHash) typed.verneed).sections.size)
    (dynN : Array DynEntry)
    (hContentN : ((applyVerneed (applyGnuHash (applySysvHash (applyVersym
              (applyDynamic (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym)
                (ds := typed.dynstr) (some td)) typed.versym) typed.sysvHash) typed.gnuHash) typed.verneed).sections[iDyn]'hbN).content = .dynamic dynN)
    {dsN : StringTable}
    (hDsN : (applyVerneed (applyGnuHash (applySysvHash (applyVersym
              (applyDynamic (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym)
                (ds := typed.dynstr) (some td)) typed.versym) typed.sysvHash) typed.gnuHash) typed.verneed).dynstr = some dsN)
    (hInterpNe : ∀ i, (applyVerneed (applyGnuHash (applySysvHash (applyVersym
              (applyDynamic (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym)
                (ds := typed.dynstr) (some td)) typed.versym) typed.sysvHash) typed.gnuHash) typed.verneed).interpIdx = some i → i ≠ iDyn) :
    toElfFile template (removeRpath typed h)
      = (toElfFile template typed).updateSectionContent iDyn
          (.dynamic (patchDynamicEntries bd td.stripRpath)) := by
  have hKey : ∀ (a b : ElfFile), a.header = b.header → a.phdrs = b.phdrs →
      a.sections = b.sections → a = b := by
    intro a b h1 h2 h3; cases a; cases b; simp_all
  apply hKey
  · rw [toElfFile_header, ElfFile.updateSectionContent_header, toElfFile_header]; rfl
  · rw [toElfFile_phdrs, ElfFile.updateSectionContent_phdrs, toElfFile_phdrs]; rfl
  · -- sections: both equal (innerChain-noop.update iDyn _).sections
    rw [toElfFile_expand, toElfFile_expand]
    obtain ⟨hDsym, hVsym, hSh, hGh, hVn, hIp, _hHdr, _hPhd⟩ := removeRpath_fields typed h
    simp only [removeRpath_dynstr, removeRpath_dynamic, hTd, Option.map_some,
      hDsym, hVsym, hSh, hGh, hVn, hIp]
    rw [innerChain_removeRpath_factor template typed td iDyn hIdx0 bd hByte0 hbN dynN hContentN hDsN hInterpNe]
    exact ElfFile.updateSectionContent_sections_eq_of_sections _ _ iDyn _ rfl

-- applyDynamic (some td) sets content at iDyn to .dynamic (patch bd td).
theorem applyDynamic_content_at_idx (e₀ : ElfFile) {ds : StringSection}
    (td : DynamicSection ds) (iDyn : Nat) (hIdx : e₀.dynamicIdx = some iDyn)
    (bd : Array DynEntry) (hByte : e₀.dynamic = some bd)
    (hLt : iDyn < (applyDynamic e₀ (ds := ds) (some td)).sections.size) :
    ((applyDynamic e₀ (ds := ds) (some td)).sections[iDyn]'hLt).content
      = .dynamic (patchDynamicEntries bd td) := by
  have hEq : applyDynamic e₀ (ds := ds) (some td)
      = e₀.updateSectionContent iDyn (.dynamic (patchDynamicEntries bd td)) := by
    simp only [applyDynamic, hIdx, hByte]
  rw [ElfFile.getElem_content_congr _ _ iDyn hEq hLt]
  exact ElfFile.updateSectionContent_content_self e₀ iDyn _ _

-- applyOpt preserves content at iDyn when its target ≠ iDyn.
theorem applyOpt_content_at_ne {α : Type} (e : ElfFile) (idx? : Option Nat) (val? : Option α)
    (mk : α → SectionContent) (iDyn : Nat)
    (hNe : ∀ i, idx? = some i → i ≠ iDyn)
    (hb : iDyn < e.sections.size) (hb' : iDyn < (applyOpt e idx? val? mk).sections.size) :
    ((applyOpt e idx? val? mk).sections[iDyn]'hb').content
      = (e.sections[iDyn]'hb).content := by
  -- The content at iDyn is bound-irrelevant; reduce to the underlying array fact.
  match hidx : idx?, val? with
  | none, _ => simp_all [applyOpt]
  | some i, none => simp_all [applyOpt]
  | some i, some v =>
      have happly : applyOpt e (some i) (some v) mk = e.updateSectionContent i (mk v) := rfl
      rw [ElfFile.getElem_content_congr _ _ iDyn happly hb']
      exact congrArg Section.content
        (ElfFile.updateSectionContent_getElem_ne e i (mk v) iDyn hb (Ne.symm (hNe i rfl)) _)

-- Generic: a type-based outer-apply (ty ≠ SHT_DYNAMIC) preserves content at the
-- dynamic index (its target ≠ iDyn).  The four per-type applies are wrappers.
theorem applyTypeOpt_content_at {α : Type} (e : ElfFile) (ty : ShType)
    (hTyNe : ty ≠ ShType.SHT_DYNAMIC) (val? : Option α) (mk : α → SectionContent)
    (iDyn : Nat) (hIdx : e.dynamicIdx = some iDyn) (hb : iDyn < e.sections.size)
    (hb' : iDyn < (applyOpt e (e.findUniqueTypeIdx ty) val? mk).sections.size) :
    ((applyOpt e (e.findUniqueTypeIdx ty) val? mk).sections[iDyn]'hb').content
      = (e.sections[iDyn]'hb).content :=
  applyOpt_content_at_ne e (e.findUniqueTypeIdx ty) val? mk iDyn
    (fun i hi => ElfFile.findUniqueTypeIdx_ne_dynamicIdx e ty hTyNe iDyn hIdx i hi) hb hb'

-- Per-apply content preservation at the dynamic index (target ≠ iDyn).
theorem applyVersym_content_at (e : ElfFile) (vs? : Option (Array UInt16)) (iDyn : Nat)
    (hIdx : e.dynamicIdx = some iDyn) (hb : iDyn < e.sections.size)
    (hb' : iDyn < (applyVersym e vs?).sections.size) :
    ((applyVersym e vs?).sections[iDyn]'hb').content = (e.sections[iDyn]'hb).content := by
  unfold applyVersym ElfFile.versymIdx
  exact applyTypeOpt_content_at e ShType.SHT_GNU_VERSYM (by decide) vs? _ iDyn hIdx hb hb'

theorem applySysvHash_content_at (e : ElfFile) (x? : Option SysVHashSection) (iDyn : Nat)
    (hIdx : e.dynamicIdx = some iDyn) (hb : iDyn < e.sections.size)
    (hb' : iDyn < (applySysvHash e x?).sections.size) :
    ((applySysvHash e x?).sections[iDyn]'hb').content = (e.sections[iDyn]'hb).content := by
  unfold applySysvHash ElfFile.sysvHashIdx
  exact applyTypeOpt_content_at e ShType.SHT_HASH (by decide) x? _ iDyn hIdx hb hb'

theorem applyGnuHash_content_at (e : ElfFile) (x? : Option GnuHashSection) (iDyn : Nat)
    (hIdx : e.dynamicIdx = some iDyn) (hb : iDyn < e.sections.size)
    (hb' : iDyn < (applyGnuHash e x?).sections.size) :
    ((applyGnuHash e x?).sections[iDyn]'hb').content = (e.sections[iDyn]'hb).content := by
  unfold applyGnuHash ElfFile.gnuHashIdx
  exact applyTypeOpt_content_at e ShType.SHT_GNU_HASH (by decide) x? _ iDyn hIdx hb hb'

theorem applyVerneed_content_at (e : ElfFile) (x? : Option VerneedSection) (iDyn : Nat)
    (hIdx : e.dynamicIdx = some iDyn) (hb : iDyn < e.sections.size)
    (hb' : iDyn < (applyVerneed e x?).sections.size) :
    ((applyVerneed e x?).sections[iDyn]'hb').content = (e.sections[iDyn]'hb).content := by
  unfold applyVerneed ElfFile.verneedIdx
  exact applyTypeOpt_content_at e ShType.SHT_GNU_VERNEED (by decide) x? _ iDyn hIdx hb hb'

theorem applyInterp_content_at (e : ElfFile) (ip? : Option InterpSection) (iDyn : Nat)
    (hInterpNe : ∀ i, e.interpIdx = some i → i ≠ iDyn) (hb : iDyn < e.sections.size)
    (hb' : iDyn < (applyInterp e ip?).sections.size) :
    ((applyInterp e ip?).sections[iDyn]'hb').content = (e.sections[iDyn]'hb).content :=
  applyOpt_content_at_ne e e.interpIdx ip? _ iDyn hInterpNe hb hb'

theorem toElfFile_content_at_dynamicIdx (template : ElfFile) (typed : ValidElfFile)
    (td : DynamicSection typed.dynstr) (iDyn : Nat)
    (hIdx0 : (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym).dynamicIdx = some iDyn)
    (bd : Array DynEntry)
    (hByte0 : (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym).dynamic = some bd)
    (hInterpNe : ∀ i, (applyVerneed (applyGnuHash (applySysvHash (applyVersym (applyDynamic (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym) (ds := typed.dynstr) (some td)) typed.versym) typed.sysvHash) typed.gnuHash) typed.verneed).interpIdx = some i → i ≠ iDyn)
    (hChain : iDyn < (applyInterp (applyVerneed (applyGnuHash (applySysvHash (applyVersym (applyDynamic (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym) (ds := typed.dynstr) (some td)) typed.versym) typed.sysvHash) typed.gnuHash) typed.verneed) typed.interp).sections.size) :
    ((applyInterp (applyVerneed (applyGnuHash (applySysvHash (applyVersym (applyDynamic (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym) (ds := typed.dynstr) (some td)) typed.versym) typed.sysvHash) typed.gnuHash) typed.verneed) typed.interp).sections[iDyn]'hChain).content = .dynamic (patchDynamicEntries bd td) := by
  have hIdxD : (applyDynamic (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym) (ds := typed.dynstr) (some td)).dynamicIdx = some iDyn :=
    (applyDynamic_dynamicIdx _ (some td) iDyn hIdx0).trans hIdx0
  have hIdxV : (applyVersym (applyDynamic (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym) (ds := typed.dynstr) (some td)) typed.versym).dynamicIdx = some iDyn := by rw [applyVersym_dynamicIdx]; exact hIdxD
  have hIdxS : (applySysvHash (applyVersym (applyDynamic (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym) (ds := typed.dynstr) (some td)) typed.versym) typed.sysvHash).dynamicIdx = some iDyn := by rw [applySysvHash_dynamicIdx]; exact hIdxV
  have hIdxG : (applyGnuHash (applySysvHash (applyVersym (applyDynamic (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym) (ds := typed.dynstr) (some td)) typed.versym) typed.sysvHash) typed.gnuHash).dynamicIdx = some iDyn := by rw [applyGnuHash_dynamicIdx]; exact hIdxS
  have bN : iDyn < (applyVerneed (applyGnuHash (applySysvHash (applyVersym (applyDynamic (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym) (ds := typed.dynstr) (some td)) typed.versym) typed.sysvHash) typed.gnuHash) typed.verneed).sections.size := by simpa using hChain
  have bG : iDyn < (applyGnuHash (applySysvHash (applyVersym (applyDynamic (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym) (ds := typed.dynstr) (some td)) typed.versym) typed.sysvHash) typed.gnuHash).sections.size := by simpa using hChain
  have bS : iDyn < (applySysvHash (applyVersym (applyDynamic (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym) (ds := typed.dynstr) (some td)) typed.versym) typed.sysvHash).sections.size := by simpa using hChain
  have bV : iDyn < (applyVersym (applyDynamic (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym) (ds := typed.dynstr) (some td)) typed.versym).sections.size := by simpa using hChain
  have bD : iDyn < (applyDynamic (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym) (ds := typed.dynstr) (some td)).sections.size := by simpa using hChain
  calc ((applyInterp (applyVerneed (applyGnuHash (applySysvHash (applyVersym (applyDynamic (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym) (ds := typed.dynstr) (some td)) typed.versym) typed.sysvHash) typed.gnuHash) typed.verneed) typed.interp).sections[iDyn]'hChain).content
      = ((applyVerneed (applyGnuHash (applySysvHash (applyVersym (applyDynamic (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym) (ds := typed.dynstr) (some td)) typed.versym) typed.sysvHash) typed.gnuHash) typed.verneed).sections[iDyn]'bN).content :=
        applyInterp_content_at _ typed.interp iDyn hInterpNe bN hChain
    _ = ((applyGnuHash (applySysvHash (applyVersym (applyDynamic (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym) (ds := typed.dynstr) (some td)) typed.versym) typed.sysvHash) typed.gnuHash).sections[iDyn]'bG).content :=
        applyVerneed_content_at _ typed.verneed iDyn hIdxG bG bN
    _ = ((applySysvHash (applyVersym (applyDynamic (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym) (ds := typed.dynstr) (some td)) typed.versym) typed.sysvHash).sections[iDyn]'bS).content :=
        applyGnuHash_content_at _ typed.gnuHash iDyn hIdxS bS bG
    _ = ((applyVersym (applyDynamic (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym) (ds := typed.dynstr) (some td)) typed.versym).sections[iDyn]'bV).content :=
        applySysvHash_content_at _ typed.sysvHash iDyn hIdxV bV bS
    _ = ((applyDynamic (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym) (ds := typed.dynstr) (some td)).sections[iDyn]'bD).content :=
        applyVersym_content_at _ typed.versym iDyn hIdxD bD bV
    _ = .dynamic (patchDynamicEntries bd td) :=
        applyDynamic_content_at_idx _ td iDyn hIdx0 bd hByte0 bD

-- Bundle the per-op facts needed for removeRpath's structural transport.
structure RemoveRpathFactorData (template : ElfFile) (typed : ValidElfFile)
    (h : typed.dynamic.isSome) where
  td : DynamicSection typed.dynstr
  hTd : typed.dynamic = some td
  iDyn : Nat
  hIdx0 : (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym).dynamicIdx = some iDyn
  bd : Array DynEntry
  hByte0 : (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym).dynamic = some bd
  hInterpNe : ∀ i, (applyVerneed (applyGnuHash (applySysvHash (applyVersym
              (applyDynamic (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym)
                (ds := typed.dynstr) (some td)) typed.versym) typed.sysvHash) typed.gnuHash) typed.verneed).interpIdx = some i → i ≠ iDyn
  hbN : iDyn < (applyVerneed (applyGnuHash (applySysvHash (applyVersym
              (applyDynamic (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym)
                (ds := typed.dynstr) (some td)) typed.versym) typed.sysvHash) typed.gnuHash) typed.verneed).sections.size
  dynN : Array DynEntry
  hContentN : ((applyVerneed (applyGnuHash (applySysvHash (applyVersym
              (applyDynamic (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym)
                (ds := typed.dynstr) (some td)) typed.versym) typed.sysvHash) typed.gnuHash) typed.verneed).sections[iDyn]'hbN).content = .dynamic dynN
  dsN : StringTable
  hDsN : (applyVerneed (applyGnuHash (applySysvHash (applyVersym
              (applyDynamic (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym)
                (ds := typed.dynstr) (some td)) typed.versym) typed.sysvHash) typed.gnuHash) typed.verneed).dynstr = some dsN

-- THE TRANSPORT: eo's 6 structural disjointness invariants + section0Null,
-- derived from the no-op base's, via the factoring + content + shrink lemmas.
theorem removeRpath_structural_transport (template : ElfFile) (typed : ValidElfFile)
    (h : typed.dynamic.isSome) (D : RemoveRpathFactorData template typed h)
    (hHP : (toElfFile template typed).headerPhdrDisjoint)
    (hHS : (toElfFile template typed).headerShdrDisjoint)
    (hPS : (toElfFile template typed).phdrShdrDisjoint)
    (hHSec : (toElfFile template typed).headerSectionDisjoint)
    (hPSec : (toElfFile template typed).phdrSectionDisjoint)
    (hShSec : (toElfFile template typed).shdrSectionDisjoint)
    (hS0 : ∀ (h0 : 0 < (toElfFile template typed).sections.size), ((toElfFile template typed).sections[0]'h0).type = ShType.SHT_NULL) :
    (toElfFile template (removeRpath typed h)).headerPhdrDisjoint ∧
    (toElfFile template (removeRpath typed h)).headerShdrDisjoint ∧
    (toElfFile template (removeRpath typed h)).phdrShdrDisjoint ∧
    (toElfFile template (removeRpath typed h)).headerSectionDisjoint ∧
    (toElfFile template (removeRpath typed h)).phdrSectionDisjoint ∧
    (toElfFile template (removeRpath typed h)).shdrSectionDisjoint ∧
    (∀ (h0 : 0 < (toElfFile template (removeRpath typed h)).sections.size),
      ((toElfFile template (removeRpath typed h)).sections[0]'h0).type = ShType.SHT_NULL) := by
  have hFactor := toElfFile_removeRpath_factor template typed h D.td D.hTd D.iDyn D.hIdx0 D.bd D.hByte0 D.hbN D.dynN D.hContentN D.hDsN D.hInterpNe
  have hLtBase : D.iDyn < (toElfFile template typed).sections.size := by
    rw [toElfFile_expand]; simpa using D.hbN
  -- base content at iDyn = .dynamic (patch bd td), via the chain content lemma.
  have hChainBound : D.iDyn < (applyInterp (applyVerneed (applyGnuHash (applySysvHash (applyVersym
        (applyDynamic (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym)
          (ds := typed.dynstr) (some D.td)) typed.versym) typed.sysvHash) typed.gnuHash) typed.verneed) typed.interp).sections.size := by
    simpa using D.hbN
  have hContentChain := toElfFile_content_at_dynamicIdx template typed D.td D.iDyn D.hIdx0 D.bd D.hByte0 D.hInterpNe hChainBound
  have hSecEq : (toElfFile template typed).sections
      = (applyInterp (applyVerneed (applyGnuHash (applySysvHash (applyVersym
          (applyDynamic (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym)
            (ds := typed.dynstr) (some D.td)) typed.versym) typed.sysvHash) typed.gnuHash) typed.verneed) typed.interp).sections := by
    rw [toElfFile_expand, D.hTd]
  have hOld : ((toElfFile template typed).sections[D.iDyn]'hLtBase).content
      = .dynamic (patchDynamicEntries D.bd D.td) := by
    rw [ElfFile.getElem_content_congr_sections (toElfFile template typed) _ D.iDyn hSecEq hLtBase]
    exact hContentChain
  have hShrink : (patchDynamicEntries D.bd D.td.stripRpath).size ≤ (patchDynamicEntries D.bd D.td).size :=
    patchDynamicEntries_stripRpath_size_le D.bd D.td
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hFactor]; exact ElfFile.updateSectionContent_headerPhdrDisjoint _ _ _ hHP
  · rw [hFactor]; exact ElfFile.updateSectionContent_headerShdrDisjoint _ _ _ hHS
  · rw [hFactor]; exact ElfFile.updateSectionContent_phdrShdrDisjoint _ _ _ hPS
  · rw [hFactor]; exact ElfFile.updateSectionContent_headerSectionDisjoint_shrink _ D.iDyn hLtBase _ _ hOld hShrink hHSec
  · rw [hFactor]; exact ElfFile.updateSectionContent_phdrSectionDisjoint_shrink _ D.iDyn hLtBase _ _ hOld hShrink hPSec
  · rw [hFactor]; exact ElfFile.updateSectionContent_shdrSectionDisjoint_shrink _ D.iDyn hLtBase _ _ hOld hShrink hShSec
  · rw [hFactor]; exact ElfFile.updateSectionContent_section0Null _ D.iDyn hLtBase _ _ hOld hS0

/-! ## §E — Capstone: `removeRpath` Tier-D round-trip with DERIVED structural invariants

    Composing `removeRpath_structural_transport` (the 6 structural disjointness
    invariants + section-0-NULL on `eo`, DERIVED from the no-op output's via the
    shrink-monotonicity core) with `tierD_roundtrip_of_eo_facts`.

    The `eo`-structural invariants are NO LONGER hypotheses — they are derived
    from the no-op adapter output `toElfFile template typed` (whose structural
    invariants are parser-derivable for the template, the same precondition any
    op needs) via the factoring.  What remains hypothesized is exactly the
    sanctioned surface: `eo.IsValid` (transported from the typed algebra), the
    phnum bound, the dynstr witness + `< 2^64` fit, the four eo-level
    derived-field facts, and the four `< 2^64` position bounds on the normalized
    form (the "file < 2^64" precondition; the runtime validator guards the
    pathological case). -/

/-- Tier-D byte round-trip for `removeRpath` with the 6 structural disjointness
    invariants + section-0-NULL DERIVED (not hypothesized): they are transported
    from the no-op adapter output `toElfFile template typed` through the
    `.dynamic`-shrink factoring.  §5.1 success criterion (2). -/
theorem toElfFile_removeRpath_tierD_roundtrip_derived (template : ElfFile) (typed : ValidElfFile)
    (h : typed.dynamic.isSome) (D : RemoveRpathFactorData template typed h)
    -- structural invariants of the NO-OP output (template-derived):
    (hHP : (toElfFile template typed).headerPhdrDisjoint)
    (hHS : (toElfFile template typed).headerShdrDisjoint)
    (hPS : (toElfFile template typed).phdrShdrDisjoint)
    (hHSec : (toElfFile template typed).headerSectionDisjoint)
    (hPSec : (toElfFile template typed).phdrSectionDisjoint)
    (hShSec : (toElfFile template typed).shdrSectionDisjoint)
    (hS0noop : ∀ (h0 : 0 < (toElfFile template typed).sections.size),
      ((toElfFile template typed).sections[0]'h0).type = ShType.SHT_NULL)
    -- the sanctioned eo-level remainder (validity + derived fields + < 2^64 bounds):
    (hVal : (toElfFile template (removeRpath typed h)).IsValid)
    (hPhdrFit : ((toElfFile template (removeRpath typed h)).phdrs.size + 1) < UInt16.size)
    {ds : StringTable} (hDs : (toElfFile template (removeRpath typed h)).dynstr = some ds)
    (hFit : ds.bytes.size < UInt64.size)
    (hIdentEo : IdentBytesValid (toElfFile template (removeRpath typed h)))
    (hSizeFitEo : ∀ (i : Nat) (hi : i < (toElfFile template (removeRpath typed h)).sections.size),
      ((toElfFile template (removeRpath typed h)).sections[i]'hi).shdrSize < UInt64.size)
    (hNullEmptyEo : ∀ (i : Nat) (hi : i < (toElfFile template (removeRpath typed h)).sections.size),
      ((toElfFile template (removeRpath typed h)).sections[i]'hi).type = ShType.SHT_NULL →
      ∃ ty hOk bs, ((toElfFile template (removeRpath typed h)).sections[i]'hi).content = .raw ty hOk bs ∧ bs.size = 0)
    (hHdrEntryEo : (toElfFile template (removeRpath typed h)).header.entry.val < UInt64.size)
    (hHdrPhoff : (prepLayoutForEncode (syncDtStrszInFile (toElfFile template (removeRpath typed h)))).header.phoff.val < UInt64.size)
    (hHdrShoff : (prepLayoutForEncode (syncDtStrszInFile (toElfFile template (removeRpath typed h)))).header.shoff.val < UInt64.size)
    (hPhdrFitEn : ∀ (i : Nat) (hi : i < (prepLayoutForEncode (syncDtStrszInFile (toElfFile template (removeRpath typed h)))).phdrs.size),
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (removeRpath typed h)))).phdrs[i]'hi).offset.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (removeRpath typed h)))).phdrs[i]'hi).vaddr.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (removeRpath typed h)))).phdrs[i]'hi).paddr.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (removeRpath typed h)))).phdrs[i]'hi).filesz.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (removeRpath typed h)))).phdrs[i]'hi).memsz.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (removeRpath typed h)))).phdrs[i]'hi).align.val < UInt64.size)
    (hShdrFitEn : ∀ (i : Nat) (hi : i < (prepLayoutForEncode (syncDtStrszInFile (toElfFile template (removeRpath typed h)))).sections.size),
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (removeRpath typed h)))).sections[i]'hi).addr.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (removeRpath typed h)))).sections[i]'hi).offset.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (removeRpath typed h)))).sections[i]'hi).addralign.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (removeRpath typed h)))).sections[i]'hi).entsize.val < UInt64.size) :
    parse (encode (toElfFile template (removeRpath typed h)))
      = .ok ⟨prepLayoutForEncode (syncDtStrszInFile (toElfFile template (removeRpath typed h))),
             prepLayout_syncDtStrsz_preserves_valid _ hVal hPhdrFit hDs⟩ := by
  obtain ⟨hHPeo, hHSeo, hPSeo, hHSeceo, hPSeceo, _hShSeceo, hS0eo⟩ :=
    removeRpath_structural_transport template typed h D hHP hHS hPS hHSec hPSec hShSec hS0noop
  exact tierD_roundtrip_of_eo_facts _ hVal hPhdrFit hDs hFit hS0eo hHPeo hHSeo hPSeo hHSeceo hPSeceo
    hIdentEo hSizeFitEo hNullEmptyEo hHdrEntryEo hHdrPhoff hHdrShoff hPhdrFitEn hShdrFitEn

end Patchelf.Elf.Adapter
