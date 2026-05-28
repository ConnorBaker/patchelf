import Patchelf.Elf.GrowEOF

open Patchelf.Elf
open Patchelf.Elf.Layout

namespace Patchelf.Elf

-- ===== helper lemmas (already validated, will be transplanted) =====
theorem roundUp_mod_self (n align : Nat) (h : align ≠ 0) :
    roundUp n align % align = 0 := by
  unfold roundUp; rw [if_neg h]; exact Nat.mul_mod_left _ _

theorem array_getElem_at_base_size {α : Type _} (xs : Array α) (x : α) (n : Nat)
    (hn : xs.size = n) (h : n < (xs.push x).size) :
    (xs.push x)[n]'h = x := by
  subst hn; exact Array.getElem_push_eq

theorem freshPtLoad_roundUp_congruence (a b appendedBytes align : Nat) :
    (freshPtLoad (roundUp a align) (roundUp b align) appendedBytes align).align.val ≤ 1 ∨
    (freshPtLoad (roundUp a align) (roundUp b align) appendedBytes align).offset.val
      % (freshPtLoad (roundUp a align) (roundUp b align) appendedBytes align).align.val
    = (freshPtLoad (roundUp a align) (roundUp b align) appendedBytes align).vaddr.val
      % (freshPtLoad (roundUp a align) (roundUp b align) appendedBytes align).align.val := by
  unfold freshPtLoad; simp only []
  by_cases h : align = 0
  · left; omega
  · right; rw [roundUp_mod_self a align h, roundUp_mod_self b align h]

@[simp] theorem growEOFWithFreshPtLoad_interpIdx
    (pageSize? : Option Nat) (e : ElfFile) :
    (growEOFWithFreshPtLoad pageSize? e).interpIdx = e.interpIdx :=
  growEOFWithFreshPtLoad_findIdxByName pageSize? e _

theorem growEOFWithFreshPtLoad_phdr_lt_type
    (pageSize? : Option Nat) (e : ElfFile) (i : Nat)
    (hi : i < (growEOFWithFreshPtLoad pageSize? e).phdrs.size)
    (hiE : i < e.phdrs.size) :
    ((growEOFWithFreshPtLoad pageSize? e).phdrs[i]'hi).type = (e.phdrs[i]'hiE).type := by
  unfold growEOFWithFreshPtLoad; unfold growEOFWithFreshPtLoad at hi
  rw [Array.getElem_push_lt (by rw [updatePhdrsAfterMove_size]; exact hiE)]
  exact updatePhdrsAfterMove_type (i := i) e.phdrs _ _ _ _ _ _ _ hiE

theorem growEOFWithFreshPtLoad_phdr_lt_pt_interp
    (pageSize? : Option Nat) (e : ElfFile) (i : Nat)
    (hi : i < (growEOFWithFreshPtLoad pageSize? e).phdrs.size)
    (hiE : i < e.phdrs.size)
    (hPhT : (e.phdrs[i]'hiE).type = PhType.PT_INTERP)
    {iS : Nat} (hIdx : e.interpIdx = some iS)
    (hS : iS < (growEOFWithFreshPtLoad pageSize? e).sections.size) :
    ((growEOFWithFreshPtLoad pageSize? e).phdrs[i]'hi).offset
      = ((growEOFWithFreshPtLoad pageSize? e).sections[iS]'hS).offset := by
  unfold growEOFWithFreshPtLoad; unfold growEOFWithFreshPtLoad at hi hS
  rw [Array.getElem_push_lt (by rw [updatePhdrsAfterMove_size]; exact hiE)]
  exact updatePhdrsAfterMove_pt_interp (i := i) (iS := iS) e.phdrs _ _ _ _ _ _ hiE hPhT hIdx hS

theorem growEOFWithFreshPtLoad_phdr_lt_pt_dynamic
    (pageSize? : Option Nat) (e : ElfFile) (i : Nat)
    (hi : i < (growEOFWithFreshPtLoad pageSize? e).phdrs.size)
    (hiE : i < e.phdrs.size)
    (hPhT : (e.phdrs[i]'hiE).type = PhType.PT_DYNAMIC)
    {iS : Nat} (hIdx : e.dynamicIdx = some iS)
    (hS : iS < (growEOFWithFreshPtLoad pageSize? e).sections.size) :
    ((growEOFWithFreshPtLoad pageSize? e).phdrs[i]'hi).offset
      = ((growEOFWithFreshPtLoad pageSize? e).sections[iS]'hS).offset := by
  unfold growEOFWithFreshPtLoad; unfold growEOFWithFreshPtLoad at hi hS
  rw [Array.getElem_push_lt (by rw [updatePhdrsAfterMove_size]; exact hiE)]
  exact updatePhdrsAfterMove_pt_dynamic (i := i) (iS := iS) e.phdrs _ _ _ _ _ _ hiE hPhT hIdx hS

theorem growEOFWithFreshPtLoad_phdr_lt_pt_load
    (pageSize? : Option Nat) (e : ElfFile) (i : Nat)
    (hi : i < (growEOFWithFreshPtLoad pageSize? e).phdrs.size)
    (hiE : i < e.phdrs.size)
    (hPhT : (e.phdrs[i]'hiE).type = PhType.PT_LOAD) :
    ((growEOFWithFreshPtLoad pageSize? e).phdrs[i]'hi).type = (e.phdrs[i]'hiE).type ∧
    ((growEOFWithFreshPtLoad pageSize? e).phdrs[i]'hi).offset = (e.phdrs[i]'hiE).offset ∧
    ((growEOFWithFreshPtLoad pageSize? e).phdrs[i]'hi).vaddr = (e.phdrs[i]'hiE).vaddr ∧
    ((growEOFWithFreshPtLoad pageSize? e).phdrs[i]'hi).align = (e.phdrs[i]'hiE).align := by
  unfold growEOFWithFreshPtLoad; unfold growEOFWithFreshPtLoad at hi
  rw [Array.getElem_push_lt (by rw [updatePhdrsAfterMove_size]; exact hiE)]
  exact updatePhdrsAfterMove_pt_load_offset_vaddr_align (i := i) e.phdrs _ _ _ _ _ _ _ hiE hPhT

theorem growEOFWithFreshPtLoad_phdr_fresh_type
    (pageSize? : Option Nat) (e : ElfFile) (i : Nat)
    (hi : i < (growEOFWithFreshPtLoad pageSize? e).phdrs.size)
    (hiNot : ¬ i < e.phdrs.size) :
    ((growEOFWithFreshPtLoad pageSize? e).phdrs[i]'hi).type = PhType.PT_LOAD := by
  have hiSize : i = e.phdrs.size := by
    have := growEOFWithFreshPtLoad_phdrs_size pageSize? e; omega
  subst hiSize
  unfold growEOFWithFreshPtLoad
  rw [array_getElem_at_base_size _ _ _ (updatePhdrsAfterMove_size _ _ _ _ _ _ _)]; rfl

theorem growEOFWithFreshPtLoad_phdr_fresh_congruence
    (pageSize? : Option Nat) (e : ElfFile) (i : Nat)
    (hi : i < (growEOFWithFreshPtLoad pageSize? e).phdrs.size)
    (hiNot : ¬ i < e.phdrs.size) :
    ((growEOFWithFreshPtLoad pageSize? e).phdrs[i]'hi).align.val ≤ 1 ∨
    ((growEOFWithFreshPtLoad pageSize? e).phdrs[i]'hi).offset.val
      % ((growEOFWithFreshPtLoad pageSize? e).phdrs[i]'hi).align.val
    = ((growEOFWithFreshPtLoad pageSize? e).phdrs[i]'hi).vaddr.val
      % ((growEOFWithFreshPtLoad pageSize? e).phdrs[i]'hi).align.val := by
  have hiSize : i = e.phdrs.size := by
    have := growEOFWithFreshPtLoad_phdrs_size pageSize? e; omega
  subst hiSize
  unfold growEOFWithFreshPtLoad
  rw [array_getElem_at_base_size _ _ _ (updatePhdrsAfterMove_size _ _ _ _ _ _ _)]
  exact freshPtLoad_roundUp_congruence _ _ _ _

-- ===== main theorem =====
theorem growEOFWithFreshPtLoad_preserves_loadable
    (pageSize? : Option Nat) (e : ElfFile)
    (hLoad : e.IsLoadable)
    (hPhdrFit : (e.phdrs.size + 1) < UInt16.size)
    (hCan : canAddFreshPtLoad e = true)
    (hHeaderSec : e.headerSectionDisjoint) :
    (growEOFWithFreshPtLoad pageSize? e).IsLoadable := by
  refine
    { toIsValid := growEOFWithFreshPtLoad_preserves_valid pageSize? e hLoad.toIsValid hPhdrFit
      sections_nonoverlapping := ?_
      pt_interp_agrees := ?_
      pt_dynamic_agrees := ?_
      segment_congruent := ?_ }
  · exact (growEOFWithFreshPtLoad_produces_spliceRegionsDisjoint pageSize? e hCan
            hHeaderSec).sections_disjoint
  · unfold ElfFile.ptInterpAgreement
    rw [growEOFWithFreshPtLoad_interpIdx]
    cases hI : e.interpIdx with
    | none => trivial
    | some iS =>
      intro hLt iPh hPh hPhT
      by_cases hiE : iPh < e.phdrs.size
      · have hPhTE : (e.phdrs[iPh]'hiE).type = PhType.PT_INTERP := by
          rw [← growEOFWithFreshPtLoad_phdr_lt_type pageSize? e iPh hPh hiE]; exact hPhT
        exact growEOFWithFreshPtLoad_phdr_lt_pt_interp pageSize? e iPh hPh hiE hPhTE hI hLt
      · -- fresh phdr is PT_LOAD ≠ PT_INTERP — contradiction.
        exfalso
        rw [growEOFWithFreshPtLoad_phdr_fresh_type pageSize? e iPh hPh hiE] at hPhT
        exact absurd hPhT (by decide)
  · unfold ElfFile.ptDynamicAgreement
    rw [growEOFWithFreshPtLoad_dynamicIdx]
    cases hD : e.dynamicIdx with
    | none => trivial
    | some iS =>
      intro hLt iPh hPh hPhT
      by_cases hiE : iPh < e.phdrs.size
      · have hPhTE : (e.phdrs[iPh]'hiE).type = PhType.PT_DYNAMIC := by
          rw [← growEOFWithFreshPtLoad_phdr_lt_type pageSize? e iPh hPh hiE]; exact hPhT
        exact growEOFWithFreshPtLoad_phdr_lt_pt_dynamic pageSize? e iPh hPh hiE hPhTE hD hLt
      · exfalso
        rw [growEOFWithFreshPtLoad_phdr_fresh_type pageSize? e iPh hPh hiE] at hPhT
        exact absurd hPhT (by decide)
  · unfold ElfFile.segmentCongruence
    intro iPh hPh hPhT
    by_cases hiE : iPh < e.phdrs.size
    · have hPhTE : (e.phdrs[iPh]'hiE).type = PhType.PT_LOAD := by
        rw [← growEOFWithFreshPtLoad_phdr_lt_type pageSize? e iPh hPh hiE]; exact hPhT
      obtain ⟨_, hOff, hVad, hAlign⟩ :=
        growEOFWithFreshPtLoad_phdr_lt_pt_load pageSize? e iPh hPh hiE hPhTE
      rw [hOff, hVad, hAlign]
      exact hLoad.segment_congruent iPh hiE hPhTE
    · exact growEOFWithFreshPtLoad_phdr_fresh_congruence pageSize? e iPh hPh hiE

end Patchelf.Elf
