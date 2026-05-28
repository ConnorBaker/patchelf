import Patchelf.Elf.GrowEOF

open Patchelf.Elf
open Patchelf.Elf.Layout

namespace Patchelf.Elf

-- ===== retargetPtPhdr + composed lemmas (validated; will transplant) =====
@[simp] theorem retargetPtPhdr_size (phdrs : Array Patchelf.Elf.ProgramHeader)
    (a b c : Nat) : (retargetPtPhdr phdrs a b c).size = phdrs.size := by
  unfold retargetPtPhdr; exact Array.size_map

theorem retargetPtPhdr_type (phdrs : Array Patchelf.Elf.ProgramHeader)
    (a b c : Nat) (i : Nat)
    (hi : i < (retargetPtPhdr phdrs a b c).size) (hiE : i < phdrs.size) :
    ((retargetPtPhdr phdrs a b c)[i]'hi).type = (phdrs[i]'hiE).type := by
  unfold retargetPtPhdr; rw [Array.getElem_map]; split <;> rfl

theorem retargetPtPhdr_of_not_pt_phdr (phdrs : Array Patchelf.Elf.ProgramHeader)
    (a b c : Nat) (i : Nat)
    (hi : i < (retargetPtPhdr phdrs a b c).size) (hiE : i < phdrs.size)
    (hNotPhdr : (phdrs[i]'hiE).type ≠ PhType.PT_PHDR) :
    (retargetPtPhdr phdrs a b c)[i]'hi = phdrs[i]'hiE := by
  unfold retargetPtPhdr; rw [Array.getElem_map]; rw [if_neg hNotPhdr]

private theorem reloc_inner_size (phdrs : Array Patchelf.Elf.ProgramHeader)
    (lastIdx? : Option Nat) (f m : Nat) (ii di : Option Nat) (ns : Array Section)
    (a b c : Nat) :
    (retargetPtPhdr (updatePhdrsAfterMove phdrs lastIdx? f m ii di ns) a b c).size
      = phdrs.size := by
  rw [retargetPtPhdr_size, updatePhdrsAfterMove_size]

theorem retarget_update_type
    (phdrs : Array Patchelf.Elf.ProgramHeader)
    (lastIdx? : Option Nat) (f m : Nat) (ii di : Option Nat) (ns : Array Section)
    (a b c : Nat) (i : Nat)
    (hi : i < (retargetPtPhdr (updatePhdrsAfterMove phdrs lastIdx? f m ii di ns) a b c).size)
    (hiE : i < phdrs.size) :
    ((retargetPtPhdr (updatePhdrsAfterMove phdrs lastIdx? f m ii di ns) a b c)[i]'hi).type
      = (phdrs[i]'hiE).type := by
  have hiU : i < (updatePhdrsAfterMove phdrs lastIdx? f m ii di ns).size := by
    rw [updatePhdrsAfterMove_size]; exact hiE
  rw [retargetPtPhdr_type _ _ _ _ i hi hiU]
  exact updatePhdrsAfterMove_type (i := i) phdrs _ _ _ _ _ _ hiU hiE

theorem retarget_update_pt_interp
    (phdrs : Array Patchelf.Elf.ProgramHeader)
    (lastIdx? : Option Nat) (f m : Nat) {ii : Option Nat} (di : Option Nat) (ns : Array Section)
    (a b c : Nat) (i : Nat)
    (hi : i < (retargetPtPhdr (updatePhdrsAfterMove phdrs lastIdx? f m ii di ns) a b c).size)
    (hiE : i < phdrs.size)
    (hPhT : (phdrs[i]'hiE).type = PhType.PT_INTERP)
    {iS : Nat} (hIdx : ii = some iS) (hS : iS < ns.size) :
    ((retargetPtPhdr (updatePhdrsAfterMove phdrs lastIdx? f m ii di ns) a b c)[i]'hi).offset
      = (ns[iS]'hS).offset := by
  have hiU : i < (updatePhdrsAfterMove phdrs lastIdx? f m ii di ns).size := by
    rw [updatePhdrsAfterMove_size]; exact hiE
  have hUType : ((updatePhdrsAfterMove phdrs lastIdx? f m ii di ns)[i]'hiU).type
      = PhType.PT_INTERP := by
    rw [updatePhdrsAfterMove_type (i := i) phdrs _ _ _ _ _ _ hiU hiE]; exact hPhT
  have hNotPhdr : ((updatePhdrsAfterMove phdrs lastIdx? f m ii di ns)[i]'hiU).type
      ≠ PhType.PT_PHDR := by rw [hUType]; decide
  rw [retargetPtPhdr_of_not_pt_phdr _ _ _ _ i hi hiU hNotPhdr]
  exact updatePhdrsAfterMove_pt_interp (i := i) (iS := iS) phdrs _ _ _ _ _ hiU hiE hPhT hIdx hS

theorem retarget_update_pt_dynamic
    (phdrs : Array Patchelf.Elf.ProgramHeader)
    (lastIdx? : Option Nat) (f m : Nat) (ii : Option Nat) {di : Option Nat} (ns : Array Section)
    (a b c : Nat) (i : Nat)
    (hi : i < (retargetPtPhdr (updatePhdrsAfterMove phdrs lastIdx? f m ii di ns) a b c).size)
    (hiE : i < phdrs.size)
    (hPhT : (phdrs[i]'hiE).type = PhType.PT_DYNAMIC)
    {iS : Nat} (hIdx : di = some iS) (hS : iS < ns.size) :
    ((retargetPtPhdr (updatePhdrsAfterMove phdrs lastIdx? f m ii di ns) a b c)[i]'hi).offset
      = (ns[iS]'hS).offset := by
  have hiU : i < (updatePhdrsAfterMove phdrs lastIdx? f m ii di ns).size := by
    rw [updatePhdrsAfterMove_size]; exact hiE
  have hUType : ((updatePhdrsAfterMove phdrs lastIdx? f m ii di ns)[i]'hiU).type
      = PhType.PT_DYNAMIC := by
    rw [updatePhdrsAfterMove_type (i := i) phdrs _ _ _ _ _ _ hiU hiE]; exact hPhT
  have hNotPhdr : ((updatePhdrsAfterMove phdrs lastIdx? f m ii di ns)[i]'hiU).type
      ≠ PhType.PT_PHDR := by rw [hUType]; decide
  rw [retargetPtPhdr_of_not_pt_phdr _ _ _ _ i hi hiU hNotPhdr]
  exact updatePhdrsAfterMove_pt_dynamic (i := i) (iS := iS) phdrs _ _ _ _ _ hiU hiE hPhT hIdx hS

theorem retarget_update_pt_load
    (phdrs : Array Patchelf.Elf.ProgramHeader)
    (lastIdx? : Option Nat) (f m : Nat) (ii di : Option Nat) (ns : Array Section)
    (a b c : Nat) (i : Nat)
    (hi : i < (retargetPtPhdr (updatePhdrsAfterMove phdrs lastIdx? f m ii di ns) a b c).size)
    (hiE : i < phdrs.size)
    (hPhT : (phdrs[i]'hiE).type = PhType.PT_LOAD) :
    ((retargetPtPhdr (updatePhdrsAfterMove phdrs lastIdx? f m ii di ns) a b c)[i]'hi).type
      = (phdrs[i]'hiE).type ∧
    ((retargetPtPhdr (updatePhdrsAfterMove phdrs lastIdx? f m ii di ns) a b c)[i]'hi).offset
      = (phdrs[i]'hiE).offset ∧
    ((retargetPtPhdr (updatePhdrsAfterMove phdrs lastIdx? f m ii di ns) a b c)[i]'hi).vaddr
      = (phdrs[i]'hiE).vaddr ∧
    ((retargetPtPhdr (updatePhdrsAfterMove phdrs lastIdx? f m ii di ns) a b c)[i]'hi).align
      = (phdrs[i]'hiE).align := by
  have hiU : i < (updatePhdrsAfterMove phdrs lastIdx? f m ii di ns).size := by
    rw [updatePhdrsAfterMove_size]; exact hiE
  have hUType : ((updatePhdrsAfterMove phdrs lastIdx? f m ii di ns)[i]'hiU).type
      = PhType.PT_LOAD := by
    rw [updatePhdrsAfterMove_type (i := i) phdrs _ _ _ _ _ _ hiU hiE]; exact hPhT
  have hNotPhdr : ((updatePhdrsAfterMove phdrs lastIdx? f m ii di ns)[i]'hiU).type
      ≠ PhType.PT_PHDR := by rw [hUType]; decide
  rw [retargetPtPhdr_of_not_pt_phdr _ _ _ _ i hi hiU hNotPhdr]
  exact updatePhdrsAfterMove_pt_load_offset_vaddr_align (i := i) phdrs _ _ _ _ _ _ hiU hiE hPhT

-- ===== Reloc branch =====
@[simp] theorem growEOFWithFreshPtLoadReloc_interpIdx
    (pageSize? : Option Nat) (e : ElfFile) :
    (growEOFWithFreshPtLoadReloc pageSize? e).interpIdx = e.interpIdx :=
  growEOFWithFreshPtLoadReloc_findIdxByName pageSize? e _

theorem growEOFWithFreshPtLoadReloc_phdr_lt_type
    (pageSize? : Option Nat) (e : ElfFile) (i : Nat)
    (hi : i < (growEOFWithFreshPtLoadReloc pageSize? e).phdrs.size)
    (hiE : i < e.phdrs.size) :
    ((growEOFWithFreshPtLoadReloc pageSize? e).phdrs[i]'hi).type = (e.phdrs[i]'hiE).type := by
  unfold growEOFWithFreshPtLoadReloc; unfold growEOFWithFreshPtLoadReloc at hi
  rw [Array.getElem_push_lt (by rw [reloc_inner_size]; exact hiE)]
  exact retarget_update_type e.phdrs _ _ _ _ _ _ _ _ _ i _ hiE

theorem growEOFWithFreshPtLoadReloc_phdr_lt_pt_interp
    (pageSize? : Option Nat) (e : ElfFile) (i : Nat)
    (hi : i < (growEOFWithFreshPtLoadReloc pageSize? e).phdrs.size)
    (hiE : i < e.phdrs.size)
    (hPhT : (e.phdrs[i]'hiE).type = PhType.PT_INTERP)
    {iS : Nat} (hIdx : e.interpIdx = some iS)
    (hS : iS < (growEOFWithFreshPtLoadReloc pageSize? e).sections.size) :
    ((growEOFWithFreshPtLoadReloc pageSize? e).phdrs[i]'hi).offset
      = ((growEOFWithFreshPtLoadReloc pageSize? e).sections[iS]'hS).offset := by
  unfold growEOFWithFreshPtLoadReloc; unfold growEOFWithFreshPtLoadReloc at hi hS
  rw [Array.getElem_push_lt (by rw [reloc_inner_size]; exact hiE)]
  exact retarget_update_pt_interp (i := i) e.phdrs _ _ _ _ _ _ _ _ _ hiE hPhT hIdx hS

theorem growEOFWithFreshPtLoadReloc_phdr_lt_pt_dynamic
    (pageSize? : Option Nat) (e : ElfFile) (i : Nat)
    (hi : i < (growEOFWithFreshPtLoadReloc pageSize? e).phdrs.size)
    (hiE : i < e.phdrs.size)
    (hPhT : (e.phdrs[i]'hiE).type = PhType.PT_DYNAMIC)
    {iS : Nat} (hIdx : e.dynamicIdx = some iS)
    (hS : iS < (growEOFWithFreshPtLoadReloc pageSize? e).sections.size) :
    ((growEOFWithFreshPtLoadReloc pageSize? e).phdrs[i]'hi).offset
      = ((growEOFWithFreshPtLoadReloc pageSize? e).sections[iS]'hS).offset := by
  unfold growEOFWithFreshPtLoadReloc; unfold growEOFWithFreshPtLoadReloc at hi hS
  rw [Array.getElem_push_lt (by rw [reloc_inner_size]; exact hiE)]
  exact retarget_update_pt_dynamic (i := i) e.phdrs _ _ _ _ _ _ _ _ _ hiE hPhT hIdx hS

theorem growEOFWithFreshPtLoadReloc_phdr_lt_pt_load
    (pageSize? : Option Nat) (e : ElfFile) (i : Nat)
    (hi : i < (growEOFWithFreshPtLoadReloc pageSize? e).phdrs.size)
    (hiE : i < e.phdrs.size)
    (hPhT : (e.phdrs[i]'hiE).type = PhType.PT_LOAD) :
    ((growEOFWithFreshPtLoadReloc pageSize? e).phdrs[i]'hi).type = (e.phdrs[i]'hiE).type ∧
    ((growEOFWithFreshPtLoadReloc pageSize? e).phdrs[i]'hi).offset = (e.phdrs[i]'hiE).offset ∧
    ((growEOFWithFreshPtLoadReloc pageSize? e).phdrs[i]'hi).vaddr = (e.phdrs[i]'hiE).vaddr ∧
    ((growEOFWithFreshPtLoadReloc pageSize? e).phdrs[i]'hi).align = (e.phdrs[i]'hiE).align := by
  unfold growEOFWithFreshPtLoadReloc; unfold growEOFWithFreshPtLoadReloc at hi
  rw [Array.getElem_push_lt (by rw [reloc_inner_size]; exact hiE)]
  exact retarget_update_pt_load e.phdrs _ _ _ _ _ _ _ _ _ i _ hiE hPhT

theorem growEOFWithFreshPtLoadReloc_phdr_fresh_type
    (pageSize? : Option Nat) (e : ElfFile) (i : Nat)
    (hi : i < (growEOFWithFreshPtLoadReloc pageSize? e).phdrs.size)
    (hiNot : ¬ i < e.phdrs.size) :
    ((growEOFWithFreshPtLoadReloc pageSize? e).phdrs[i]'hi).type = PhType.PT_LOAD := by
  have hiSize : i = e.phdrs.size := by
    have := growEOFWithFreshPtLoadReloc_phdrs_size pageSize? e; omega
  subst hiSize
  unfold growEOFWithFreshPtLoadReloc
  rw [array_getElem_at_base_size _ _ _ (reloc_inner_size _ _ _ _ _ _ _ _ _ _)]; rfl

theorem growEOFWithFreshPtLoadReloc_phdr_fresh_congruence
    (pageSize? : Option Nat) (e : ElfFile) (i : Nat)
    (hi : i < (growEOFWithFreshPtLoadReloc pageSize? e).phdrs.size)
    (hiNot : ¬ i < e.phdrs.size) :
    ((growEOFWithFreshPtLoadReloc pageSize? e).phdrs[i]'hi).align.val ≤ 1 ∨
    ((growEOFWithFreshPtLoadReloc pageSize? e).phdrs[i]'hi).offset.val
      % ((growEOFWithFreshPtLoadReloc pageSize? e).phdrs[i]'hi).align.val
    = ((growEOFWithFreshPtLoadReloc pageSize? e).phdrs[i]'hi).vaddr.val
      % ((growEOFWithFreshPtLoadReloc pageSize? e).phdrs[i]'hi).align.val := by
  have hiSize : i = e.phdrs.size := by
    have := growEOFWithFreshPtLoadReloc_phdrs_size pageSize? e; omega
  subst hiSize
  unfold growEOFWithFreshPtLoadReloc
  rw [array_getElem_at_base_size _ _ _ (reloc_inner_size _ _ _ _ _ _ _ _ _ _)]
  exact freshPtLoad_roundUp_congruence _ _ _ _

theorem growEOFWithFreshPtLoadReloc_preserves_loadable
    (pageSize? : Option Nat) (e : ElfFile)
    (hLoad : e.IsLoadable)
    (hPhdrFit : (e.phdrs.size + 1) < UInt16.size)
    (hHeaderSec : e.headerSectionDisjoint) :
    (growEOFWithFreshPtLoadReloc pageSize? e).IsLoadable := by
  refine
    { toIsValid := growEOFWithFreshPtLoadReloc_preserves_valid pageSize? e hLoad.toIsValid hPhdrFit
      sections_nonoverlapping := ?_
      pt_interp_agrees := ?_
      pt_dynamic_agrees := ?_
      segment_congruent := ?_ }
  · exact (growEOFWithFreshPtLoadReloc_produces_spliceRegionsDisjoint pageSize? e
            hHeaderSec).sections_disjoint
  · unfold ElfFile.ptInterpAgreement
    rw [growEOFWithFreshPtLoadReloc_interpIdx]
    cases hI : e.interpIdx with
    | none => trivial
    | some iS =>
      intro hLt iPh hPh hPhT
      by_cases hiE : iPh < e.phdrs.size
      · have hPhTE : (e.phdrs[iPh]'hiE).type = PhType.PT_INTERP := by
          rw [← growEOFWithFreshPtLoadReloc_phdr_lt_type pageSize? e iPh hPh hiE]; exact hPhT
        exact growEOFWithFreshPtLoadReloc_phdr_lt_pt_interp pageSize? e iPh hPh hiE hPhTE hI hLt
      · exfalso
        rw [growEOFWithFreshPtLoadReloc_phdr_fresh_type pageSize? e iPh hPh hiE] at hPhT
        exact absurd hPhT (by decide)
  · unfold ElfFile.ptDynamicAgreement
    rw [growEOFWithFreshPtLoadReloc_dynamicIdx]
    cases hD : e.dynamicIdx with
    | none => trivial
    | some iS =>
      intro hLt iPh hPh hPhT
      by_cases hiE : iPh < e.phdrs.size
      · have hPhTE : (e.phdrs[iPh]'hiE).type = PhType.PT_DYNAMIC := by
          rw [← growEOFWithFreshPtLoadReloc_phdr_lt_type pageSize? e iPh hPh hiE]; exact hPhT
        exact growEOFWithFreshPtLoadReloc_phdr_lt_pt_dynamic pageSize? e iPh hPh hiE hPhTE hD hLt
      · exfalso
        rw [growEOFWithFreshPtLoadReloc_phdr_fresh_type pageSize? e iPh hPh hiE] at hPhT
        exact absurd hPhT (by decide)
  · unfold ElfFile.segmentCongruence
    intro iPh hPh hPhT
    by_cases hiE : iPh < e.phdrs.size
    · have hPhTE : (e.phdrs[iPh]'hiE).type = PhType.PT_LOAD := by
        rw [← growEOFWithFreshPtLoadReloc_phdr_lt_type pageSize? e iPh hPh hiE]; exact hPhT
      obtain ⟨_, hOff, hVad, hAlign⟩ :=
        growEOFWithFreshPtLoadReloc_phdr_lt_pt_load pageSize? e iPh hPh hiE hPhTE
      rw [hOff, hVad, hAlign]
      exact hLoad.segment_congruent iPh hiE hPhTE
    · exact growEOFWithFreshPtLoadReloc_phdr_fresh_congruence pageSize? e iPh hPh hiE

end Patchelf.Elf
