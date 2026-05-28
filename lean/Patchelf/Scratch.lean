import Patchelf.Elf.GrowEOF

open Patchelf.Elf
open Patchelf.Elf.Layout

namespace Patchelf.Elf

@[simp] theorem growEOFWithMainBody_interpIdx
    (pageSize? : Option Nat) (e : ElfFile) (lastIdx : Nat) :
    (growEOFWithMainBody pageSize? e lastIdx).interpIdx = e.interpIdx :=
  growEOFWithMainBody_findIdxByName pageSize? e lastIdx _

theorem growEOFWithMainBody_phdr_type
    (pageSize? : Option Nat) (e : ElfFile) (lastIdx : Nat) (i : Nat)
    (hi : i < (growEOFWithMainBody pageSize? e lastIdx).phdrs.size)
    (hiE : i < e.phdrs.size) :
    ((growEOFWithMainBody pageSize? e lastIdx).phdrs[i]'hi).type
      = (e.phdrs[i]'hiE).type := by
  unfold growEOFWithMainBody
  unfold growEOFWithMainBody at hi
  exact updatePhdrsAfterMove_type (i := i) e.phdrs _ _ _ _ _ _ hi hiE

theorem growEOFWithMainBody_phdr_pt_interp
    (pageSize? : Option Nat) (e : ElfFile) (lastIdx : Nat) (i : Nat)
    (hi : i < (growEOFWithMainBody pageSize? e lastIdx).phdrs.size)
    (hiE : i < e.phdrs.size)
    (hPhT : (e.phdrs[i]'hiE).type = PhType.PT_INTERP)
    {iS : Nat} (hIdx : e.interpIdx = some iS)
    (hS : iS < (growEOFWithMainBody pageSize? e lastIdx).sections.size) :
    ((growEOFWithMainBody pageSize? e lastIdx).phdrs[i]'hi).offset
      = ((growEOFWithMainBody pageSize? e lastIdx).sections[iS]'hS).offset := by
  unfold growEOFWithMainBody
  unfold growEOFWithMainBody at hi hS
  exact updatePhdrsAfterMove_pt_interp (i := i) (iS := iS) e.phdrs _ _ _ _ _ hi hiE hPhT hIdx hS

theorem growEOFWithMainBody_phdr_pt_dynamic
    (pageSize? : Option Nat) (e : ElfFile) (lastIdx : Nat) (i : Nat)
    (hi : i < (growEOFWithMainBody pageSize? e lastIdx).phdrs.size)
    (hiE : i < e.phdrs.size)
    (hPhT : (e.phdrs[i]'hiE).type = PhType.PT_DYNAMIC)
    {iS : Nat} (hIdx : e.dynamicIdx = some iS)
    (hS : iS < (growEOFWithMainBody pageSize? e lastIdx).sections.size) :
    ((growEOFWithMainBody pageSize? e lastIdx).phdrs[i]'hi).offset
      = ((growEOFWithMainBody pageSize? e lastIdx).sections[iS]'hS).offset := by
  unfold growEOFWithMainBody
  unfold growEOFWithMainBody at hi hS
  exact updatePhdrsAfterMove_pt_dynamic (i := i) (iS := iS) e.phdrs _ _ _ _ _ hi hiE hPhT hIdx hS

theorem growEOFWithMainBody_phdr_pt_load
    (pageSize? : Option Nat) (e : ElfFile) (lastIdx : Nat) (i : Nat)
    (hi : i < (growEOFWithMainBody pageSize? e lastIdx).phdrs.size)
    (hiE : i < e.phdrs.size)
    (hPhT : (e.phdrs[i]'hiE).type = PhType.PT_LOAD) :
    ((growEOFWithMainBody pageSize? e lastIdx).phdrs[i]'hi).type = (e.phdrs[i]'hiE).type ∧
    ((growEOFWithMainBody pageSize? e lastIdx).phdrs[i]'hi).offset = (e.phdrs[i]'hiE).offset ∧
    ((growEOFWithMainBody pageSize? e lastIdx).phdrs[i]'hi).vaddr = (e.phdrs[i]'hiE).vaddr ∧
    ((growEOFWithMainBody pageSize? e lastIdx).phdrs[i]'hi).align = (e.phdrs[i]'hiE).align := by
  unfold growEOFWithMainBody
  unfold growEOFWithMainBody at hi
  exact updatePhdrsAfterMove_pt_load_offset_vaddr_align (i := i) e.phdrs _ _ _ _ _ _ hi hiE hPhT

-- Now the main theorem. Mirror layoutForEncoding_preserves_loadable.
theorem growEOFWithMainBody_preserves_loadable
    (pageSize? : Option Nat) (e : ElfFile) (lastIdx : Nat)
    (hLoad : e.IsLoadable)
    (hHeaderPhdr : e.headerPhdrDisjoint)
    (hHeaderSec : e.headerSectionDisjoint)
    (hPhdrSec : e.phdrSectionDisjoint) :
    (growEOFWithMainBody pageSize? e lastIdx).IsLoadable := by
  refine
    { toIsValid := growEOFWithMainBody_preserves_valid pageSize? e lastIdx hLoad.toIsValid
      sections_nonoverlapping := ?_
      pt_interp_agrees := ?_
      pt_dynamic_agrees := ?_
      segment_congruent := ?_ }
  ----------------------------------------
  -- sections_nonoverlapping: from spliceRegionsDisjoint.
  ----------------------------------------
  · exact (growEOFWithMainBody_produces_spliceRegionsDisjoint pageSize? e lastIdx
            hHeaderPhdr hHeaderSec hPhdrSec).sections_disjoint
  ----------------------------------------
  -- ptInterpAgreement
  ----------------------------------------
  · unfold ElfFile.ptInterpAgreement
    rw [growEOFWithMainBody_interpIdx]
    cases hI : e.interpIdx with
    | none => trivial
    | some iS =>
      intro hLt iPh hPh hPhT
      have hPhE : iPh < e.phdrs.size := by
        have := growEOFWithMainBody_phdrs_size pageSize? e lastIdx
        omega
      -- output phdr type = input phdr type = PT_INTERP
      have hPhTE : (e.phdrs[iPh]'hPhE).type = PhType.PT_INTERP := by
        rw [← growEOFWithMainBody_phdr_type pageSize? e lastIdx iPh hPh hPhE]; exact hPhT
      exact growEOFWithMainBody_phdr_pt_interp pageSize? e lastIdx iPh hPh hPhE hPhTE hI hLt
  ----------------------------------------
  -- ptDynamicAgreement
  ----------------------------------------
  · unfold ElfFile.ptDynamicAgreement
    rw [growEOFWithMainBody_dynamicIdx]
    cases hD : e.dynamicIdx with
    | none => trivial
    | some iS =>
      intro hLt iPh hPh hPhT
      have hPhE : iPh < e.phdrs.size := by
        have := growEOFWithMainBody_phdrs_size pageSize? e lastIdx
        omega
      have hPhTE : (e.phdrs[iPh]'hPhE).type = PhType.PT_DYNAMIC := by
        rw [← growEOFWithMainBody_phdr_type pageSize? e lastIdx iPh hPh hPhE]; exact hPhT
      exact growEOFWithMainBody_phdr_pt_dynamic pageSize? e lastIdx iPh hPh hPhE hPhTE hD hLt
  ----------------------------------------
  -- segmentCongruence
  ----------------------------------------
  · unfold ElfFile.segmentCongruence
    intro iPh hPh hPhT
    have hPhE : iPh < e.phdrs.size := by
      have := growEOFWithMainBody_phdrs_size pageSize? e lastIdx
      omega
    have hPhTE : (e.phdrs[iPh]'hPhE).type = PhType.PT_LOAD := by
      rw [← growEOFWithMainBody_phdr_type pageSize? e lastIdx iPh hPh hPhE]; exact hPhT
    obtain ⟨_, hOff, hVad, hAlign⟩ :=
      growEOFWithMainBody_phdr_pt_load pageSize? e lastIdx iPh hPh hPhE hPhTE
    rw [hOff, hVad, hAlign]
    exact hLoad.segment_congruent iPh hPhE hPhTE

end Patchelf.Elf
