module

public import Patchelf.Elf.Encoder

@[expose] public section

namespace Patchelf.Elf

open Patchelf.Elf.Layout
open Layout

-- prepLayoutForEncode preserves IsValid (compose growEOFWith + syncDtAddrTagsInFile).
theorem prepLayoutForEncode_preserves_valid (e : ElfFile)
    (hVal : e.IsValid) (hPhdrFit : (e.phdrs.size + 1) < UInt16.size)
    {ds : StringTable} (hDs : e.dynstr = some ds) :
    (prepLayoutForEncode e).IsValid := by
  unfold prepLayoutForEncode prepLayoutForEncodeWith
  by_cases hLay : layoutAlreadyValid e = true
  · simp only [hLay, ↓reduceIte]; exact hVal
  · simp only [hLay, Bool.false_eq_true, ↓reduceIte]
    have hGrow : (growEOFWith none e).IsValid := growEOFWith_preserves_valid none e hVal hPhdrFit
    have hGrowDs : (growEOFWith none e).dynstr = some ds := by rw [growEOFWith_dynstr]; exact hDs
    exact syncDtAddrTagsInFile_preserves_valid _ hGrow hGrowDs

-- Full pre-encode pipeline preserves IsValid (mirrors prepLayout_syncDtStrsz_preserves_loadable).
theorem prepLayout_syncDtStrsz_preserves_valid (e : ElfFile)
    (hVal : e.IsValid) (hPhdrFit : (e.phdrs.size + 1) < UInt16.size)
    {ds : StringTable} (hDs : e.dynstr = some ds) :
    (prepLayoutForEncode (syncDtStrszInFile e)).IsValid := by
  have hVal' := syncDtStrszInFile_preserves_valid e hVal
  have hDs' : (syncDtStrszInFile e).dynstr = some ds := by
    rw [syncDtStrszInFile_dynstr_eq]; exact hDs
  exact prepLayoutForEncode_preserves_valid (syncDtStrszInFile e) hVal'
    (by rw [syncDtStrszInFile_phdrs]; exact hPhdrFit) hDs'

end Patchelf.Elf
