/-
  addNeeded.

  Record-literal call to `growDynstrDynamicOp` + `pushNeeded`.
  The observable is 3 lines of tactic — the boilerplate is in
  `ObservableCombinators.lean`.
-/
module

public import Patchelf.Elf.ObservableCombinators
public import Patchelf.Elf.Basic

@[expose] public section

namespace Patchelf.Elf

open Patchelf.Elf (StringTable)

/-- Add a DT_NEEDED entry for `lib`.  Implementation matches the
    `growDynstrDynamicOp` shape so the observable combinator fires. -/
def addNeeded (e : ValidElfFile) (lib : String) (_h : e.dynamic.isSome) :
    ValidElfFile :=
  growDynstrDynamicOp e lib (fun _ off d => d.pushNeeded off)

/-! ## Observable -/

/-- After addNeeded, the FIRST DT_NEEDED points at the new name.  This
    matches C++ patchelf's `addNeeded`, which inserts new entries at
    the top of `.dynamic` (shifting existing DT_NEEDED entries down). -/
theorem addNeeded_observable
    (e : ValidElfFile) (lib : String) (h : e.dynamic.isSome)
    (hNoNulls : StringTable.NoNullBytes lib.toUTF8) :
    ∃ (dyn' : DynamicSection (addNeeded e lib h).dynstr)
      (off : Fin (addNeeded e lib h).dynstr.size)
      (hSize : 0 < dyn'.needed.size),
      (addNeeded e lib h).dynamic = some dyn' ∧
      dyn'.needed[0]'hSize = off ∧
      (addNeeded e lib h).dynstr.lookup off = some lib.toUTF8 := by
  obtain ⟨dyn', off, hDyn', hP, hLookup⟩ :=
    growDynstrDynamicOp_observable
      (P := fun d off =>
        ∃ hSize : 0 < d.needed.size, d.needed[0]'hSize = off)
      e lib (fun _ off d => d.pushNeeded off) h hNoNulls
      (fun _ => by
        refine ⟨?_, ?_⟩
        · show 0 < (#[_] ++ _).size
          rw [Array.size_append]; simp; omega
        · show (#[_] ++ _)[0]'_ = _
          rw [Array.getElem_append_left (by simp)]; rfl)
  obtain ⟨hSize, hElem⟩ := hP
  exact ⟨dyn', off, hSize, hDyn', hElem, hLookup⟩

end Patchelf.Elf
