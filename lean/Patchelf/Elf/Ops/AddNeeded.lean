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

/-- After addNeeded, the last DT_NEEDED points at the new name. -/
theorem addNeeded_observable
    (e : ValidElfFile) (lib : String) (h : e.dynamic.isSome)
    (hNoNulls : StringTable.NoNullBytes lib.toUTF8) :
    ∃ (dyn' : DynamicSection (addNeeded e lib h).dynstr)
      (off : Fin (addNeeded e lib h).dynstr.size),
      (addNeeded e lib h).dynamic = some dyn' ∧
      dyn'.needed.back? = some off ∧
      (addNeeded e lib h).dynstr.lookup off = some lib.toUTF8 :=
  growDynstrDynamicOp_observable
    (P := fun d off => d.needed.back? = some off)
    e lib _ h hNoNulls
    (fun _ => by simp)

end Patchelf.Elf
