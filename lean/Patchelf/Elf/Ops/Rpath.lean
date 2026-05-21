/-
  modifyRPath — set or remove DT_RPATH / DT_RUNPATH.

  Modal op.  `.set` grows dynstr + sets rpath/runpath slot.
  `.remove` drops both.
-/

import Patchelf.Elf.ObservableCombinators
import Patchelf.Elf.Basic

namespace Patchelf.Elf

open Patchelf.Elf (StringTable)

inductive RpathMode | set | remove
  deriving DecidableEq, Repr

/-- Modify DT_RPATH / DT_RUNPATH. -/
def modifyRPath (e : ValidElfFile) (forceRpath : Bool) (mode : RpathMode)
    (newRpath : String) (_h : e.dynamic.isSome) : ValidElfFile :=
  match mode with
  | .remove => mapDynamicOp e (fun d => d.stripRpath)
  | .set    => growDynstrDynamicOp e newRpath
                 (fun _ off d => d.setRpathTag forceRpath off)

/-! ## Observables -/

theorem modifyRPath_remove_observable
    (e : ValidElfFile) (forceRpath : Bool) (newRpath : String)
    (h : e.dynamic.isSome) :
    ∃ dyn', e.dynamic = some dyn' ∧
      (modifyRPath e forceRpath .remove newRpath h).dynamic = some dyn'.stripRpath :=
  mapDynamicOp_observable e _ h

theorem modifyRPath_set_rpath_observable
    (e : ValidElfFile) (newRpath : String) (h : e.dynamic.isSome)
    (hNoNulls : StringTable.NoNullBytes newRpath.toUTF8) :
    ∃ (dyn' : DynamicSection (modifyRPath e true .set newRpath h).dynstr)
      (off : Fin (modifyRPath e true .set newRpath h).dynstr.size),
      (modifyRPath e true .set newRpath h).dynamic = some dyn' ∧
      (dyn'.rpath = some off ∧ dyn'.runpath = none) ∧
      (modifyRPath e true .set newRpath h).dynstr.lookup off = some newRpath.toUTF8 :=
  growDynstrDynamicOp_observable
    (P := fun d off => d.rpath = some off ∧ d.runpath = none)
    e newRpath _ h hNoNulls
    (fun _ => by unfold DynamicSection.setRpathTag; simp)

theorem modifyRPath_set_runpath_observable
    (e : ValidElfFile) (newRpath : String) (h : e.dynamic.isSome)
    (hNoNulls : StringTable.NoNullBytes newRpath.toUTF8) :
    ∃ (dyn' : DynamicSection (modifyRPath e false .set newRpath h).dynstr)
      (off : Fin (modifyRPath e false .set newRpath h).dynstr.size),
      (modifyRPath e false .set newRpath h).dynamic = some dyn' ∧
      (dyn'.rpath = none ∧ dyn'.runpath = some off) ∧
      (modifyRPath e false .set newRpath h).dynstr.lookup off = some newRpath.toUTF8 :=
  growDynstrDynamicOp_observable
    (P := fun d off => d.rpath = none ∧ d.runpath = some off)
    e newRpath _ h hNoNulls
    (fun _ => by unfold DynamicSection.setRpathTag; simp)

end Patchelf.Elf
