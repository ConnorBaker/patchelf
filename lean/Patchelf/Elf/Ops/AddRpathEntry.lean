/-
  addRpathEntry — insert a new DT_RPATH / DT_RUNPATH entry.

  Semantics (matching patchelf.cc:1667 `rpAdd`):
    1. Grow `.dynstr` with `newRpath`.
    2. Set DT_RPATH (if `forceRpath`) or DT_RUNPATH to the new offset,
       clearing the other slot.
-/
module

public import Patchelf.Elf.ObservableCombinators
public import Patchelf.Elf.Basic

@[expose] public section

namespace Patchelf.Elf

open Patchelf.Elf (StringTable)

/-- Append `newRpath` to `.dynstr`; set one rpath slot, clear the other. -/
def addRpathEntry (e : ValidElfFile) (forceRpath : Bool) (newRpath : String)
    (_h : e.dynamic.isSome) : ValidElfFile :=
  growDynstrDynamicOp e newRpath (fun _ off d => d.setRpathTag forceRpath off)

/-! ## Observables -/

theorem addRpathEntry_rpath_observable
    (e : ValidElfFile) (newRpath : String) (h : e.dynamic.isSome)
    (hNoNulls : StringTable.NoNullBytes newRpath.toUTF8) :
    ∃ (dyn' : DynamicSection (addRpathEntry e true newRpath h).dynstr)
      (off : Fin (addRpathEntry e true newRpath h).dynstr.size),
      (addRpathEntry e true newRpath h).dynamic = some dyn' ∧
      (dyn'.rpath = some off ∧ dyn'.runpath = none) ∧
      (addRpathEntry e true newRpath h).dynstr.lookup off = some newRpath.toUTF8 :=
  growDynstrDynamicOp_observable
    (P := fun d off => d.rpath = some off ∧ d.runpath = none)
    e newRpath _ h hNoNulls
    (fun _ => by unfold DynamicSection.setRpathTag; simp)

theorem addRpathEntry_runpath_observable
    (e : ValidElfFile) (newRpath : String) (h : e.dynamic.isSome)
    (hNoNulls : StringTable.NoNullBytes newRpath.toUTF8) :
    ∃ (dyn' : DynamicSection (addRpathEntry e false newRpath h).dynstr)
      (off : Fin (addRpathEntry e false newRpath h).dynstr.size),
      (addRpathEntry e false newRpath h).dynamic = some dyn' ∧
      (dyn'.rpath = none ∧ dyn'.runpath = some off) ∧
      (addRpathEntry e false newRpath h).dynstr.lookup off = some newRpath.toUTF8 :=
  growDynstrDynamicOp_observable
    (P := fun d off => d.rpath = none ∧ d.runpath = some off)
    e newRpath _ h hNoNulls
    (fun _ => by unfold DynamicSection.setRpathTag; simp)

end Patchelf.Elf
