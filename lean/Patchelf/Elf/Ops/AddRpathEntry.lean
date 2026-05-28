/-
  addRpathEntry — insert a new DT_RPATH / DT_RUNPATH entry.

  Identical to `modifyRPath … .set`; this file just provides the
  alias and re-exports the two observables under the
  `addRpathEntry_*` names (the canonical names referenced by the
  CLI tests).
-/
module

public import Patchelf.Elf.Ops.Rpath

@[expose] public section

namespace Patchelf.Elf

open Patchelf.Elf (StringTable)

/-- Append `newRpath` to `.dynstr`; set one rpath slot, clear the other.
    Defined as `modifyRPath … .set`. -/
def addRpathEntry (e : ValidElfFile) (forceRpath : Bool) (newRpath : String)
    (h : e.dynamic.isSome) : ValidElfFile :=
  modifyRPath e forceRpath .set newRpath h

/-! ## Observables (re-exports of the modifyRPath set-mode lemmas) -/

theorem addRpathEntry_rpath_observable
    (e : ValidElfFile) (newRpath : String) (h : e.dynamic.isSome)
    (hNoNulls : StringTable.NoNullBytes newRpath.toUTF8) :
    ∃ (dyn' : DynamicSection (addRpathEntry e true newRpath h).dynstr)
      (off : Fin (addRpathEntry e true newRpath h).dynstr.size),
      (addRpathEntry e true newRpath h).dynamic = some dyn' ∧
      (dyn'.rpath = some off ∧ dyn'.runpath = none) ∧
      (addRpathEntry e true newRpath h).dynstr.lookup off = some newRpath.toUTF8 :=
  modifyRPath_set_rpath_observable e newRpath h hNoNulls

theorem addRpathEntry_runpath_observable
    (e : ValidElfFile) (newRpath : String) (h : e.dynamic.isSome)
    (hNoNulls : StringTable.NoNullBytes newRpath.toUTF8) :
    ∃ (dyn' : DynamicSection (addRpathEntry e false newRpath h).dynstr)
      (off : Fin (addRpathEntry e false newRpath h).dynstr.size),
      (addRpathEntry e false newRpath h).dynamic = some dyn' ∧
      (dyn'.rpath = none ∧ dyn'.runpath = some off) ∧
      (addRpathEntry e false newRpath h).dynstr.lookup off = some newRpath.toUTF8 :=
  modifyRPath_set_runpath_observable e newRpath h hNoNulls

end Patchelf.Elf
