/-
  removeRpath — drop DT_RPATH and DT_RUNPATH from `.dynamic`.

  Single record update; observable follows from `mapDynamicOp_observable`
  plus rfl on the cleared fields.
-/

import Patchelf.Elf.ObservableCombinators

namespace Patchelf.Elf

/-- Drop DT_RPATH and DT_RUNPATH.  Precondition: `.dynamic` exists. -/
def removeRpath (e : ValidElfFile) (_h : e.dynamic.isSome) : ValidElfFile :=
  mapDynamicOp e (fun d => d.stripRpath)

/-! ## Observables -/

theorem removeRpath_observable
    (e : ValidElfFile) (h : e.dynamic.isSome) :
    ∃ dyn',
      (removeRpath e h).dynamic = some dyn' ∧
      dyn'.rpath = none ∧ dyn'.runpath = none := by
  obtain ⟨dyn, _hDyn, hResult⟩ := mapDynamicOp_observable e (fun d => d.stripRpath) h
  exact ⟨dyn.stripRpath, hResult, rfl, rfl⟩

end Patchelf.Elf
