/-
  removeNeeded — drop DT_NEEDED entries whose library name matches.

  Op is `mapDynamicOp` with `filterNeededBy`; observable is a
  2-line corollary of `filterNeededBy_lookup_preserved`.
-/

import Patchelf.Elf.ObservableCombinators
import Patchelf.Elf.Basic

namespace Patchelf.Elf

/-- Drop every DT_NEEDED entry whose `.dynstr`-resolved name equals
    `libToRemove`.  Precondition: `.dynamic` exists. -/
def removeNeeded (e : ValidElfFile) (libToRemove : String)
    (_h : e.dynamic.isSome) : ValidElfFile :=
  mapDynamicOp e (fun d => d.filterNeededBy libToRemove.toUTF8)

/-! ## Observables -/

/-- Main observable: no surviving `needed` entry resolves to `libToRemove`. -/
theorem removeNeeded_observable
    (e : ValidElfFile) (libToRemove : String) (h : e.dynamic.isSome) :
    ∃ dyn',
      (removeNeeded e libToRemove h).dynamic = some dyn' ∧
      ∀ (i : Nat) (hi : i < dyn'.needed.size),
        e.dynstr.lookup (dyn'.needed[i]'hi) ≠ some libToRemove.toUTF8 := by
  obtain ⟨dyn, _hDyn, hResult⟩ :=
    mapDynamicOp_observable e (fun d => d.filterNeededBy libToRemove.toUTF8) h
  exact ⟨dyn.filterNeededBy libToRemove.toUTF8, hResult,
         filterNeededBy_lookup_preserved dyn libToRemove.toUTF8⟩

end Patchelf.Elf
