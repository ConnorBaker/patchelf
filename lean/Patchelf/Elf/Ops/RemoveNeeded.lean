/-
  removeNeeded — drop DT_NEEDED entries whose library name matches.

  Op is `mapDynamicOp` with `filterNeededBy`; observable is a
  2-line corollary of `filterNeededBy_lookup_preserved`.
-/
module

public import Patchelf.Elf.ObservableCombinators
public import Patchelf.Elf.Basic

@[expose] public section

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

/-- Size never grows (filter is monotone). -/
theorem removeNeeded_needed_size_le
    (e : ValidElfFile) (libToRemove : String) (h : e.dynamic.isSome)
    (dyn : DynamicSection e.dynstr) (hDyn : e.dynamic = some dyn) :
    ∃ dyn',
      (removeNeeded e libToRemove h).dynamic = some dyn' ∧
      dyn'.needed.size ≤ dyn.needed.size := by
  refine ⟨dyn.filterNeededBy libToRemove.toUTF8, ?_, ?_⟩
  · unfold removeNeeded mapDynamicOp; simp [hDyn]
  · unfold DynamicSection.filterNeededBy; exact Array.size_filter_le

/-- Adversary-rejecting strong observable: when the input contained at
    least one DT_NEEDED entry resolving to `libToRemove`, the output's
    `needed` is strictly smaller.  An identity `removeNeeded` would
    fail this. -/
theorem removeNeeded_needed_size_lt
    (e : ValidElfFile) (libToRemove : String) (h : e.dynamic.isSome)
    (dyn : DynamicSection e.dynstr) (hDyn : e.dynamic = some dyn)
    (i : Nat) (hi : i < dyn.needed.size)
    (hMatch : e.dynstr.lookup (dyn.needed[i]'hi) = some libToRemove.toUTF8) :
    ∃ dyn',
      (removeNeeded e libToRemove h).dynamic = some dyn' ∧
      dyn'.needed.size < dyn.needed.size := by
  refine ⟨dyn.filterNeededBy libToRemove.toUTF8, ?_, ?_⟩
  · unfold removeNeeded mapDynamicOp; simp [hDyn]
  · -- The predicate fails on `dyn.needed[i]` (lookup matches target),
    -- so `Array.filter` strictly drops at least that element.
    let p : Fin e.dynstr.size → Bool := fun off =>
      match e.dynstr.lookup off with
      | some bytes => bytes ≠ libToRemove.toUTF8
      | none       => true
    have hPred : ¬ p (dyn.needed[i]'hi) = true := by
      simp only [p, hMatch]; simp
    have hMem : dyn.needed[i] ∈ dyn.needed.toList := Array.getElem_mem_toList hi
    have hLen : (dyn.needed.toList.filter p).length < dyn.needed.toList.length :=
      List.length_filter_lt_length_iff_exists.mpr ⟨dyn.needed[i], hMem, hPred⟩
    show (dyn.needed.filter p).size < dyn.needed.size
    rw [show (dyn.needed.filter p).size = (dyn.needed.toList.filter p).length from by
          rw [← Array.length_toList, Array.toList_filter]]
    rw [show dyn.needed.size = dyn.needed.toList.length from Array.length_toList.symm]
    exact hLen

end Patchelf.Elf
