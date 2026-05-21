/-
  addDebugTag — insert DT_DEBUG entry with value 0 if absent.

  Uses `mapDynamicOp` combinator.  Main observable collapses to a
  single `obtain` + case split on `dyn.debug`.
-/
module

public import Patchelf.Elf.ObservableCombinators

@[expose] public section

namespace Patchelf.Elf

/-- Insert a DT_DEBUG entry (value 0) if absent; no-op otherwise. -/
def addDebugTag (e : ValidElfFile) (_h : e.dynamic.isSome) : ValidElfFile :=
  mapDynamicOp e (fun d => d.addDebugTag)

/-! ## Observables -/

/-- Main observable: after addDebugTag, `dyn'.debug.isSome`. -/
theorem addDebugTag_observable (e : ValidElfFile) (h : e.dynamic.isSome) :
    ∃ dyn', (addDebugTag e h).dynamic = some dyn' ∧ dyn'.debug.isSome = true := by
  obtain ⟨dyn, hDyn, hResult⟩ := mapDynamicOp_observable e (fun d => d.addDebugTag) h
  refine ⟨dyn.addDebugTag, hResult, ?_⟩
  unfold DynamicSection.addDebugTag
  cases hd : dyn.debug with
  | none   => simp
  | some v => simp [hd]

/-- Idempotence: if DT_DEBUG was present with value `v`, post value = `v`. -/
theorem addDebugTag_idempotent_value
    (e : ValidElfFile) (h : e.dynamic.isSome)
    (dyn : DynamicSection e.dynstr) (hDyn : e.dynamic = some dyn)
    (v : UInt64) (hv : dyn.debug = some v) :
    ∃ dyn', (addDebugTag e h).dynamic = some dyn' ∧ dyn'.debug = some v := by
  refine ⟨dyn.addDebugTag, ?_, ?_⟩
  · unfold addDebugTag mapDynamicOp; simp [hDyn]
  · unfold DynamicSection.addDebugTag; simp [hv]

/-- Insertion case: if DT_DEBUG was absent, post value = 0. -/
theorem addDebugTag_insert_value
    (e : ValidElfFile) (h : e.dynamic.isSome)
    (dyn : DynamicSection e.dynstr) (hDyn : e.dynamic = some dyn)
    (hNone : dyn.debug = none) :
    ∃ dyn', (addDebugTag e h).dynamic = some dyn' ∧ dyn'.debug = some 0 := by
  refine ⟨dyn.addDebugTag, ?_, ?_⟩
  · unfold addDebugTag mapDynamicOp; simp [hDyn]
  · unfold DynamicSection.addDebugTag; simp [hNone]

end Patchelf.Elf
