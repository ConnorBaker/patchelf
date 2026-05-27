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

/-- Adversary-rejecting observable.  An identity `addDebugTag` would
    satisfy the basic `_observable` (`debug.isSome = true`) only on
    files that already had DT_DEBUG; this version rules that out by
    case-splitting on the input.

    Either DT_DEBUG was already present and the value is preserved,
    OR it was absent and the post-op value is `some 0` — i.e. the op
    is observably non-trivial unless its precondition was idempotent. -/
theorem addDebugTag_observable_strong (e : ValidElfFile) (h : e.dynamic.isSome) :
    ∃ (dyn : DynamicSection e.dynstr) (dyn' : DynamicSection e.dynstr),
      e.dynamic = some dyn ∧ (addDebugTag e h).dynamic = some dyn' ∧
        ((∃ v, dyn.debug = some v ∧ dyn'.debug = some v) ∨
         (dyn.debug = none ∧ dyn'.debug = some 0)) := by
  obtain ⟨dyn, hDyn⟩ := Option.isSome_iff_exists.mp h
  refine ⟨dyn, dyn.addDebugTag, hDyn, ?_, ?_⟩
  · unfold addDebugTag mapDynamicOp; simp [hDyn]
  · by_cases hSome : dyn.debug.isSome
    · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hSome
      exact .inl ⟨v, hv, by unfold DynamicSection.addDebugTag; simp [hv]⟩
    · have hNone : dyn.debug = none := Option.not_isSome_iff_eq_none.mp hSome
      exact .inr ⟨hNone, by unfold DynamicSection.addDebugTag; simp [hNone]⟩

end Patchelf.Elf
