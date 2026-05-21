/-
  noDefaultLib — OR DF_1_NODEFLIB into DT_FLAGS_1.

  `DF_1_NODEFLIB = 0x00000800` per `elf.h` — NOT `DF_1_PIE = 0x08000000`.
-/

import Patchelf.Elf.ObservableCombinators
import Std.Tactic.BVDecide

namespace Patchelf.Elf

/-- DF_1_NODEFLIB: "Ignore default lib search path." -/
def DF_1_NODEFLIB : UInt64 := 0x0000_0800

/-- OR DF_1_NODEFLIB into DT_FLAGS_1 (creating the entry if absent). -/
def noDefaultLib (e : ValidElfFile) (_h : e.dynamic.isSome) : ValidElfFile :=
  mapDynamicOp e (fun d => d.setNoDefaultLib)

/-! ## Observables -/

/-- OR-idempotence on the masked bit: `(x ||| y) &&& y = y`. -/
private theorem or_and_same (x y : UInt64) : (x ||| y) &&& y = y := by
  bv_decide

/-- Main observable: DT_FLAGS_1 is present with DF_1_NODEFLIB bit set. -/
theorem noDefaultLib_observable (e : ValidElfFile) (h : e.dynamic.isSome) :
    ∃ (dyn' : DynamicSection (noDefaultLib e h).dynstr) (v : UInt64),
      (noDefaultLib e h).dynamic = some dyn' ∧
      dyn'.flags1 = some v ∧
      v &&& DF_1_NODEFLIB = DF_1_NODEFLIB := by
  obtain ⟨dyn, _hDyn, hResult⟩ :=
    mapDynamicOp_observable e (fun d => d.setNoDefaultLib) h
  refine ⟨dyn.setNoDefaultLib, (dyn.flags1.getD 0) ||| 0x0000_0800,
          hResult, ?_, ?_⟩
  · show (dyn.setNoDefaultLib).flags1 = _
    unfold DynamicSection.setNoDefaultLib; rfl
  · show ((dyn.flags1.getD 0) ||| 0x0000_0800) &&& DF_1_NODEFLIB = DF_1_NODEFLIB
    unfold DF_1_NODEFLIB
    exact or_and_same _ _

/-- Insertion case: if DT_FLAGS_1 was absent, post value = DF_1_NODEFLIB. -/
theorem noDefaultLib_insert_value
    (e : ValidElfFile) (h : e.dynamic.isSome)
    (dyn : DynamicSection e.dynstr) (hDyn : e.dynamic = some dyn)
    (hNone : dyn.flags1 = none) :
    ∃ dyn', (noDefaultLib e h).dynamic = some dyn' ∧
            dyn'.flags1 = some DF_1_NODEFLIB := by
  refine ⟨dyn.setNoDefaultLib, ?_, ?_⟩
  · unfold noDefaultLib mapDynamicOp; simp [hDyn]
  · show (dyn.setNoDefaultLib).flags1 = _
    unfold DynamicSection.setNoDefaultLib DF_1_NODEFLIB
    rw [hNone]; rfl

/-- Mutate-in-place: post = v ||| DF_1_NODEFLIB. -/
theorem noDefaultLib_mutate_value
    (e : ValidElfFile) (h : e.dynamic.isSome)
    (dyn : DynamicSection e.dynstr) (hDyn : e.dynamic = some dyn)
    (v : UInt64) (hSome : dyn.flags1 = some v) :
    ∃ dyn', (noDefaultLib e h).dynamic = some dyn' ∧
            dyn'.flags1 = some (v ||| DF_1_NODEFLIB) := by
  refine ⟨dyn.setNoDefaultLib, ?_, ?_⟩
  · unfold noDefaultLib mapDynamicOp; simp [hDyn]
  · show (dyn.setNoDefaultLib).flags1 = _
    unfold DynamicSection.setNoDefaultLib DF_1_NODEFLIB
    rw [hSome]; rfl

end Patchelf.Elf
