/-
  replaceNeeded{,Reuse} — rewrite DT_NEEDED entries by name.

  Uses `mapDynamicOp` + `replaceNeededBy_getElem_rewritten`.
-/
module

public import Patchelf.Elf.ObservableCombinators
public import Patchelf.Elf.Basic

@[expose] public section

namespace Patchelf.Elf

open Patchelf.Elf (StringTable)

/-- Rewrite matching DT_NEEDED entries to an existing `.dynstr` offset.

    Direct record update rather than `mapDynamicOp` because `newOffset`
    is specifically `Fin e.dynstr.size` — the ds-polymorphic signature
    of `mapDynamicOp` doesn't fit this op. -/
def replaceNeededReuse (e : ValidElfFile) (oldName : String)
    (newOffset : Fin e.dynstr.size) (_h : e.dynamic.isSome) : ValidElfFile :=
  { e with dynamic := e.dynamic.map fun d =>
      d.replaceNeededBy oldName.toUTF8 newOffset }

/-- Grow `.dynstr` with `newName`, rebase sections, rewrite DT_NEEDED. -/
def replaceNeeded (e : ValidElfFile) (oldName newName : String)
    (_h : e.dynamic.isSome) : ValidElfFile :=
  growDynstrDynamicOp e newName
    (fun _ off d => d.replaceNeededBy oldName.toUTF8 off)

/-! ## Observables -/

theorem replaceNeededReuse_observable
    (e : ValidElfFile) (oldName : String) (newOffset : Fin e.dynstr.size)
    (h : e.dynamic.isSome)
    (dyn : DynamicSection e.dynstr) (hDyn : e.dynamic = some dyn)
    (i : Nat) (hi : i < dyn.needed.size)
    (hMatches : e.dynstr.lookup (dyn.needed[i]'hi) = some oldName.toUTF8) :
    ∃ dyn',
      (replaceNeededReuse e oldName newOffset h).dynamic = some dyn' ∧
      ∃ hi' : i < dyn'.needed.size,
        dyn'.needed[i]'hi' = newOffset := by
  refine ⟨dyn.replaceNeededBy oldName.toUTF8 newOffset, ?_, ?_⟩
  · unfold replaceNeededReuse; simp [hDyn]
  · exact replaceNeededBy_getElem_rewritten dyn oldName.toUTF8 newOffset i hi hMatches

/-- `replaceNeeded` (grow path): input entry at index `i` (rebased to
    new dynstr) whose lookup equals `oldName` → output entry at `i` has
    value equal to the new append-offset. -/
theorem replaceNeeded_observable_offset
    (e : ValidElfFile) (oldName newName : String)
    (h : e.dynamic.isSome)
    (dyn : DynamicSection e.dynstr) (hDyn : e.dynamic = some dyn)
    (i : Nat) (hi : i < dyn.needed.size)
    (hMatchesThroughNew :
      (e.dynstr.append newName).1.lookup
        ((dyn.rebase (StringSection.size_le_append e.dynstr newName)).needed[i]'(by
          rw [DynamicSection.rebase_needed_size]; exact hi))
      = some oldName.toUTF8) :
    ∃ dyn',
      (replaceNeeded e oldName newName h).dynamic = some dyn' ∧
      ∃ hi' : i < dyn'.needed.size,
        (dyn'.needed[i]'hi').val = (e.dynstr.appendOffset newName).val := by
  have hRebased :
      i < (dyn.rebase (StringSection.size_le_append e.dynstr newName)).needed.size := by
    rw [DynamicSection.rebase_needed_size]; exact hi
  refine ⟨(dyn.rebase (StringSection.size_le_append e.dynstr newName)).replaceNeededBy
            oldName.toUTF8 (e.dynstr.appendOffset newName), ?_, ?_⟩
  · unfold replaceNeeded growDynstrDynamicOp ValidElfFile.growDynstr; simp [hDyn]
  · obtain ⟨hi'', hEq⟩ := replaceNeededBy_getElem_rewritten
                           (dyn.rebase (StringSection.size_le_append e.dynstr newName))
                           oldName.toUTF8 (e.dynstr.appendOffset newName) i hRebased
                           hMatchesThroughNew
    exact ⟨hi'', congrArg Fin.val hEq⟩

end Patchelf.Elf
