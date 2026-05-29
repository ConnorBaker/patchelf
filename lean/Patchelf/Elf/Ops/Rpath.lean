/-
  modifyRPath — set or remove DT_RPATH / DT_RUNPATH.

  Modal op.  `.set` grows dynstr + sets rpath/runpath slot.
  `.remove` drops both.
-/
module

public import Patchelf.Elf.ObservableCombinators
public import Patchelf.Elf.Basic

@[expose] public section

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

/-- Non-corruption companion: `.set` touches ONLY the rpath/runpath slots.  The
    other dynamic fields survive as their rebased originals — `needed.size` is
    unchanged, `flags1`/`debug` are equal — for either `forceRpath` mode.  Rules
    out an adversary that sets the rpath but drops a DT_NEEDED entry or clobbers
    a flags/debug slot. -/
theorem modifyRPath_set_preserves
    (e : ValidElfFile) (newRpath : String) (fr : Bool) (h : e.dynamic.isSome)
    (dyn : DynamicSection e.dynstr) (hDyn : e.dynamic = some dyn) :
    ∃ (dyn' : DynamicSection (modifyRPath e fr .set newRpath h).dynstr),
      (modifyRPath e fr .set newRpath h).dynamic = some dyn' ∧
      dyn'.needed.size = dyn.needed.size ∧
      dyn'.flags1 = dyn.flags1 ∧ dyn'.debug = dyn.debug := by
  refine ⟨(dyn.rebase (StringSection.size_le_append e.dynstr newRpath)).setRpathTag fr
            (e.dynstr.appendOffset newRpath), ?_, ?_, ?_, ?_⟩
  · show (growDynstrDynamicOp e newRpath (fun _ off d => d.setRpathTag fr off)).dynamic = _
    unfold growDynstrDynamicOp ValidElfFile.growDynstr
    rw [hDyn]; rfl
  · show (DynamicSection.setRpathTag (dyn.rebase _) fr _).needed.size = _
    unfold DynamicSection.setRpathTag
    cases fr <;> exact DynamicSection.rebase_needed_size _ _
  · show (DynamicSection.setRpathTag (dyn.rebase _) fr _).flags1 = _
    unfold DynamicSection.setRpathTag; cases fr <;> rfl
  · show (DynamicSection.setRpathTag (dyn.rebase _) fr _).debug = _
    unfold DynamicSection.setRpathTag; cases fr <;> rfl

end Patchelf.Elf
