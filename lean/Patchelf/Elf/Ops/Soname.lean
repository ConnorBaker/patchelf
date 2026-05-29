/-
  modifySoname — set or remove DT_SONAME.

  Semantics (matching patchelf.cc:1432 `modifySoname`):
    * `.set newName` — append `newName` to `.dynstr`, set `soname` slot.
    * `.remove`      — clear the `soname` slot.

  Uses the observable combinators to eliminate boilerplate; each
  branch's observable is 3 lines.
-/
module

public import Patchelf.Elf.ObservableCombinators
public import Patchelf.Elf.Basic

@[expose] public section

namespace Patchelf.Elf

open Patchelf.Elf (StringTable)

inductive SonameMode | set | remove
  deriving DecidableEq, Repr

/-- Modify DT_SONAME.  `.set` grows dynstr + sets soname slot;
    `.remove` just clears the slot. -/
def modifySoname (e : ValidElfFile) (mode : SonameMode) (newName : String)
    (_h : e.dynamic.isSome) : ValidElfFile :=
  match mode with
  | .remove => mapDynamicOp e (fun d => d.removeSoname)
  | .set    => growDynstrDynamicOp e newName (fun _ off d => d.setSonameOff off)

/-! ## Observables -/

theorem modifySoname_remove_observable
    (e : ValidElfFile) (newName : String) (h : e.dynamic.isSome) :
    ∃ dyn', e.dynamic = some dyn' ∧
      (modifySoname e .remove newName h).dynamic = some dyn'.removeSoname :=
  mapDynamicOp_observable e _ h

theorem modifySoname_set_observable
    (e : ValidElfFile) (newName : String) (h : e.dynamic.isSome)
    (hNoNulls : StringTable.NoNullBytes newName.toUTF8) :
    ∃ (dyn' : DynamicSection (modifySoname e .set newName h).dynstr)
      (off : Fin (modifySoname e .set newName h).dynstr.size),
      (modifySoname e .set newName h).dynamic = some dyn' ∧
      dyn'.soname = some off ∧
      (modifySoname e .set newName h).dynstr.lookup off = some newName.toUTF8 :=
  growDynstrDynamicOp_observable
    (P := fun d off => d.soname = some off)
    e newName _ h hNoNulls
    (fun _ => by unfold DynamicSection.setSonameOff; simp)

/-- Non-corruption companion: `.set` touches ONLY the soname slot.  The other
    dynamic fields survive as their rebased originals — `needed.size` is
    unchanged, `flags1`/`debug` are equal (rebase doesn't cast scalars).  Rules
    out an adversary that sets the soname but drops a DT_NEEDED entry or clobbers
    a flags/debug slot. -/
theorem modifySoname_set_preserves
    (e : ValidElfFile) (newName : String) (h : e.dynamic.isSome)
    (dyn : DynamicSection e.dynstr) (hDyn : e.dynamic = some dyn) :
    ∃ (dyn' : DynamicSection (modifySoname e .set newName h).dynstr),
      (modifySoname e .set newName h).dynamic = some dyn' ∧
      dyn'.needed.size = dyn.needed.size ∧
      dyn'.flags1 = dyn.flags1 ∧ dyn'.debug = dyn.debug := by
  refine ⟨(dyn.rebase (StringSection.size_le_append e.dynstr newName)).setSonameOff
            (e.dynstr.appendOffset newName), ?_, ?_, ?_, ?_⟩
  · show (growDynstrDynamicOp e newName (fun _ off d => d.setSonameOff off)).dynamic = _
    unfold growDynstrDynamicOp ValidElfFile.growDynstr
    rw [hDyn]; rfl
  · show (DynamicSection.setSonameOff (dyn.rebase _) _).needed.size = _
    unfold DynamicSection.setSonameOff
    exact DynamicSection.rebase_needed_size _ _
  · show (DynamicSection.setSonameOff (dyn.rebase _) _).flags1 = _
    rfl
  · show (DynamicSection.setSonameOff (dyn.rebase _) _).debug = _
    rfl

end Patchelf.Elf
