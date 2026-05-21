/-
  Observable combinators.

  Every "grow .dynstr + mutate .dynamic" op has an observable
  of the same shape:

    ∃ dyn' off,
      result.dynamic = some dyn' ∧
      <field-specific claim using off> ∧
      result.dynstr.lookup off = some name.toUTF8

  The proof of each case is mechanical:
    1. Destructure `h : e.dynamic.isSome` into a concrete dyn.
    2. Witness = dyn rebased then mutated + appendOffset.
    3. `dynamic = some` branch: unfold + simp [hDyn].
    4. field branch: per-op; typically `unfold <setter>; simp`.
    5. lookup branch: `StringSection.append_lookup`.

  This file packages (1), (3), (5) into a single theorem.  Each op
  proves (4) inline (the field-specific equation is what makes the op
  distinctive; it can't be abstracted).

  After this lands, a grow-dynstr op's observable collapses from
  ~20 LOC to ~5 LOC.
-/
module

public import Patchelf.Elf.ValidElfFile
public import Patchelf.Elf.Basic

@[expose] public section

namespace Patchelf.Elf

open Patchelf.Elf (StringTable)

/-- Shape of a "grow-dynstr op on the dynamic section."
    The op:
      * Appends `name` to `.dynstr` (using `growDynstr`).
      * Rebases the existing `DynamicSection` through size-le-append.
      * Applies `f` to the rebased section, using the new offset.

    This is the shape shared by addNeeded, setSoname.set,
    modifyRPath.set, addRpathEntry, replaceNeeded (grow path).

    Preserving the "result = growDynstr + map f" form as the
    canonical shape lets a single observable theorem cover them all. -/
def growDynstrDynamicOp
    (e : ValidElfFile) (name : String)
    (f : (ds : StringSection) → Fin ds.size → DynamicSection ds → DynamicSection ds) :
    ValidElfFile :=
  let p := e.growDynstr name
  let e'  := p.1
  let off := p.2
  { e' with dynamic := e'.dynamic.map (f _ off) }

/-- The master observable.  Given any `f` that produces a dynamic
    section whose post-mutation shape satisfies `P dyn' off`,
    `growDynstrDynamicOp e name f` produces a ValidElfFile whose
    dynamic = some dyn' and whose dynstr contains `name` at `off`.

    Caller responsibilities:
      * `hDynProp` — `P` holds of the mutator's output at `off`.
        Typically 1-2 lines: `unfold f; simp` or similar.
      * `hNoNulls` — `name.toUTF8` has no interior NULs (so
        `append_lookup` fires).
      * `h` — the dynamic section is present.
-/
theorem growDynstrDynamicOp_observable
    {P : ∀ {ds : StringSection}, DynamicSection ds → Fin ds.size → Prop}
    (e : ValidElfFile) (name : String)
    (f : (ds : StringSection) → Fin ds.size → DynamicSection ds → DynamicSection ds)
    (h : e.dynamic.isSome)
    (hNoNulls : StringTable.NoNullBytes name.toUTF8)
    (hDynProp : ∀ (dyn : DynamicSection e.dynstr),
      P (f _ (e.dynstr.appendOffset name)
           (dyn.rebase (StringSection.size_le_append e.dynstr name)))
        (e.dynstr.appendOffset name)) :
    ∃ (dyn' : DynamicSection (growDynstrDynamicOp e name f).dynstr)
      (off : Fin (growDynstrDynamicOp e name f).dynstr.size),
      (growDynstrDynamicOp e name f).dynamic = some dyn' ∧
      P dyn' off ∧
      (growDynstrDynamicOp e name f).dynstr.lookup off = some name.toUTF8 := by
  obtain ⟨dyn, hDyn⟩ := Option.isSome_iff_exists.mp h
  refine ⟨
      f _ (e.dynstr.appendOffset name)
        (dyn.rebase (StringSection.size_le_append e.dynstr name)),
      e.dynstr.appendOffset name,
      ?_, hDynProp dyn, ?_⟩
  · unfold growDynstrDynamicOp ValidElfFile.growDynstr
    simp [hDyn]
  · show (e.dynstr.append name).1.lookup (e.dynstr.appendOffset name) = _
    exact StringSection.append_lookup e.dynstr name hNoNulls

/-! ## Shape for modal ops (set/remove with remove-branch)

    `modifyRPath`, `modifySoname` have a `.remove` mode that doesn't
    grow dynstr — just clears a slot.  That branch is even simpler:
    one `dynamic.map` call.  Observable: `field = none`. -/

/-- A mutator that simply maps over `.dynamic` without touching dynstr.
    Shape shared by `.remove` modes of modal ops + removeRpath,
    removeNeeded, etc. -/
def mapDynamicOp
    (e : ValidElfFile)
    (f : {ds : StringSection} → DynamicSection ds → DynamicSection ds) :
    ValidElfFile :=
  { e with dynamic := e.dynamic.map f }

/-- Observable for a map-over-dynamic op: the result's dynamic is
    `some (f dyn)` for the original dyn. -/
theorem mapDynamicOp_observable
    (e : ValidElfFile)
    (f : {ds : StringSection} → DynamicSection ds → DynamicSection ds)
    (h : e.dynamic.isSome) :
    ∃ (dyn : DynamicSection e.dynstr),
      e.dynamic = some dyn ∧
      (mapDynamicOp e f).dynamic = some (f dyn) := by
  obtain ⟨dyn, hDyn⟩ := Option.isSome_iff_exists.mp h
  refine ⟨dyn, hDyn, ?_⟩
  unfold mapDynamicOp
  simp [hDyn]

/-! ## DynamicSection.{filter,map}-needed lemmas (direct on the operations)

    Rather than abstract over arbitrary mutators (which tends to trip
    up Lean 4.29's dependent-rewrite machinery), we expose direct
    lemmas on the specific DynamicSection operations.  Callers apply
    these at the call-site rather than through a generic combinator.
-/

/-- After `filterNeededBy target`, every surviving needed entry's
    lookup in `ds` is NOT `some target`. -/
theorem filterNeededBy_lookup_preserved
    {ds : StringSection} (dyn : DynamicSection ds) (target : ByteArray)
    (i : Nat) (hi : i < (dyn.filterNeededBy target).needed.size) :
    ds.lookup ((dyn.filterNeededBy target).needed[i]'hi) ≠ some target := by
  have hMem : (dyn.filterNeededBy target).needed[i]'hi
                ∈ (dyn.filterNeededBy target).needed := Array.getElem_mem _
  have hMem' :
      (dyn.filterNeededBy target).needed[i]'hi ∈
        dyn.needed.filter (fun off =>
          match ds.lookup off with
          | some bytes => bytes ≠ target
          | none       => true) := hMem
  obtain ⟨_, hPred⟩ := Array.mem_filter.mp hMem'
  intro hEq
  rw [hEq] at hPred
  simp at hPred

/-- After `replaceNeededBy target newOff`, the needed entry at index
    `i` equals `newOff` if the input's entry at `i` had lookup = target,
    else equals the input's entry. -/
theorem replaceNeededBy_getElem_rewritten
    {ds : StringSection} (dyn : DynamicSection ds)
    (target : ByteArray) (newOff : Fin ds.size)
    (i : Nat) (hi : i < dyn.needed.size)
    (hMatch : ds.lookup (dyn.needed[i]'hi) = some target) :
    ∃ hi' : i < (dyn.replaceNeededBy target newOff).needed.size,
      (dyn.replaceNeededBy target newOff).needed[i]'hi' = newOff := by
  have hSize : (dyn.replaceNeededBy target newOff).needed.size = dyn.needed.size := by
    unfold DynamicSection.replaceNeededBy; simp
  refine ⟨hSize ▸ hi, ?_⟩
  show (Array.map _ dyn.needed)[i]'_ = newOff
  rw [Array.getElem_map, hMatch]
  simp

end Patchelf.Elf
