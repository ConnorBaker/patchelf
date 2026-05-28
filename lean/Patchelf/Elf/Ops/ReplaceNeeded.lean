/-
  replaceNeeded{,Reuse} — rewrite DT_NEEDED entries by name, plus
  matching `.gnu.version_r` `vn_file` offsets.

  Uses `mapDynamicOp` + `replaceNeededBy_getElem_rewritten`.

  `.gnu.version_r` rewrite: per ELF spec, every `Verneed.vn_file`
  resolves to a library name in some strings section (almost always
  `.dynstr`).  When `replace-needed` rewrites a DT_NEEDED entry from
  `oldName` → `newName`, the matching `vn_file` entries in
  `.gnu.version_r` should track.  Real-world impact: minor (loaders
  resolve symbol versions via `Verdef`, not `vn_file`), but matches
  C++ patchelf and keeps the `.gnu.version_r` table internally
  consistent with `.dynamic`.
-/
module

public import Patchelf.Elf.ObservableCombinators
public import Patchelf.Elf.Basic

@[expose] public section

namespace Patchelf.Elf

open Patchelf.Elf (StringTable)

/-- Rewrite `vn_file` in every `Verneed` entry whose current `vn_file`
    resolves (in `oldDs`) to `oldName`.  The new offset is supplied by
    the caller and is interpreted in the post-replace dynstr (which
    must contain the byte sequence at that offset).  We assume the
    Verneed strings section IS `.dynstr`; binaries that point at a
    distinct strings section via `sh_link` aren't handled — see C++
    patchelf.cc:1853 for the general case. -/
def VerneedSection.rewriteVnFile (vn : VerneedSection) (oldDs : StringSection)
    (oldName : String) (newOffset : UInt32) : VerneedSection :=
  { entries := vn.entries.map fun ve =>
      if h : ve.vn_file.toNat < oldDs.size then
        match oldDs.lookup ⟨ve.vn_file.toNat, h⟩ with
        | some bytes => if bytes = oldName.toUTF8 then { ve with vn_file := newOffset } else ve
        | none       => ve
      else ve }

/-- Rewrite matching DT_NEEDED entries to an existing `.dynstr` offset.

    Direct record update rather than `mapDynamicOp` because `newOffset`
    is specifically `Fin e.dynstr.size` — the ds-polymorphic signature
    of `mapDynamicOp` doesn't fit this op. -/
def replaceNeededReuse (e : ValidElfFile) (oldName : String)
    (newOffset : Fin e.dynstr.size) (_h : e.dynamic.isSome) : ValidElfFile :=
  { e with
      dynamic := e.dynamic.map (fun d => d.replaceNeededBy oldName.toUTF8 newOffset)
      verneed := e.verneed.map (fun vn =>
        vn.rewriteVnFile e.dynstr oldName newOffset.val.toUInt32) }

/-- Grow `.dynstr` with `newName`, rebase sections, rewrite DT_NEEDED
    and matching `.gnu.version_r` `vn_file` entries. -/
def replaceNeeded (e : ValidElfFile) (oldName newName : String)
    (_h : e.dynamic.isSome) : ValidElfFile :=
  let p := e.growDynstr newName
  let e' := p.1
  let off := p.2
  let newDynamic := e'.dynamic.map (fun d => d.replaceNeededBy oldName.toUTF8 off)
  -- The vn_file lookup must use the OLD dynstr; old offsets survive an
  -- append and still resolve to the same byte sequences.
  let newVerneed := e'.verneed.map (fun vn =>
    vn.rewriteVnFile e.dynstr oldName off.val.toUInt32)
  { e' with dynamic := newDynamic, verneed := newVerneed }

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
  · unfold replaceNeeded ValidElfFile.growDynstr; simp [hDyn]
  · obtain ⟨hi'', hEq⟩ := replaceNeededBy_getElem_rewritten
                           (dyn.rebase (StringSection.size_le_append e.dynstr newName))
                           oldName.toUTF8 (e.dynstr.appendOffset newName) i hRebased
                           hMatchesThroughNew
    exact ⟨hi'', congrArg Fin.val hEq⟩

end Patchelf.Elf
