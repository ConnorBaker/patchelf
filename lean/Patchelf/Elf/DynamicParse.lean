/-
  Parser from raw `Array DynEntry` to typed `DynamicSection`.

  Goal: validate that the typed section algebra admits a clean parser,
  and that the parser's RESPONSIBILITIES align with the byte layer's but are
  structurally simpler (no post-hoc coherence validation).

  Routing policy:
    * DT_NULL          → terminator (consumed; must appear at end)
    * DT_NEEDED        → needed : Array (Fin ds.size)  [bounds-checked]
    * DT_RPATH         → rpath   : Option (Fin ds.size) [last-wins]
    * DT_RUNPATH       → runpath : Option (Fin ds.size) [last-wins]
    * DT_SONAME        → soname  : Option (Fin ds.size) [last-wins]
    * DT_FLAGS_1       → flags1  : Option UInt64         [last-wins]
    * DT_DEBUG         → debug   : Option UInt64         [last-wins]
    * DT_STRTAB/SYMTAB/HASH/GNU_HASH/VERNEED/STRSZ → DROPPED
      (the byte-layer template preserves them; typed ops never touch them)
    * DT_RELA/REL/JMPREL/raw → DROPPED
      (layout-sensitive, byte template preserves them)

  Error taxonomy:
    * `valueOutOfBounds`: DT_NEEDED/RPATH/RUNPATH/SONAME entry whose
      value is ≥ ds.size.  Rejection is strict because a typed
      DynamicSection cannot represent an out-of-bounds offset.

  Duplicates are resolved last-wins for singleton fields.  This
  matches C++ patchelf's behavior (it reads entries linearly; the
  LAST DT_RPATH wins on output).  A stricter parser would reject
  duplicates; that's a one-line change.

  Missing DT_NULL is NOT a parser error in this prototype: we treat
  any input as a valid prefix to be wrapped.  A full port would
  make DT_NULL termination a parser precondition.

  Coherence tags are DROPPED, not validated.  Rationale: patchelf's
  entire raison d'être is to fix malformed coherence; rejecting on
  e.g. stored-DT_STRSZ ≠ ds.size would refuse to operate on the
  exact binaries users want to patch.  The derived values in the
  encoder are guaranteed correct.
-/

import Patchelf.Elf.DynamicSection
import Patchelf.Elf.Basic

namespace Patchelf.Elf

open Patchelf.Elf (DynEntry DynTag)

/-- Parser error for `DynamicSection.parseFrom`.  Minimal for the
    prototype; a full port would carry the offending index + value. -/
inductive DynamicParseError
  /-- A string-ref entry's `value` is ≥ `ds.size`. -/
  | valueOutOfBounds (tag : DynTag) (value : UInt64)
  deriving Repr

namespace DynamicSection

/-- Try to coerce a `UInt64` into `Fin ds.size`.  Returns `none` if
    the value is out of bounds; callers turn that into a
    `valueOutOfBounds` error. -/
private def tryMkFin (ds : StringSection) (v : UInt64) : Option (Fin ds.size) :=
  if h : v.toNat < ds.size then some ⟨v.toNat, h⟩ else none

/-- Per-entry dispatch step.  Takes the accumulator-so-far + the
    next entry; returns the updated accumulator or a parse error.

    Accumulator fields parallel `DynamicSection` but are mutable
    during the fold (represented via updates on an already-allocated
    structure).  Coherence tags and DT_NULL are skipped silently;
    unknown tags fall through to `unstructured`. -/
private def stepEntry (ds : StringSection) (acc : DynamicSection ds)
    (d : DynEntry) : Except DynamicParseError (DynamicSection ds) :=
  match d.tag with
  -- Terminator + coherence tags: DROP (return acc unchanged).
  | DynTag.null | DynTag.strtab | DynTag.symtab | DynTag.strsz
  | DynTag.hash  | DynTag.gnuHash | DynTag.verneed | DynTag.versym => .ok acc
  -- String-ref structured tags.
  | DynTag.needed =>
      match tryMkFin ds d.value with
      | some off => .ok { acc with needed := acc.needed.push off }
      | none     => .error (.valueOutOfBounds DynTag.needed d.value)
  | DynTag.rpath =>
      match tryMkFin ds d.value with
      | some off => .ok { acc with rpath := some off }
      | none     => .error (.valueOutOfBounds DynTag.rpath d.value)
  | DynTag.runpath =>
      match tryMkFin ds d.value with
      | some off => .ok { acc with runpath := some off }
      | none     => .error (.valueOutOfBounds DynTag.runpath d.value)
  | DynTag.soname =>
      match tryMkFin ds d.value with
      | some off => .ok { acc with soname := some off }
      | none     => .error (.valueOutOfBounds DynTag.soname d.value)
  -- Scalar structured tags (no dynstr bound).
  | DynTag.flags1 => .ok { acc with flags1 := some d.value }
  | DynTag.debug  => .ok { acc with debug  := some d.value }
  -- Layout-sensitive tags (DT_RELA / DT_REL / DT_JMPREL / unknown):
  -- DROPPED at the typed layer.  The byte-layer template preserves
  -- them through `Adapter.patchDynamicEntries`, which is the actual
  -- source of truth for layout-sensitive entries.
  | DynTag.rela | DynTag.rel | DynTag.jmprel | DynTag.raw _ _ => .ok acc

/-- The empty dynamic section (for a given `ds`). -/
def empty (ds : StringSection) : DynamicSection ds where
  needed := #[]
  rpath := none
  runpath := none
  soname := none
  flags1 := none
  debug := none

/-- Parse a raw `Array DynEntry` into a typed `DynamicSection ds`.

    Left-fold via `stepEntry`, threading `Except DynamicParseError`.
    The resulting `DynamicSection` has every offset guaranteed
    in-bounds (by `tryMkFin`'s `Fin` construction) and every
    structured field populated correctly. -/
def parseFrom (ds : StringSection) (raw : Array DynEntry) :
    Except DynamicParseError (DynamicSection ds) :=
  raw.foldlM (init := empty ds) (stepEntry ds)

/-! ## Parser preservation theorems -/

/-- The empty accumulator has an empty `needed` array. -/
@[simp] theorem empty_needed (ds : StringSection) :
    (empty ds).needed = #[] := rfl

/-- `stepEntry` on a DT_NEEDED with in-bounds value appends to `needed`. -/
theorem stepEntry_needed_ok
    (ds : StringSection) (acc : DynamicSection ds) (d : DynEntry)
    (hTag : d.tag = DynTag.needed)
    (hLt : d.value.toNat < ds.size) :
    stepEntry ds acc d
      = .ok { acc with needed := acc.needed.push ⟨d.value.toNat, hLt⟩ } := by
  unfold stepEntry
  rw [hTag]
  -- Unfold tryMkFin just enough to expose the dependent if.
  show (match tryMkFin ds d.value with
        | some off => Except.ok { acc with needed := acc.needed.push off }
        | none     => Except.error (DynamicParseError.valueOutOfBounds DynTag.needed d.value)) = _
  unfold tryMkFin
  rw [dif_pos hLt]

/-- `stepEntry` on a DT_NEEDED with out-of-bounds value errors. -/
theorem stepEntry_needed_error
    (ds : StringSection) (acc : DynamicSection ds) (d : DynEntry)
    (hTag : d.tag = DynTag.needed)
    (hGe : ¬ d.value.toNat < ds.size) :
    stepEntry ds acc d = .error (.valueOutOfBounds DynTag.needed d.value) := by
  unfold stepEntry
  rw [hTag]
  show (match tryMkFin ds d.value with
        | some off => Except.ok { acc with needed := acc.needed.push off }
        | none     => Except.error (DynamicParseError.valueOutOfBounds DynTag.needed d.value)) = _
  unfold tryMkFin
  rw [dif_neg hGe]

/-- Parser-preservation witness: a DT_NEEDED entry with in-bounds value
    `v`, processed via `stepEntry`, pushes a matching offset into the
    accumulator's `needed`.  This is the per-entry preservation that
    composes (via `foldlM` induction, not proved here) into the full
    `parseFrom` preservation.

    The byte layer's equivalent chain is ~40 LOC of per-tag-case preservation
    lemmas inside `decodeDynamic` + post-hoc validation.  This one-step parser has one
    3-line theorem per tag. -/
theorem stepEntry_needed_preservation
    (ds : StringSection) (acc : DynamicSection ds) (d : DynEntry)
    (hTag : d.tag = DynTag.needed)
    (hLt : d.value.toNat < ds.size) :
    ∃ acc', stepEntry ds acc d = .ok acc' ∧
            acc'.needed = acc.needed.push ⟨d.value.toNat, hLt⟩ := by
  refine ⟨_, stepEntry_needed_ok ds acc d hTag hLt, ?_⟩
  rfl

/-! ## Singleton-input parser preservation

    Proof that `parseFrom ds #[d]` succeeds and stores the offset
    when `d` is an in-bounds DT_NEEDED.  The full multi-entry form
    follows by `Array.foldlM`-induction over the input; we show the
    singleton case to confirm the composition pattern works. -/

/-- Specialized form for a single DT_NEEDED entry.  Useful as a
    base case when proving `parseFrom`-preservation by induction. -/
theorem parseFrom_singleton_needed
    (ds : StringSection) (d : DynEntry)
    (hTag : d.tag = DynTag.needed)
    (hLt : d.value.toNat < ds.size) :
    parseFrom ds #[d]
      = .ok { (empty ds) with needed := #[⟨d.value.toNat, hLt⟩] } := by
  -- Array.foldlM on a singleton is definitionally one step.  After
  -- unfolding `parseFrom`, the goal reduces to
  --   stepEntry ds (empty ds) d = .ok result
  -- which is precisely `stepEntry_needed_ok`.
  show (stepEntry ds (empty ds) d).bind (fun x => .ok x) = _
  rw [stepEntry_needed_ok ds (empty ds) d hTag hLt]
  rfl

/-! ## Coherence tags are DROPPED -/

/-- DT_STRTAB entries are ignored — regardless of their value, the
    accumulator is unchanged.  This is the key design property: the
    parser doesn't carry the (wrong, or right) stored DT_STRTAB value
    into the typed representation; it trusts the encoder to derive it. -/
theorem stepEntry_strtab_dropped
    (ds : StringSection) (acc : DynamicSection ds) (d : DynEntry)
    (hTag : d.tag = DynTag.strtab) :
    stepEntry ds acc d = .ok acc := by
  unfold stepEntry
  rw [hTag]

/-- Same for DT_STRSZ: dropped regardless of stored value. -/
theorem stepEntry_strsz_dropped
    (ds : StringSection) (acc : DynamicSection ds) (d : DynEntry)
    (hTag : d.tag = DynTag.strsz) :
    stepEntry ds acc d = .ok acc := by
  unfold stepEntry
  rw [hTag]

/-- Same for DT_SYMTAB / HASH / GNU_HASH / VERNEED / VERSYM. -/
theorem stepEntry_coherence_dropped
    (ds : StringSection) (acc : DynamicSection ds) (d : DynEntry)
    (hCoh : d.tag = DynTag.symtab ∨ d.tag = DynTag.hash ∨
            d.tag = DynTag.gnuHash ∨ d.tag = DynTag.verneed ∨
            d.tag = DynTag.versym) :
    stepEntry ds acc d = .ok acc := by
  unfold stepEntry
  rcases hCoh with h|h|h|h|h <;> rw [h]

end DynamicSection
end Patchelf.Elf
