/-
  Typed StringSection with intrinsic invariants.

  Design:
    * A `StringSection` is a well-formed byte array (null-terminated when
      non-empty).  The WellFormed proof is a FIELD of the structure — not
      a post-hoc validation predicate.
    * `append` returns an offset as `Fin st'.bytes.size` — in-bounds-ness
      is at the type level.
    * Two sections are related by `≤` when the smaller is a prefix of the
      larger.  `append` produces a `≤`-related pair automatically.
    * `Fin.castLE` lifts offsets from the smaller table to the larger.

  This is a thin wrapper over the existing `StringTable` machinery in
  `Basic.lean` — we reuse `append_size`, `append_wellFormed`, `append_lookup`,
  etc. so we don't re-prove byte-level runway lemmas.
-/

import Patchelf.Elf.Basic

namespace Patchelf.Elf

open Patchelf.Elf (StringTable)

/-- A well-formed string section: bytes + intrinsic null-termination proof.

    Invariant: `bytes.size = 0 ∨ bytes[bytes.size - 1] = 0`.  This is
    exactly `StringTable.WellFormed`; we wrap it as a subtype so callers
    can't construct a malformed section. -/
structure StringSection where
  bytes : ByteArray
  wf    : (⟨bytes⟩ : StringTable).WellFormed
  deriving Repr

namespace StringSection

/-- The size of the underlying bytes.  Named so proofs about `Fin .size`
    offsets can rewrite on it. -/
@[simp] def size (ss : StringSection) : Nat := ss.bytes.size

/-- Reinterpret a `StringSection` as a `StringTable` (forgetting the wf
    field).  Used to lift existing `StringTable` lemmas. -/
@[simp] def toTable (ss : StringSection) : StringTable := ⟨ss.bytes⟩

/-- The empty string section is well-formed. -/
def empty : StringSection where
  bytes := ByteArray.empty
  wf    := Or.inl rfl

/-- Look up the C-string at a typed offset.  The offset is always
    in-bounds by construction (it's a `Fin ss.size`). -/
def lookup (ss : StringSection) (offset : Fin ss.size) : Option ByteArray :=
  ss.toTable.lookup offset.val

/-- Scan the table for `target`; return the offset (as `Fin ss.size`)
    if found.  Wrapper over `StringTable.findOffsetOf` that carries
    in-bounds-ness in the type.  The post-condition is bundled in the
    returned subtype — the offset index is a real `Fin`. -/
def findOffsetOf (ss : StringSection) (target : ByteArray) : Option (Fin ss.size) :=
  match ss.toTable.findOffsetOf target with
  | none   => none
  | some n =>
      -- In principle `findOffsetOf` returns an offset `< ss.bytes.size`;
      -- proving that in full closes another ~80 LOC of byte-level work
      -- we don't need for the addNeeded prototype.  For this prototype
      -- we emit a dependent-if that rejects out-of-bounds offsets at
      -- runtime.  A future tightening (see TIGHTENING note below) makes
      -- this `Fin`-valued directly from a strengthened
      -- `StringTable.findOffsetOf_lt`.
      if hLt : n < ss.size then some ⟨n, hLt⟩ else none

/-- Append a string + null terminator.  Returns the new section plus
    the typed offset at which `s` was placed.

    The returned offset is `Fin new_ss.size` — in-bounds by construction.
    Callers don't prove bounds; the type delivers them. -/
def append (ss : StringSection) (s : String) :
    StringSection × Fin (ss.size + s.toUTF8.size + 1) :=
  let p := ss.toTable.append s
  have hSize : p.1.bytes.size = ss.size + s.toUTF8.size + 1 :=
    StringTable.append_size ss.toTable s
  have hOff : p.2 = ss.size := rfl
  have hWf  : p.1.WellFormed := StringTable.append_wellFormed ss.toTable s
  have hLt  : p.2 < ss.size + s.toUTF8.size + 1 := by rw [hOff]; omega
  (⟨p.1.bytes, hWf⟩, ⟨p.2, hLt⟩)

/-- Size-in-new-section equality after `append`.  Useful when the
    `append` return type's size expression needs normalization. -/
@[simp] theorem append_size (ss : StringSection) (s : String) :
    (ss.append s).1.size = ss.size + s.toUTF8.size + 1 := by
  unfold append size
  exact StringTable.append_size ss.toTable s

/-! ## Prefix ordering

    `ss ≤ ss'` iff `ss.bytes` is a prefix of `ss'.bytes`.  This is what
    `append` produces, and it's exactly what we need to lift offsets:
    `Fin ss.size → Fin ss'.size` is just `Fin.castLE` when `ss.size ≤ ss'.size`.

    We use a custom notation so that the size-only lift is usable even
    when full prefix-equality is overkill.  Every op in patchelf that
    rebases an offset only needs size-monotonicity.
-/

/-- Size-monotonicity: `ss.size ≤ ss'.size`.  This is the weaker form
    of prefix-containment — it's all that addNeeded/setRpath/setSoname
    need for offset rebasing, so we model it directly as a Prop rather
    than introducing a full `PrefixLE` relation. -/
def SizeLE (ss ss' : StringSection) : Prop := ss.size ≤ ss'.size

/-- `append` is size-monotone. -/
theorem size_le_append (ss : StringSection) (s : String) :
    SizeLE ss (ss.append s).1 := by
  unfold SizeLE
  rw [append_size]
  omega

/-- Lift an offset from `ss` to `ss'` when `ss.size ≤ ss'.size`.  The
    offset is numerically the same — `Fin.castLE` is a no-op at runtime. -/
def rebase (ss ss' : StringSection) (h : SizeLE ss ss')
    (off : Fin ss.size) : Fin ss'.size :=
  ⟨off.val, Nat.lt_of_lt_of_le off.isLt h⟩

/-- Convenience: after `append`, a pre-existing offset lifts to the new
    section.  Avoids callers computing the `SizeLE` witness explicitly. -/
def rebaseAfterAppend (ss : StringSection) (s : String)
    (off : Fin ss.size) : Fin (ss.append s).1.size :=
  rebase ss (ss.append s).1 (size_le_append ss s) off

/-! ## Observable: the appended string looks up correctly at the new offset. -/

/-- The returned offset, cast to the new section's Fin-typed size.
    `append` returns a `Fin (ss.size + s.toUTF8.size + 1)` because that
    expression is where the size *came from*; `append_size` equates it
    with `(ss.append s).1.size`. -/
def appendOffset (ss : StringSection) (s : String) : Fin (ss.append s).1.size :=
  (ss.append s).2.cast (append_size ss s).symm

/-- After appending `s` (with no interior NULs), looking up the returned
    offset in the new section yields `s.toUTF8`.  This is the FUNDAMENTAL
    observable for any op that grows `.dynstr`. -/
theorem append_lookup (ss : StringSection) (s : String)
    (hNoNulls : StringTable.NoNullBytes s.toUTF8) :
    (ss.append s).1.lookup (ss.appendOffset s) = some s.toUTF8 :=
  StringTable.append_lookup ss.toTable s hNoNulls

end StringSection
end Patchelf.Elf
