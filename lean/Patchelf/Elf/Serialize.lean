/-
  `writeArray`: the polymorphic byte-array concatenation combinator
  used by every per-struct serializer, plus the `writeArray_size_of_uniform`
  size lemma.

  All per-struct `.write` functions (DynEntry, Symbol, Vernaux,
  ProgramHeader, SectionHeader, ElfIdent, ElfHeader) are DSL-generated
  in `Schemas.lean` via `elf_schema`. The variable-size writers
  (Verneed, SysV hash, GNU hash) are hand-written in `Schemas.lean`
  too, co-located with the DSL outputs they depend on.
-/

import Patchelf.Elf.Basic
import Patchelf.Elf.Layout
import Patchelf.Elf.Writer

namespace Patchelf.Elf

open Layout

/-- Concatenate a writer over an array, in order.

    Lean's `ByteArray.append` is implemented via in-place extension when
    the left operand is uniquely referenced (no other alias holds the
    same FFI-level pointer). In the `foldl` pattern below, the
    accumulator is always the most-recent result, so uniqueness holds
    and each `++` is amortized O(|f x|) rather than O(|acc|). Total cost:
    O(total output bytes), same as a pre-sized builder. -/
def writeArray {α} (f : α → ByteArray) (arr : Array α) : ByteArray :=
  arr.foldl (fun acc x => acc ++ f x) ByteArray.empty

/-- When `f` produces a fixed-size ByteArray, `writeArray f arr` totals
    `arr.size * n` bytes. Proven via `List.foldl`. -/
theorem writeArray_size_of_uniform {α} (f : α → ByteArray) (n : Nat)
    (hUniform : ∀ x, (f x).size = n) (arr : Array α) :
    (writeArray f arr).size = arr.size * n := by
  unfold writeArray
  rw [← Array.foldl_toList]
  rw [Array.size, arr.length_toList]
  -- Generalize over the initial accumulator.
  suffices h : ∀ (acc : ByteArray) (l : List α),
      (l.foldl (fun acc x => acc ++ f x) acc).size = acc.size + l.length * n by
    have := h ByteArray.empty arr.toList
    simpa using this
  intro acc l
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih, ByteArray.size_append, hUniform, List.length_cons,
        Nat.succ_mul]
    omega

end Patchelf.Elf
