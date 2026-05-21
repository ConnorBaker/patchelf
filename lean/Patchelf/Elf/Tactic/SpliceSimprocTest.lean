/-
  Self-test for `simp_splice` (defined in `Tactic/SpliceSimproc.lean`).

  Each test mirrors a real proof shape from `ByteRoundtrip.lean`:
  the manual 4-step splice cascade.  All theorems below are proved
  with `simp_splice` alone, with omega discharging the side conditions.
-/
module

public import Patchelf.Elf.Tactic.SpliceSimproc

@[expose] public section

namespace Patchelf.Elf.Tactic.Test

open Patchelf.Elf.Encoder Patchelf.Elf.Reader

/-- Disjoint splice: read at offset `r` strictly before the splice region. -/
example (bs w : ByteArray) (off r : Nat)
    (hSplice : off + w.size ≤ bs.size)
    (hr : r + 4 ≤ bs.size)
    (hDisj : r + 4 ≤ off) :
    readU32 (splice bs off w) r = readU32 bs r := by
  simp_splice

/-- Disjoint splice: read at offset `r` strictly after the splice region. -/
example (bs w : ByteArray) (off r : Nat)
    (hSplice : off + w.size ≤ bs.size)
    (hr : r + 8 ≤ bs.size)
    (hDisj : off + w.size ≤ r) :
    readU64 (splice bs off w) r = readU64 bs r := by
  simp_splice

/-- Inside-splice at offset 0. -/
example (bs w : ByteArray) (r : Nat)
    (hSplice : 0 + w.size ≤ bs.size)
    (hr : r + 2 ≤ w.size) :
    readU16 (splice bs 0 w) r = readU16 w r := by
  simp_splice

/-- Inside-splice at arbitrary offset. -/
example (bs w : ByteArray) (off r : Nat)
    (hSplice : off + w.size ≤ bs.size)
    (hr1 : off ≤ r)
    (hr2 : r + 4 ≤ off + w.size) :
    readU32 (splice bs off w) r = readU32 w (r - off) := by
  simp_splice

/-- Two-step cascade: outer disjoint splice + inner disjoint splice.
    Mirrors `hStep2 ; hStep3` in `readU8_encode_in_header`. -/
example (bs w₁ w₂ : ByteArray) (off₁ off₂ r : Nat)
    (hSplice₁ : off₁ + w₁.size ≤ bs.size)
    (hSplice₂ : off₂ + w₂.size ≤ (splice bs off₁ w₁).size)
    (hr : r + 1 ≤ bs.size)
    (hDisj₁ : r + 1 ≤ off₁)
    (hDisj₂ : r + 1 ≤ off₂) :
    readU8 (splice (splice bs off₁ w₁) off₂ w₂) r = readU8 bs r := by
  simp_splice

/-- Three-deep cascade with the innermost splice INSIDE at offset 0.
    Mirrors the shape of `hStep2 → hStep3 → hStep4` in
    `readU8_encode_in_header` (shdr disjoint, phdr disjoint, header
    inside-splice at 0).  This is the highest-leverage shape: the
    threading-lemma family in `ByteRoundtrip.lean` is dominated by
    proofs of exactly this form. -/
example (buf0 hdrW phdrW shdrW : ByteArray) (phoff shoff r : Nat)
    (hHdrFit  : 0     + hdrW.size  ≤ buf0.size)
    (hPhdrFit : phoff + phdrW.size ≤ (splice buf0 0 hdrW).size)
    (hShdrFit : shoff + shdrW.size ≤
                  (splice (splice buf0 0 hdrW) phoff phdrW).size)
    (hHdrInside  : r + 1 ≤ hdrW.size)
    (hPhdrDisj   : r + 1 ≤ phoff)
    (hShdrDisj   : r + 1 ≤ shoff) :
    readU8 (splice (splice (splice buf0 0 hdrW) phoff phdrW) shoff shdrW) r
      = readU8 hdrW r := by
  simp_splice

/-- Four-width sweep: same disjoint-splice shape at each width. -/
example (bs w : ByteArray) (off r : Nat)
    (hSplice : off + w.size ≤ bs.size)
    (hr8  : r + 1 ≤ bs.size) (hd8  : r + 1 ≤ off)
    (hr16 : r + 2 ≤ bs.size) (hd16 : r + 2 ≤ off)
    (hr32 : r + 4 ≤ bs.size) (hd32 : r + 4 ≤ off)
    (hr64 : r + 8 ≤ bs.size) (hd64 : r + 8 ≤ off) :
    readU8  (splice bs off w) r = readU8  bs r ∧
    readU16 (splice bs off w) r = readU16 bs r ∧
    readU32 (splice bs off w) r = readU32 bs r ∧
    readU64 (splice bs off w) r = readU64 bs r := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp_splice

end Patchelf.Elf.Tactic.Test
