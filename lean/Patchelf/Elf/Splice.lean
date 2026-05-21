/-
  `Encoder.splice`: overwrite a byte-array region with fresh bytes
  while preserving the outer size.  Used by the byte-layer encoder.
-/
module

public import Patchelf.Elf.Reader

@[expose] public section

namespace Patchelf.Elf.Encoder

/-- Overwrite `bs[off..off+w.size)` with `w`, returning a new ByteArray
    of the same size as `bs`. If out-of-bounds, return `bs` unchanged
    (size-preserving even on error). -/
def splice (bs : ByteArray) (off : Nat) (w : ByteArray) : ByteArray :=
  if off + w.size ≤ bs.size then
    bs.extract 0 off ++ w ++ bs.extract (off + w.size) bs.size
  else bs

@[simp] theorem splice_size (bs : ByteArray) (off : Nat) (w : ByteArray) :
    (splice bs off w).size = bs.size := by
  unfold splice
  by_cases h : off + w.size ≤ bs.size
  · simp [h, ByteArray.size_append, ByteArray.size_extract]
    omega
  · simp [h]

/-! ## Splice preservation: bytes outside the splice region survive.

    These are the structural lemmas Tier D needs: when a splice writes
    region `[off, off + w.size)` and a subsequent read is at offset `r`
    disjoint from that region, the read sees the original byte. -/

/-- Pointwise byte preservation: getting a byte outside the splice region
    returns the original byte. -/
private theorem splice_getElem_outside (bs : ByteArray) (off : Nat) (w : ByteArray)
    (hSplice : off + w.size ≤ bs.size) (r : Nat)
    (hr : r < bs.size)
    (hDisjoint : r < off ∨ off + w.size ≤ r) :
    (splice bs off w)[r]'(by rw [splice_size]; exact hr) = bs[r]'hr := by
  have hSpliceEq : splice bs off w
      = bs.extract 0 off ++ w ++ bs.extract (off + w.size) bs.size := by
    unfold splice; rw [if_pos hSplice]
  have hSplSz := splice_size bs off w
  rw [show (splice bs off w)[r]'(by rw [splice_size]; exact hr)
      = (bs.extract 0 off ++ w ++ bs.extract (off + w.size) bs.size)[r]'(by
          rw [← hSpliceEq, hSplSz]; exact hr)
      from by congr 1]
  rcases hDisjoint with hL | hR
  · rw [ByteArray.getElem_append_left, ByteArray.getElem_append_left,
        ByteArray.getElem_extract]
    · simp
    · simp [ByteArray.size_extract]; omega
    · rw [ByteArray.size_append, ByteArray.size_extract]; omega
  · have hr_ge : (bs.extract 0 off ++ w).size ≤ r := by
      rw [ByteArray.size_append, ByteArray.size_extract]
      have : min off bs.size = off := by omega
      rw [this]; omega
    rw [ByteArray.getElem_append_right hr_ge, ByteArray.getElem_extract]
    have hAppSz : (bs.extract 0 off ++ w).size = off + w.size := by
      rw [ByteArray.size_append, ByteArray.size_extract]
      have : min off bs.size = off := by omega
      omega
    show bs[off + w.size + (r - (bs.extract 0 off ++ w).size)]'(by omega)
       = bs[r]'hr
    have : off + w.size + (r - (bs.extract 0 off ++ w).size) = r := by
      rw [hAppSz]; omega
    congr 1

end Patchelf.Elf.Encoder

namespace Patchelf.Elf.Reader

open Patchelf.Elf.Encoder

/-- `readU8` is preserved across a disjoint splice. -/
theorem readU8_splice_disjoint (bs : ByteArray) (off : Nat) (w : ByteArray)
    (hSplice : off + w.size ≤ bs.size) (r : Nat) (hr : r < bs.size)
    (hDisjoint : r + 1 ≤ off ∨ off + w.size ≤ r) :
    readU8 (splice bs off w) r = readU8 bs r := by
  unfold readU8
  have hr' : r < (splice bs off w).size := by rw [splice_size]; exact hr
  rw [dif_pos hr', dif_pos hr]
  have hDisj' : r < off ∨ off + w.size ≤ r := by
    rcases hDisjoint with hl | hg
    · left; omega
    · right; exact hg
  exact splice_getElem_outside bs off w hSplice r hr hDisj'

/-- `readU16` is preserved across a disjoint splice. -/
theorem readU16_splice_disjoint (bs : ByteArray) (off : Nat) (w : ByteArray)
    (hSplice : off + w.size ≤ bs.size) (r : Nat) (hrFit : r + 2 ≤ bs.size)
    (hDisjoint : r + 2 ≤ off ∨ off + w.size ≤ r) :
    readU16 (splice bs off w) r = readU16 bs r := by
  unfold readU16
  rw [readU8_splice_disjoint bs off w hSplice r (by omega) (by
        rcases hDisjoint with hl | hg
        · left; omega
        · right; exact hg)]
  rw [readU8_splice_disjoint bs off w hSplice (r + 1) (by omega) (by
        rcases hDisjoint with hl | hg
        · left; omega
        · right; omega)]

/-- `readU32` is preserved across a disjoint splice. -/
theorem readU32_splice_disjoint (bs : ByteArray) (off : Nat) (w : ByteArray)
    (hSplice : off + w.size ≤ bs.size) (r : Nat) (hrFit : r + 4 ≤ bs.size)
    (hDisjoint : r + 4 ≤ off ∨ off + w.size ≤ r) :
    readU32 (splice bs off w) r = readU32 bs r := by
  unfold readU32
  iterate 4 rw [readU8_splice_disjoint bs off w hSplice _ (by omega) (by
    rcases hDisjoint with hl | hg
    · left; omega
    · right; omega)]

/-- `readU64` is preserved across a disjoint splice. -/
theorem readU64_splice_disjoint (bs : ByteArray) (off : Nat) (w : ByteArray)
    (hSplice : off + w.size ≤ bs.size) (r : Nat) (hrFit : r + 8 ≤ bs.size)
    (hDisjoint : r + 8 ≤ off ∨ off + w.size ≤ r) :
    readU64 (splice bs off w) r = readU64 bs r := by
  unfold readU64
  rw [readU32_splice_disjoint bs off w hSplice r (by omega) (by
        rcases hDisjoint with hl | hg
        · left; omega
        · right; exact hg)]
  rw [readU32_splice_disjoint bs off w hSplice (r + 4) (by omega) (by
        rcases hDisjoint with hl | hg
        · left; omega
        · right; omega)]

end Patchelf.Elf.Reader

namespace Patchelf.Elf.Encoder

/-- Helper: extract of zero length is empty. -/
private theorem extract_zero_zero (bs : ByteArray) : bs.extract 0 0 = ByteArray.empty := by
  apply ByteArray.ext_getElem
  · simp
  · intros _ hk _; simp at hk

/-- Pointwise byte access INSIDE the spliced region returns the splice
    payload's byte.  This is the dual of `splice_getElem_outside`. -/
private theorem splice_at_0_getElem (bs : ByteArray) (w : ByteArray)
    (hSplice : 0 + w.size ≤ bs.size) (r : Nat) (hr : r < w.size) :
    (splice bs 0 w)[r]'(by rw [splice_size]; omega) = w[r]'hr := by
  have hSpliceEq : splice bs 0 w = bs.extract 0 0 ++ w ++ bs.extract w.size bs.size := by
    unfold splice
    rw [if_pos hSplice]
    simp
  have hr' : r < (bs.extract 0 0 ++ w ++ bs.extract w.size bs.size).size := by
    rw [← hSpliceEq, splice_size]; omega
  have eq_spliced :
      (splice bs 0 w)[r]'(by rw [splice_size]; omega)
        = (bs.extract 0 0 ++ w ++ bs.extract w.size bs.size)[r]'hr' := by
    congr 1
  rw [eq_spliced]
  have hExSz : (bs.extract 0 0).size = 0 := by
    rw [ByteArray.size_extract]; omega
  have hLeftSize : (bs.extract 0 0 ++ w).size = w.size := by
    rw [ByteArray.size_append, hExSz, Nat.zero_add]
  rw [ByteArray.getElem_append_left (hlt := by rw [hLeftSize]; exact hr)]
  rw [ByteArray.getElem_append_right (hle := by rw [hExSz]; omega)]
  show w[r - (bs.extract 0 0).size]'(by rw [hExSz]; omega) = w[r]'hr
  congr 1
  rw [hExSz]; omega

/-- Pointwise byte access INSIDE the spliced region for a splice at
    arbitrary offset `off`.  Generalizes `splice_at_0_getElem`: when
    reading at `r ∈ [off, off + w.size)`, the result is `w[r - off]`. -/
private theorem splice_at_off_getElem (bs : ByteArray) (off : Nat) (w : ByteArray)
    (hSplice : off + w.size ≤ bs.size) (r : Nat) (hr : off ≤ r) (hrU : r < off + w.size) :
    (splice bs off w)[r]'(by rw [splice_size]; omega) = w[r - off]'(by omega) := by
  have hSpliceEq : splice bs off w
      = bs.extract 0 off ++ w ++ bs.extract (off + w.size) bs.size := by
    unfold splice; rw [if_pos hSplice]
  have hExSz : (bs.extract 0 off).size = off := by
    rw [ByteArray.size_extract]; omega
  have hLeftSize : (bs.extract 0 off ++ w).size = off + w.size := by
    rw [ByteArray.size_append, hExSz]
  have hr' : r < (bs.extract 0 off ++ w ++ bs.extract (off + w.size) bs.size).size := by
    rw [← hSpliceEq, splice_size]; omega
  rw [show (splice bs off w)[r]'(by rw [splice_size]; omega)
        = (bs.extract 0 off ++ w ++ bs.extract (off + w.size) bs.size)[r]'hr'
        from by congr 1]
  -- r is in the middle factor `w` (between extract-prefix and extract-suffix).
  rw [ByteArray.getElem_append_left (hlt := by rw [hLeftSize]; omega)]
  rw [ByteArray.getElem_append_right (hle := by rw [hExSz]; exact hr)]
  show w[r - (bs.extract 0 off).size]'(by rw [hExSz]; omega) = w[r - off]'(by omega)
  congr 1
  rw [hExSz]

end Patchelf.Elf.Encoder

namespace Patchelf.Elf.Reader

open Patchelf.Elf.Encoder

/-! ## Splice-at-0: reading INSIDE the spliced region returns the splice payload. -/

/-- `readU8` inside the spliced region of `splice bs 0 w` reads from `w`. -/
theorem readU8_splice_at_0_inside (bs w : ByteArray)
    (hSplice : 0 + w.size ≤ bs.size) (r : Nat) (hr : r < w.size) :
    readU8 (splice bs 0 w) r = readU8 w r := by
  unfold readU8
  have hr_spl : r < (splice bs 0 w).size := by rw [splice_size]; omega
  rw [dif_pos hr_spl, dif_pos hr]
  exact splice_at_0_getElem bs w hSplice r hr

/-! ## Splice-at-off: reading INSIDE a splice at arbitrary offset.

    Used by Tier D byte-roundtrip for the phdr / shdr / per-section
    region preservations: each region is spliced at its dedicated offset
    `off`, and reads at `r ∈ [off, off + w.size)` return the payload's
    byte at `(r - off)`. -/

/-- `readU8` inside a splice at offset `off` reads from `w` at `(r - off)`. -/
theorem readU8_splice_at_off_inside (bs : ByteArray) (off : Nat) (w : ByteArray)
    (hSplice : off + w.size ≤ bs.size) (r : Nat)
    (hr : off ≤ r) (hrU : r < off + w.size) :
    readU8 (splice bs off w) r = readU8 w (r - off) := by
  unfold readU8
  have hr_spl : r < (splice bs off w).size := by rw [splice_size]; omega
  have hrW : r - off < w.size := by omega
  rw [dif_pos hr_spl, dif_pos hrW]
  exact splice_at_off_getElem bs off w hSplice r hr hrU

/-- `readU16` inside a splice at offset `off`. -/
theorem readU16_splice_at_off_inside (bs : ByteArray) (off : Nat) (w : ByteArray)
    (hSplice : off + w.size ≤ bs.size) (r : Nat)
    (hr : off ≤ r) (hrU : r + 2 ≤ off + w.size) :
    readU16 (splice bs off w) r = readU16 w (r - off) := by
  unfold readU16
  rw [readU8_splice_at_off_inside bs off w hSplice r hr (by omega)]
  rw [readU8_splice_at_off_inside bs off w hSplice (r + 1) (by omega) (by omega)]
  rw [show r + 1 - off = (r - off) + 1 from by omega]

/-- `readU32` inside a splice at offset `off`. -/
theorem readU32_splice_at_off_inside (bs : ByteArray) (off : Nat) (w : ByteArray)
    (hSplice : off + w.size ≤ bs.size) (r : Nat)
    (hr : off ≤ r) (hrU : r + 4 ≤ off + w.size) :
    readU32 (splice bs off w) r = readU32 w (r - off) := by
  unfold readU32
  rw [readU8_splice_at_off_inside bs off w hSplice r hr (by omega)]
  rw [readU8_splice_at_off_inside bs off w hSplice (r + 1) (by omega) (by omega)]
  rw [readU8_splice_at_off_inside bs off w hSplice (r + 2) (by omega) (by omega)]
  rw [readU8_splice_at_off_inside bs off w hSplice (r + 3) (by omega) (by omega)]
  rw [show r + 1 - off = (r - off) + 1 from by omega,
      show r + 2 - off = (r - off) + 2 from by omega,
      show r + 3 - off = (r - off) + 3 from by omega]

/-- `readU64` inside a splice at offset `off`. -/
theorem readU64_splice_at_off_inside (bs : ByteArray) (off : Nat) (w : ByteArray)
    (hSplice : off + w.size ≤ bs.size) (r : Nat)
    (hr : off ≤ r) (hrU : r + 8 ≤ off + w.size) :
    readU64 (splice bs off w) r = readU64 w (r - off) := by
  unfold readU64
  rw [readU32_splice_at_off_inside bs off w hSplice r hr (by omega)]
  rw [readU32_splice_at_off_inside bs off w hSplice (r + 4) (by omega) (by omega)]
  rw [show r + 4 - off = (r - off) + 4 from by omega]

/-- `readU16` inside. -/
theorem readU16_splice_at_0_inside (bs w : ByteArray)
    (hSplice : 0 + w.size ≤ bs.size) (r : Nat) (hr : r + 2 ≤ w.size) :
    readU16 (splice bs 0 w) r = readU16 w r := by
  unfold readU16
  rw [readU8_splice_at_0_inside bs w hSplice r (by omega)]
  rw [readU8_splice_at_0_inside bs w hSplice (r + 1) (by omega)]

/-- `readU32` inside. -/
theorem readU32_splice_at_0_inside (bs w : ByteArray)
    (hSplice : 0 + w.size ≤ bs.size) (r : Nat) (hr : r + 4 ≤ w.size) :
    readU32 (splice bs 0 w) r = readU32 w r := by
  unfold readU32
  iterate 4 rw [readU8_splice_at_0_inside bs w hSplice _ (by omega)]

/-- `readU64` inside. -/
theorem readU64_splice_at_0_inside (bs w : ByteArray)
    (hSplice : 0 + w.size ≤ bs.size) (r : Nat) (hr : r + 8 ≤ w.size) :
    readU64 (splice bs 0 w) r = readU64 w r := by
  unfold readU64
  rw [readU32_splice_at_0_inside bs w hSplice r (by omega)]
  rw [readU32_splice_at_0_inside bs w hSplice (r + 4) (by omega)]

end Patchelf.Elf.Reader
