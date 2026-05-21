/-
  ByteArray → integer primitives (little-endian).

  Out-of-bounds reads return 0 (Lean stdlib convention). Callers must
  bounds-check before relying on the returned value.
-/
module

@[expose] public section

namespace Patchelf.Elf.Reader

/-- Read a single byte; returns 0 if `off ≥ bs.size`. -/
def readU8 (bs : ByteArray) (off : Nat) : UInt8 :=
  if h : off < bs.size then bs[off]'h else 0

/-- In-bounds `readU8` is just `getElem`.  Used to bridge byte-level
    invariants stated as `readU8 bs i = v` to `bs[i]'h = v` form. -/
theorem readU8_eq_getElem (bs : ByteArray) (i : Nat) (h : i < bs.size) :
    readU8 bs i = bs[i]'h := by
  unfold readU8; rw [dif_pos h]

/-- Read 2 bytes LE. -/
def readU16 (bs : ByteArray) (off : Nat) : UInt16 :=
  let b0 := (readU8 bs off).toUInt16
  let b1 := (readU8 bs (off + 1)).toUInt16
  b0 ||| (b1 <<< 8)

/-- Read 4 bytes LE. -/
def readU32 (bs : ByteArray) (off : Nat) : UInt32 :=
  let b0 := (readU8 bs off).toUInt32
  let b1 := (readU8 bs (off + 1)).toUInt32
  let b2 := (readU8 bs (off + 2)).toUInt32
  let b3 := (readU8 bs (off + 3)).toUInt32
  b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)

/-- Read 8 bytes LE. -/
def readU64 (bs : ByteArray) (off : Nat) : UInt64 :=
  let lo := (readU32 bs off).toUInt64
  let hi := (readU32 bs (off + 4)).toUInt64
  lo ||| (hi <<< 32)

/-- Read `len` bytes starting at `off`. If out-of-bounds, returns a
    shorter slice. Use `inBounds` first if you need the full `len`. -/
def readBytes (bs : ByteArray) (off len : Nat) : ByteArray :=
  bs.extract off (off + len)

/-- Size of a `readBytes` result when the range is in-bounds. -/
theorem readBytes_size (bs : ByteArray) (off len : Nat)
    (h : off + len ≤ bs.size) : (readBytes bs off len).size = len := by
  unfold readBytes
  simp [ByteArray.size_extract]
  omega

end Patchelf.Elf.Reader
