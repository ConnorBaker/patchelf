/-
  Integer → ByteArray primitives (little-endian).

  Each writer returns a ByteArray of the fixed field width.

  Per-struct (ElfHeader, ProgramHeader, ...) serializers live in
  `Serialize.lean`; this file stays focused on bit-level LE encoding.
-/

namespace Patchelf.Elf.Writer

/-- 1-byte encoding. -/
def writeU8 (v : UInt8) : ByteArray :=
  ⟨#[v]⟩

/-- 2-byte LE encoding. -/
def writeU16 (v : UInt16) : ByteArray :=
  let b0 := (v &&& 0xff).toUInt8
  let b1 := ((v >>> 8) &&& 0xff).toUInt8
  ⟨#[b0, b1]⟩

/-- 4-byte LE encoding. -/
def writeU32 (v : UInt32) : ByteArray :=
  let b0 := (v &&& 0xff).toUInt8
  let b1 := ((v >>> 8) &&& 0xff).toUInt8
  let b2 := ((v >>> 16) &&& 0xff).toUInt8
  let b3 := ((v >>> 24) &&& 0xff).toUInt8
  ⟨#[b0, b1, b2, b3]⟩

/-- 8-byte LE encoding. -/
def writeU64 (v : UInt64) : ByteArray :=
  let b0 := (v &&& 0xff).toUInt8
  let b1 := ((v >>> 8) &&& 0xff).toUInt8
  let b2 := ((v >>> 16) &&& 0xff).toUInt8
  let b3 := ((v >>> 24) &&& 0xff).toUInt8
  let b4 := ((v >>> 32) &&& 0xff).toUInt8
  let b5 := ((v >>> 40) &&& 0xff).toUInt8
  let b6 := ((v >>> 48) &&& 0xff).toUInt8
  let b7 := ((v >>> 56) &&& 0xff).toUInt8
  ⟨#[b0, b1, b2, b3, b4, b5, b6, b7]⟩

end Patchelf.Elf.Writer
