/-
  Byte-level primitives: per-width `writeUN ∘ readUN = extract`
  roundtrips, `writeArray` combinators, and the polymorphic
  `ByteWidth` bundle.

  This module is the **primitive** byte-serialization layer: it depends
  only on `Writer`/`Reader` for the LE byte codecs, plus `Serialize` for
  `writeArray` (which itself depends only on `Writer`). Every lemma here
  is ELF-structure-agnostic — it operates on raw `ByteArray` and `UIntN`
  values.

  The three per-width blocks of per-byte extraction lemmas and the
  `writeU{N}_getElem` helpers are emitted by the `byte_codec_gen`
  elaborator below.  This replaces ~400 LOC of copy-pasted scaffolding
  — N per-byte theorems per width + the N-case `writeU{N}_getElem`
  Fin-match — with one declarative invocation per width.

  The roundtrip theorems (`writeU{N}_readU{N}_extract`) remain
  hand-written because each has a different match shape: the U64
  variant handles the nested `readU32 (off + 4 + k)` form, which
  doesn't fit a uniform template.
-/

import Patchelf.Elf.Writer
import Patchelf.Elf.Reader
import Patchelf.Elf.Serialize
import Std.Tactic.BVDecide
import Lean

namespace Patchelf.Elf

open Reader Writer
open Lean Elab Command

/-! ## Per-width write_size simp lemmas -/

@[simp] theorem writeU8_size (v : UInt8) : (writeU8 v).size = 1 := rfl
@[simp] theorem writeU16_size (v : UInt16) : (writeU16 v).size = 2 := rfl
@[simp] theorem writeU32_size (v : UInt32) : (writeU32 v).size = 4 := rfl
@[simp] theorem writeU64_size (v : UInt64) : (writeU64 v).size = 8 := rfl

/-! ## Code-generating elaborator: byte_codec_gen <width>

    Emits, for a given bit-width `bw ∈ {16, 32, 64}`:

      * `readU{bw}_byte_k` for `k ∈ [0 .. bw/8)` — each byte of a
        `readU{bw}` result equals the corresponding raw `bs[...]`
        byte.  Proved via `bv_decide` after unfolding.
      * `writeU{bw}_getElem` — the i-th byte of `writeU{bw} v` equals
        the corresponding LE-shift of `v`.  Proved via term-level
        `match` + `rfl` per concrete `Fin bw/8` value.

    Writes the U64 byte lemmas for bytes 5-7 in `bs[off + 4 + (k-4)]`
    form (matching the nested `readU32` structure from `readU64`'s
    definition); the U64 roundtrip theorem below uses those forms
    directly, bridging via `have : off + k = off + 4 + (k-4)` in
    the per-case branches that need it. -/
private def buildReadByteLemma (bw : Nat) (k : Nat) :
    CommandElabM (TSyntax `command) := do
  let shift := k * 8
  let shiftLit : TSyntax `num := Syntax.mkNumLit (toString shift)
  let readUId := mkIdent (.mkSimple s!"readU{bw}")
  let thmName := mkIdent (.mkSimple s!"readU{bw}_byte_{k}")
  -- Offset form of the RHS byte.
  let rhs : TSyntax `term ←
    if k = 0 then
      `(bs[off]'h0)
    else if bw = 64 && k ≥ 5 then
      -- Bytes 5-7 of U64 use off+4+(k-4) to match the nested readU32
      -- structure — bv_decide can't bridge off+k with off+4+(k-4)
      -- through the dependent-access proof, so we keep them distinct.
      let kSub : TSyntax `num := Syntax.mkNumLit (toString (k - 4))
      `(bs[off + 4 + $kSub]'(by omega))
    else
      let kLit : TSyntax `num := Syntax.mkNumLit (toString k)
      `(bs[off + $kLit]'(by omega))
  if bw = 64 then
    `(command|
      private theorem $thmName (bs : ByteArray) (off : Nat)
          (h0 : off < bs.size) (h1 : off + 1 < bs.size)
          (h2 : off + 2 < bs.size) (h3 : off + 3 < bs.size)
          (h4 : off + 4 < bs.size)
          (h5 : off + 4 + 1 < bs.size)
          (h6 : off + 4 + 2 < bs.size)
          (h7 : off + 4 + 3 < bs.size) :
          (($readUId bs off >>> $shiftLit) &&& 0xff).toUInt8 = $rhs := by
        unfold $readUId readU32 readU8
        rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
            dif_pos h4, dif_pos h5, dif_pos h6, dif_pos h7]
        bv_decide)
  else if bw = 32 then
    `(command|
      private theorem $thmName (bs : ByteArray) (off : Nat)
          (h0 : off < bs.size) (h1 : off + 1 < bs.size)
          (h2 : off + 2 < bs.size) (h3 : off + 3 < bs.size) :
          (($readUId bs off >>> $shiftLit) &&& 0xff).toUInt8 = $rhs := by
        unfold $readUId readU8
        rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3]
        bv_decide)
  else -- bw = 16
    `(command|
      private theorem $thmName (bs : ByteArray) (off : Nat)
          (h0 : off < bs.size) (h1 : off + 1 < bs.size) :
          (($readUId bs off >>> $shiftLit) &&& 0xff).toUInt8 = $rhs := by
        unfold $readUId readU8
        rw [dif_pos h0, dif_pos h1]
        bv_decide)

/-- Build `writeU{bw}_getElem` via term-level `match` + per-case `rfl`.
    The match body is constructed by parsing a generated string (the
    shape is fixed regardless of width; only the arm count varies). -/
private def buildGetElemLemma (bw : Nat) :
    CommandElabM (TSyntax `command) := do
  let byteCount := bw / 8
  let mut branches : String := ""
  for k in [0:byteCount] do
    branches := branches ++ s!"        | ⟨{k}, _⟩ => rfl\n"
  let thmText := s!"private theorem writeU{bw}_getElem (v : UInt{bw}) (i : Fin {byteCount}) :\n" ++
                 s!"    (writeU{bw} v)[i.val]'(by show i.val < {byteCount}; exact i.isLt) =\n" ++
                 s!"      ((v >>> (8 * i.val.toUInt{bw})) &&& 0xff).toUInt8 :=\n" ++
                 s!"  match i with\n{branches}"
  let env ← getEnv
  match Parser.runParserCategory env `command thmText with
  | .ok stx => pure ⟨stx⟩
  | .error e => throwError s!"buildGetElemLemma: parse failed:\n{thmText}\n\nerror: {e}"

/-- `byte_codec_gen <w>` where `w ∈ {16, 32, 64}` emits all per-byte
    extraction lemmas + `writeU{w}_getElem` for that width. -/
elab "byte_codec_gen " w:num : command => do
  let bw := w.getNat
  unless bw = 16 || bw = 32 || bw = 64 do
    throwError "byte_codec_gen: expected 16, 32, or 64, got {bw}"
  let byteCount := bw / 8
  let mut cmds : Array (TSyntax `command) := #[]
  for k in [0:byteCount] do
    cmds := cmds.push (← buildReadByteLemma bw k)
  cmds := cmds.push (← buildGetElemLemma bw)
  cmds.forM elabCommand

/-! ## Per-byte lemmas + getElem for each width -/

byte_codec_gen 16
byte_codec_gen 32
byte_codec_gen 64

/-! ## Byte-level roundtrips: writeU{N} ∘ readU{N} = extract.

    Each theorem does an `ext_getElem` split on `Fin bw/8`, rewriting
    each byte via the corresponding `readU{bw}_byte_k` lemma.  The
    per-case body handles the `off + 0` / `off + 4 + k` normalization
    that's needed before `bv_decide` can close. -/

/-- U8 roundtrip: a 1-byte window is verbatim preserved. -/
theorem writeU8_readU8_extract (bs : ByteArray) (off : Nat)
    (h : off + 1 ≤ bs.size) :
    writeU8 (readU8 bs off) = bs.extract off (off + 1) := by
  have h0 : off < bs.size := by omega
  apply ByteArray.ext_getElem
  · rw [writeU8_size, ByteArray.size_extract]; omega
  · intro i hi _hi'
    have hi1 : i < 1 := by rw [writeU8_size] at hi; exact hi
    match i, hi1 with
    | 0, _ =>
      rw [ByteArray.getElem_extract]
      show (writeU8 (readU8 bs off))[0]'(by rw [writeU8_size]; omega) = bs[off + 0]
      unfold writeU8 readU8
      rw [dif_pos h0]
      show bs[off]'h0 = bs[off + 0]
      have : off + 0 = off := by omega
      simp [this]

theorem writeU16_readU16_extract (bs : ByteArray) (off : Nat)
    (h : off + 2 ≤ bs.size) :
    writeU16 (readU16 bs off) = bs.extract off (off + 2) := by
  have h0 : off < bs.size := by omega
  have h1 : off + 1 < bs.size := by omega
  apply ByteArray.ext_getElem
  · rw [writeU16_size, ByteArray.size_extract]; omega
  · intro i hi _hi'
    have hi2 : i < 2 := by rw [writeU16_size] at hi; exact hi
    rw [ByteArray.getElem_extract]
    rw [writeU16_getElem _ ⟨i, hi2⟩]
    match i, hi2 with
    | 0, _ => show _ = bs[off + 0]
              have heq : bs[off + 0]'(by omega) = bs[off]'h0 := by
                have : off + 0 = off := by omega
                simp [this]
              rw [heq]
              exact readU16_byte_0 bs off h0 h1
    | 1, _ => exact readU16_byte_1 bs off h0 h1

theorem writeU32_readU32_extract (bs : ByteArray) (off : Nat)
    (h : off + 4 ≤ bs.size) :
    writeU32 (readU32 bs off) = bs.extract off (off + 4) := by
  have h0 : off < bs.size := by omega
  have h1 : off + 1 < bs.size := by omega
  have h2 : off + 2 < bs.size := by omega
  have h3 : off + 3 < bs.size := by omega
  apply ByteArray.ext_getElem
  · rw [writeU32_size, ByteArray.size_extract]; omega
  · intro i hi _hi'
    have hi4 : i < 4 := by rw [writeU32_size] at hi; exact hi
    rw [ByteArray.getElem_extract]
    rw [writeU32_getElem _ ⟨i, hi4⟩]
    match i, hi4 with
    | 0, _ => show _ = bs[off + 0]
              have heq : bs[off + 0]'(by omega) = bs[off]'h0 := by
                have : off + 0 = off := by omega
                simp [this]
              rw [heq]
              exact readU32_byte_0 bs off h0 h1 h2 h3
    | 1, _ => exact readU32_byte_1 bs off h0 h1 h2 h3
    | 2, _ => exact readU32_byte_2 bs off h0 h1 h2 h3
    | 3, _ => exact readU32_byte_3 bs off h0 h1 h2 h3

theorem writeU64_readU64_extract (bs : ByteArray) (off : Nat)
    (h : off + 8 ≤ bs.size) :
    writeU64 (readU64 bs off) = bs.extract off (off + 8) := by
  have h0 : off < bs.size := by omega
  have h1 : off + 1 < bs.size := by omega
  have h2 : off + 2 < bs.size := by omega
  have h3 : off + 3 < bs.size := by omega
  have h4 : off + 4 < bs.size := by omega
  have h5 : off + 4 + 1 < bs.size := by omega
  have h6 : off + 4 + 2 < bs.size := by omega
  have h7 : off + 4 + 3 < bs.size := by omega
  apply ByteArray.ext_getElem
  · rw [writeU64_size, ByteArray.size_extract]; omega
  · intro i hi hi'
    have hi8 : i < 8 := by rw [writeU64_size] at hi; exact hi
    rw [ByteArray.getElem_extract]
    rw [writeU64_getElem _ ⟨i, hi8⟩]
    match i, hi8 with
    | 0, _ => show _ = bs[off + 0]
              have : bs[off + 0]'(by omega) = bs[off]'h0 := by
                have : off + 0 = off := by omega
                simp [this]
              rw [this]
              exact readU64_byte_0 bs off h0 h1 h2 h3 h4 h5 h6 h7
    | 1, _ => exact readU64_byte_1 bs off h0 h1 h2 h3 h4 h5 h6 h7
    | 2, _ => exact readU64_byte_2 bs off h0 h1 h2 h3 h4 h5 h6 h7
    | 3, _ => exact readU64_byte_3 bs off h0 h1 h2 h3 h4 h5 h6 h7
    | 4, _ => exact readU64_byte_4 bs off h0 h1 h2 h3 h4 h5 h6 h7
    | 5, _ => show _ = bs[off + 5]
              have : bs[off + 5]'(by omega) = bs[off + 4 + 1]'h5 := by
                have : off + 5 = off + 4 + 1 := by omega
                simp [this]
              rw [this]
              exact readU64_byte_5 bs off h0 h1 h2 h3 h4 h5 h6 h7
    | 6, _ => show _ = bs[off + 6]
              have : bs[off + 6]'(by omega) = bs[off + 4 + 2]'h6 := by
                have : off + 6 = off + 4 + 2 := by omega
                simp [this]
              rw [this]
              exact readU64_byte_6 bs off h0 h1 h2 h3 h4 h5 h6 h7
    | 7, _ => show _ = bs[off + 7]
              have : bs[off + 7]'(by omega) = bs[off + 4 + 3]'h7 := by
                have : off + 7 = off + 4 + 3 := by omega
                simp [this]
              rw [this]
              exact readU64_byte_7 bs off h0 h1 h2 h3 h4 h5 h6 h7

/-! ## Forward primitive roundtrips: `readU{N} (writeU{N} v) 0 = v`.

    These close the OTHER direction of the byte codec: writing a value
    and immediately reading it back recovers the value.  The reverse
    direction (`writeU{N} ∘ readU{N} = extract`) is above; the forward
    direction is what `DecodeRoundtripWitness` (in `ByteRoundtrip.lean`)
    needs to discharge per-struct.

    Each proof follows the same template:
      1. Unfold `readU{N}` (and its sub-readers for N≥32).
      2. Take all `dif_pos` branches via in-bounds proofs from
         `writeU{N}_size`.
      3. Reduce each `(writeU{N} v)[k]` index by `rfl` (the writer
         outputs a literal-shaped ByteArray, so direct getElem reduces).
      4. Close the bitvector identity by `bv_decide`. -/

theorem readU8_writeU8 (v : UInt8) : readU8 (writeU8 v) 0 = v := rfl

theorem readU16_writeU16 (v : UInt16) : readU16 (writeU16 v) 0 = v := by
  unfold readU16 readU8
  have h0 : (0 : Nat)     < (writeU16 v).size := by simp
  have h1 : (0 + 1 : Nat) < (writeU16 v).size := by simp
  rw [dif_pos h0, dif_pos h1]
  have e0 : (writeU16 v)[0]'h0     = (v &&& 0xff).toUInt8        := rfl
  have e1 : (writeU16 v)[0 + 1]'h1 = ((v >>> 8) &&& 0xff).toUInt8 := rfl
  rw [e0, e1]
  bv_decide

theorem readU32_writeU32 (v : UInt32) : readU32 (writeU32 v) 0 = v := by
  unfold readU32 readU8
  have h0 : (0 : Nat)     < (writeU32 v).size := by simp
  have h1 : (0 + 1 : Nat) < (writeU32 v).size := by simp
  have h2 : (0 + 2 : Nat) < (writeU32 v).size := by simp
  have h3 : (0 + 3 : Nat) < (writeU32 v).size := by simp
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3]
  have e0 : (writeU32 v)[0]'h0     = (v &&& 0xff).toUInt8         := rfl
  have e1 : (writeU32 v)[0 + 1]'h1 = ((v >>> 8) &&& 0xff).toUInt8  := rfl
  have e2 : (writeU32 v)[0 + 2]'h2 = ((v >>> 16) &&& 0xff).toUInt8 := rfl
  have e3 : (writeU32 v)[0 + 3]'h3 = ((v >>> 24) &&& 0xff).toUInt8 := rfl
  rw [e0, e1, e2, e3]
  bv_decide

theorem readU64_writeU64 (v : UInt64) : readU64 (writeU64 v) 0 = v := by
  unfold readU64 readU32 readU8
  have h0 : (0 : Nat)         < (writeU64 v).size := by simp
  have h1 : (0 + 1 : Nat)     < (writeU64 v).size := by simp
  have h2 : (0 + 2 : Nat)     < (writeU64 v).size := by simp
  have h3 : (0 + 3 : Nat)     < (writeU64 v).size := by simp
  have h4 : (0 + 4 : Nat)     < (writeU64 v).size := by simp
  have h5 : (0 + 4 + 1 : Nat) < (writeU64 v).size := by simp
  have h6 : (0 + 4 + 2 : Nat) < (writeU64 v).size := by simp
  have h7 : (0 + 4 + 3 : Nat) < (writeU64 v).size := by simp
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
      dif_pos h4, dif_pos h5, dif_pos h6, dif_pos h7]
  have e0 : (writeU64 v)[0]'h0         = (v &&& 0xff).toUInt8         := rfl
  have e1 : (writeU64 v)[0 + 1]'h1     = ((v >>> 8)  &&& 0xff).toUInt8 := rfl
  have e2 : (writeU64 v)[0 + 2]'h2     = ((v >>> 16) &&& 0xff).toUInt8 := rfl
  have e3 : (writeU64 v)[0 + 3]'h3     = ((v >>> 24) &&& 0xff).toUInt8 := rfl
  have e4 : (writeU64 v)[0 + 4]'h4     = ((v >>> 32) &&& 0xff).toUInt8 := rfl
  have e5 : (writeU64 v)[0 + 4 + 1]'h5 = ((v >>> 40) &&& 0xff).toUInt8 := rfl
  have e6 : (writeU64 v)[0 + 4 + 2]'h6 = ((v >>> 48) &&& 0xff).toUInt8 := rfl
  have e7 : (writeU64 v)[0 + 4 + 3]'h7 = ((v >>> 56) &&& 0xff).toUInt8 := rfl
  rw [e0, e1, e2, e3, e4, e5, e6, e7]
  bv_decide

/-! ## Thin aliases (`_decodeU{N}_extract`).  Kept for caller-
    compatibility; trivial renames. -/

theorem writeU16_decodeU16_extract (bs : ByteArray) (off : Nat)
    (h : off + 2 ≤ bs.size) :
    writeU16 (readU16 bs off) = bs.extract off (off + 2) :=
  writeU16_readU16_extract bs off h

theorem writeU32_decodeU32_extract (bs : ByteArray) (off : Nat)
    (h : off + 4 ≤ bs.size) :
    writeU32 (readU32 bs off) = bs.extract off (off + 4) :=
  writeU32_readU32_extract bs off h

theorem writeU64_decodeU64_extract (bs : ByteArray) (off : Nat)
    (h : off + 8 ≤ bs.size) :
    writeU64 (readU64 bs off) = bs.extract off (off + 8) :=
  writeU64_readU64_extract bs off h

/-! ## Append-getElem family: reading from a concatenated ByteArray.

    These let proofs about `readU{N} (a ++ b) off` reduce to either
    `readU{N} a off` (when `off` is in `a`'s range) or
    `readU{N} b (off - a.size)` (when `off` is in `b`'s range).

    Used by per-struct forward roundtrip proofs.  A struct serializer
    typically emits `writeU{w₁} f₁ ++ writeU{w₂} f₂ ++ …`, and decoding
    field `i` reads at offset `Σⱼ<ᵢ wⱼ`.  These lemmas split the read
    into the appropriate sub-ByteArray. -/

theorem readU8_append_left (a b : ByteArray) (off : Nat)
    (h : off < a.size) :
    Reader.readU8 (a ++ b) off = Reader.readU8 a off := by
  unfold Reader.readU8
  have h' : off < (a ++ b).size := by rw [ByteArray.size_append]; omega
  rw [dif_pos h, dif_pos h', ByteArray.getElem_append_left h]

theorem readU16_append_left (a b : ByteArray) (off : Nat)
    (h : off + 2 ≤ a.size) :
    Reader.readU16 (a ++ b) off = Reader.readU16 a off := by
  unfold Reader.readU16
  rw [readU8_append_left a b off (by omega),
      readU8_append_left a b (off + 1) (by omega)]

theorem readU32_append_left (a b : ByteArray) (off : Nat)
    (h : off + 4 ≤ a.size) :
    Reader.readU32 (a ++ b) off = Reader.readU32 a off := by
  unfold Reader.readU32
  rw [readU8_append_left a b off (by omega),
      readU8_append_left a b (off + 1) (by omega),
      readU8_append_left a b (off + 2) (by omega),
      readU8_append_left a b (off + 3) (by omega)]

theorem readU64_append_left (a b : ByteArray) (off : Nat)
    (h : off + 8 ≤ a.size) :
    Reader.readU64 (a ++ b) off = Reader.readU64 a off := by
  unfold Reader.readU64
  rw [readU32_append_left a b off (by omega),
      readU32_append_left a b (off + 4) (by omega)]

theorem readU8_append_right (a b : ByteArray) (off : Nat)
    (h : off < b.size) :
    Reader.readU8 (a ++ b) (a.size + off) = Reader.readU8 b off := by
  unfold Reader.readU8
  have h' : a.size + off < (a ++ b).size := by rw [ByteArray.size_append]; omega
  rw [dif_pos h, dif_pos h']
  rw [ByteArray.getElem_append_right (hle := by omega)]
  congr 1
  omega

theorem readU16_append_right (a b : ByteArray) (off : Nat)
    (h : off + 2 ≤ b.size) :
    Reader.readU16 (a ++ b) (a.size + off) = Reader.readU16 b off := by
  unfold Reader.readU16
  rw [readU8_append_right a b off (by omega)]
  rw [show a.size + off + 1 = a.size + (off + 1) from by omega,
      readU8_append_right a b (off + 1) (by omega)]

theorem readU32_append_right (a b : ByteArray) (off : Nat)
    (h : off + 4 ≤ b.size) :
    Reader.readU32 (a ++ b) (a.size + off) = Reader.readU32 b off := by
  unfold Reader.readU32
  rw [readU8_append_right a b off (by omega)]
  rw [show a.size + off + 1 = a.size + (off + 1) from by omega,
      readU8_append_right a b (off + 1) (by omega)]
  rw [show a.size + off + 2 = a.size + (off + 2) from by omega,
      readU8_append_right a b (off + 2) (by omega)]
  rw [show a.size + off + 3 = a.size + (off + 3) from by omega,
      readU8_append_right a b (off + 3) (by omega)]

theorem readU64_append_right (a b : ByteArray) (off : Nat)
    (h : off + 8 ≤ b.size) :
    Reader.readU64 (a ++ b) (a.size + off) = Reader.readU64 b off := by
  unfold Reader.readU64
  rw [readU32_append_right a b off (by omega)]
  rw [show a.size + off + 4 = a.size + (off + 4) from by omega,
      readU32_append_right a b (off + 4) (by omega)]

/-! ## Generic fixed-size array roundtrip

    Polymorphic combinator that lifts any per-entry byte-level roundtrip
    (`write (decode bs off) = bs.extract off (off + N)`) to an
    array-level roundtrip.

    Parameters:
    - `α`: entry type.
    - `N`: entry size in bytes (`> 0`).
    - `write : α → ByteArray` with `(write a).size = N`.
    - `decode : ByteArray → Nat → α` such that
      `write (decode bs' off') = bs'.extract off' (off' + N)` whenever
      the `N`-byte window fits in `bs'`. -/
theorem writeArray_fixed_extract {α : Type} (N : Nat)
    (write : α → ByteArray) (decode : ByteArray → Nat → α)
    (hPerEntry : ∀ bs' off', off' + N ≤ bs'.size →
      write (decode bs' off') = bs'.extract off' (off' + N))
    (bs : ByteArray) (off : Nat) (arr : Array α)
    (hFit : off + arr.size * N ≤ bs.size)
    (hEachDecoded : ∀ (i : Nat) (hi : i < arr.size),
      arr[i] = decode bs (off + i * N)) :
    writeArray write arr = bs.extract off (off + arr.size * N) := by
  suffices h : ∀ (l : List α) (accStart : Nat),
      (∀ (i : Nat) (hi : i < l.length),
        l[i] = decode bs (off + (accStart + i) * N)) →
      off + (accStart + l.length) * N ≤ bs.size →
      (l.foldl (fun acc x => acc ++ write x) ByteArray.empty) =
        bs.extract (off + accStart * N) (off + (accStart + l.length) * N) by
    have hList := h arr.toList 0 ?_ ?_
    · unfold writeArray
      rw [← Array.foldl_toList]
      rw [hList]
      rw [show off + 0 * N = off from by omega]
      rw [show (0 + arr.toList.length) * N = arr.size * N from by
        rw [Nat.zero_add, Array.length_toList]]
    · intro i hi
      have hiSz : i < arr.size := Array.length_toList ▸ hi
      have hGetEq : arr.toList[i] = arr[i]'hiSz := by
        rw [Array.getElem_toList]
      rw [hGetEq]
      have := hEachDecoded i hiSz
      rw [show (0 + i) = i from by omega]
      exact this
    · rw [show 0 + arr.toList.length = arr.size from by
        rw [Nat.zero_add, Array.length_toList]]
      exact hFit
  intro l accStart hEach hFitL
  induction l generalizing accStart with
  | nil =>
    simp only [List.foldl_nil, List.length_nil]
    rw [show accStart + 0 = accStart from by omega]
    have : bs.extract (off + accStart * N) (off + accStart * N) = ByteArray.empty :=
      ByteArray.extract_same
    exact this.symm
  | cons x xs ih =>
    simp only [List.foldl_cons, List.length_cons]
    have hX : x = decode bs (off + accStart * N) := by
      have := hEach 0 (by simp)
      simp only [List.getElem_cons_zero] at this
      rw [this, show (accStart + 0) * N = accStart * N from by
        rw [Nat.add_zero]]
    have hXsFit : off + (accStart + 1 + xs.length) * N ≤ bs.size := by
      rw [show accStart + 1 + xs.length = accStart + (xs.length + 1) from by omega]
      exact hFitL
    have hXsDecoded : ∀ (i : Nat) (hi : i < xs.length),
        xs[i] = decode bs (off + (accStart + 1 + i) * N) := by
      intro i hi
      have := hEach (i + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at this
      rw [this, show accStart + (i + 1) = accStart + 1 + i from by omega]
    have ihR := ih (accStart + 1) hXsDecoded hXsFit
    rw [hX]
    have hFitPer : off + accStart * N + N ≤ bs.size := by
      have h1 : off + accStart * N + N = off + (accStart + 1) * N := by
        rw [Nat.succ_mul]; omega
      have h2 : (accStart + 1) * N ≤ (accStart + 1 + xs.length) * N :=
        Nat.mul_le_mul_right N (by omega)
      omega
    rw [hPerEntry bs (off + accStart * N) hFitPer]
    have hFoldlAppend : ∀ (init : ByteArray) (ys : List α),
        ys.foldl (fun acc x => acc ++ write x) init =
          init ++ ys.foldl (fun acc x => acc ++ write x) ByteArray.empty := by
      intro init ys
      induction ys generalizing init with
      | nil => simp
      | cons y ys ihy =>
        simp only [List.foldl_cons]
        rw [ihy (init ++ write y)]
        rw [ihy (ByteArray.empty ++ write y)]
        rw [show (ByteArray.empty ++ write y : ByteArray) = write y from by
          exact ByteArray.empty_append]
        rw [ByteArray.append_assoc]
    rw [hFoldlAppend]
    rw [ihR]
    rw [show (ByteArray.empty : ByteArray) ++ bs.extract (off + accStart * N) (off + accStart * N + N)
        = bs.extract (off + accStart * N) (off + accStart * N + N) from by
      exact ByteArray.empty_append]
    rw [show off + accStart * N + N = off + (accStart + 1) * N from by
      rw [Nat.succ_mul]; omega]
    rw [ByteArray.extract_append_extract (a := bs) (i := off + accStart * N)
          (j := off + (accStart + 1) * N) (k := off + (accStart + 1 + xs.length) * N)]
    rw [show min (off + accStart * N) (off + (accStart + 1) * N) =
            off + accStart * N from by
      have hMonotone : accStart * N ≤ (accStart + 1) * N :=
        Nat.mul_le_mul_right N (by omega)
      omega]
    rw [show max (off + (accStart + 1) * N) (off + (accStart + 1 + xs.length) * N) =
            off + (accStart + 1 + xs.length) * N from by
      have : (accStart + 1) * N ≤ (accStart + 1 + xs.length) * N :=
        Nat.mul_le_mul_right N (by omega)
      omega]
    rw [show accStart + (xs.length + 1) = accStart + 1 + xs.length from by omega]

/-! ## Primitive-width writeArray combinators -/

/-- `writeArray writeU16` recovers a flat u16 array. Used for the
    `.gnu.version` (versym) section, which is `dynsym.size × u16`. -/
theorem writeArray_writeU16_extract (bs : ByteArray) (off : Nat)
    (arr : Array UInt16)
    (hFit : off + arr.size * 2 ≤ bs.size)
    (hEachDecoded : ∀ (i : Nat) (hi : i < arr.size),
      arr[i] = readU16 bs (off + i * 2)) :
    writeArray writeU16 arr = bs.extract off (off + arr.size * 2) :=
  writeArray_fixed_extract 2 writeU16 readU16
    (fun bs' off' h => writeU16_decodeU16_extract bs' off' h)
    bs off arr hFit hEachDecoded

/-- `writeArray writeU32` recovers a flat u32 array. -/
theorem writeArray_writeU32_extract (bs : ByteArray) (off : Nat)
    (arr : Array UInt32)
    (hFit : off + arr.size * 4 ≤ bs.size)
    (hEachDecoded : ∀ (i : Nat) (hi : i < arr.size),
      arr[i] = readU32 bs (off + i * 4)) :
    writeArray writeU32 arr = bs.extract off (off + arr.size * 4) :=
  writeArray_fixed_extract 4 writeU32 readU32
    (fun bs' off' h => writeU32_decodeU32_extract bs' off' h)
    bs off arr hFit hEachDecoded

/-- `writeArray writeU64` recovers a flat u64 array. Used for the
    GNU hash table's bloom filter (`maskwords × u64`). -/
theorem writeArray_writeU64_extract (bs : ByteArray) (off : Nat)
    (arr : Array UInt64)
    (hFit : off + arr.size * 8 ≤ bs.size)
    (hEachDecoded : ∀ (i : Nat) (hi : i < arr.size),
      arr[i] = readU64 bs (off + i * 8)) :
    writeArray writeU64 arr = bs.extract off (off + arr.size * 8) :=
  writeArray_fixed_extract 8 writeU64 readU64
    (fun bs' off' h => writeU64_decodeU64_extract bs' off' h)
    bs off arr hFit hEachDecoded

/-! ## Forward array codec roundtrip: `readU{N} (writeArray writeU{N} arr) (i*N) = arr[i]`.

    Together with the append-getElem family, this completes the forward
    direction needed for variable-length structs (SysVHashTable,
    GnuHashTable, Verneed) to have forward roundtrips.

    Proof: strong induction on `arr.size`, peeling the last element via
    `Array.pop`/`writeArray_push`, and dispatching by whether the read
    index lies in the popped prefix or is the new last element. -/

theorem writeArray_push {α} (f : α → ByteArray) (l : Array α) (x : α) :
    writeArray f (l.push x) = writeArray f l ++ f x := by
  unfold writeArray
  rw [Array.foldl_push]

/-! ## writeArray extract-at-index for uniform-width writers

    For any uniform-width writer `f : α → ByteArray` (size `N` for every
    input), the extract of `writeArray f arr` at offset `i * N` of width
    `N` recovers `f arr[i]`.  Built via `Array.pop`/`writeArray_push`
    induction directly at the extract level (no per-byte detour). -/
private theorem writeArray_uniform_extract_aux {α} (N : Nat)
    (f : α → ByteArray) (hUniform : ∀ x, (f x).size = N) :
    ∀ (n : Nat) (arr : Array α) (_ : arr.size = n)
      (i : Nat) (hi : i < arr.size),
      (writeArray f arr).extract (i * N) (i * N + N) = f (arr[i]'hi) := by
  intro n
  induction n with
  | zero => intros; omega
  | succ k ih =>
    intros arr hSize i hi
    have hPopSize : arr.pop.size = k := by simp [Array.size_pop, hSize]
    have hLastIdx : k < arr.size := by omega
    have hReconstruct : arr.pop.push (arr[k]'hLastIdx) = arr := by
      apply Array.ext
      · simp [Array.size_push, hPopSize, hSize]
      · intros j' hj' _
        rw [Array.size_push, hPopSize] at hj'
        rw [Array.getElem_push]
        split
        · rw [Array.getElem_pop]
        · have : j' = k := by omega
          subst this; rfl
    have hwa : writeArray f arr =
        writeArray f arr.pop ++ f (arr[k]'hLastIdx) := by
      conv => lhs; rw [← hReconstruct]
      exact writeArray_push f arr.pop (arr[k]'hLastIdx)
    have hPopBytes : (writeArray f arr.pop).size = k * N := by
      rw [writeArray_size_of_uniform f N hUniform, hPopSize]
    have hLastSz : (f (arr[k]'hLastIdx)).size = N := hUniform _
    by_cases hi' : i < arr.pop.size
    · -- Index in the prefix; window lies inside left factor of append.
      have ihEq := ih arr.pop hPopSize i (hPopSize ▸ hi')
      have hPopElem : arr.pop[i]'hi' = arr[i]'hi := Array.getElem_pop hi'
      rw [hPopElem] at ihEq
      rw [hwa]
      -- (a ++ b).extract (i*N) (i*N + N) = a.extract (i*N) (i*N + N)
      -- when i*N + N ≤ a.size.
      rw [ByteArray.extract_append]
      have hUpper : i * N + N ≤ (writeArray f arr.pop).size := by
        rw [hPopBytes]
        have hiLt : i < k := hPopSize ▸ hi'
        have hSucc : i + 1 ≤ k := hiLt
        have : (i + 1) * N ≤ k * N := Nat.mul_le_mul_right N hSucc
        rw [Nat.succ_mul] at this; omega
      rw [show (i * N - (writeArray f arr.pop).size : Nat) = 0 from by
            rw [hPopBytes]; omega,
          show (i * N + N - (writeArray f arr.pop).size : Nat) = 0 from by
            rw [hPopBytes]; omega,
          ByteArray.extract_same, ByteArray.append_empty]
      exact ihEq
    · -- i = k: window is entirely in the right factor.
      have hiEq : i = k := by rw [hPopSize] at hi'; omega
      subst hiEq
      rw [hwa]
      apply ByteArray.ext_getElem
      · rw [ByteArray.size_extract, ByteArray.size_append, hLastSz, hPopBytes]
        omega
      · intros j hj _
        rw [ByteArray.size_extract, ByteArray.size_append, hLastSz,
            hPopBytes] at hj
        have hjN : j < N := by omega
        rw [ByteArray.getElem_extract]
        rw [ByteArray.getElem_append_right (hle := by rw [hPopBytes]; omega)]
        have hRem : i * N + j - (writeArray f arr.pop).size = j := by
          rw [hPopBytes]; omega
        congr 1

/-- Window-extract of `writeArray f arr` at the i-th element's slot equals
    `f arr[i]`, for any uniform-width writer. -/
theorem writeArray_uniform_extract_at_index {α} (N : Nat)
    (f : α → ByteArray) (hUniform : ∀ x, (f x).size = N)
    (arr : Array α) (i : Nat) (hi : i < arr.size) :
    (writeArray f arr).extract (i * N) (i * N + N) = f (arr[i]'hi) :=
  writeArray_uniform_extract_aux N f hUniform arr.size arr rfl i hi

private theorem readU32_writeArray_aux : ∀ (n : Nat) (arr : Array UInt32) (_ : arr.size = n)
    (i : Nat) (hi : i < arr.size),
    Reader.readU32 (writeArray writeU32 arr) (i * 4) = arr[i] := by
  intro n
  induction n with
  | zero => intros; omega
  | succ k ih =>
    intros arr hSize i hi
    have hPopSize : arr.pop.size = k := by simp [Array.size_pop, hSize]
    have hLastIdx : k < arr.size := by omega
    have hReconstruct : arr.pop.push (arr[k]'hLastIdx) = arr := by
      apply Array.ext
      · simp [Array.size_push, hPopSize, hSize]
      · intros j hj _
        rw [Array.size_push, hPopSize] at hj
        rw [Array.getElem_push]
        split
        · rw [Array.getElem_pop]
        · have : j = k := by omega
          subst this; rfl
    have hwa : writeArray writeU32 arr =
        writeArray writeU32 arr.pop ++ writeU32 (arr[k]'hLastIdx) := by
      conv => lhs; rw [← hReconstruct]
      exact writeArray_push writeU32 arr.pop (arr[k]'hLastIdx)
    rw [hwa]
    by_cases hi' : i < arr.pop.size
    · rw [readU32_append_left _ _ (i * 4) (by
        rw [writeArray_size_of_uniform writeU32 4 (fun _ => writeU32_size _) arr.pop]
        omega)]
      have hLhs := ih arr.pop hPopSize i (hPopSize ▸ hi')
      rw [hLhs]
      simp [Array.getElem_pop]
    · have hieq : i = k := by simp [hPopSize] at hi'; omega
      have hi_eq_arr : arr[i]'hi = arr[k]'hLastIdx := by simp [hieq]
      rw [hi_eq_arr, show i * 4 = k * 4 from by rw [hieq]]
      rw [show (k * 4 : Nat) = (writeArray writeU32 arr.pop).size + 0 from by
            simp [writeArray_size_of_uniform writeU32 4 (fun _ => writeU32_size _) arr.pop, hPopSize]]
      rw [readU32_append_right _ _ 0 (by simp), readU32_writeU32]

theorem readU32_writeArray (arr : Array UInt32) (i : Nat) (hi : i < arr.size) :
    Reader.readU32 (writeArray writeU32 arr) (i * 4) = arr[i] :=
  readU32_writeArray_aux arr.size arr rfl i hi

private theorem readU64_writeArray_aux : ∀ (n : Nat) (arr : Array UInt64) (_ : arr.size = n)
    (i : Nat) (hi : i < arr.size),
    Reader.readU64 (writeArray writeU64 arr) (i * 8) = arr[i] := by
  intro n
  induction n with
  | zero => intros; omega
  | succ k ih =>
    intros arr hSize i hi
    have hPopSize : arr.pop.size = k := by simp [Array.size_pop, hSize]
    have hLastIdx : k < arr.size := by omega
    have hReconstruct : arr.pop.push (arr[k]'hLastIdx) = arr := by
      apply Array.ext
      · simp [Array.size_push, hPopSize, hSize]
      · intros j hj _
        rw [Array.size_push, hPopSize] at hj
        rw [Array.getElem_push]
        split
        · rw [Array.getElem_pop]
        · have : j = k := by omega
          subst this; rfl
    have hwa : writeArray writeU64 arr =
        writeArray writeU64 arr.pop ++ writeU64 (arr[k]'hLastIdx) := by
      conv => lhs; rw [← hReconstruct]
      exact writeArray_push writeU64 arr.pop (arr[k]'hLastIdx)
    rw [hwa]
    by_cases hi' : i < arr.pop.size
    · rw [readU64_append_left _ _ (i * 8) (by
        rw [writeArray_size_of_uniform writeU64 8 (fun _ => writeU64_size _) arr.pop]
        omega)]
      have hLhs := ih arr.pop hPopSize i (hPopSize ▸ hi')
      rw [hLhs]
      simp [Array.getElem_pop]
    · have hieq : i = k := by simp [hPopSize] at hi'; omega
      have hi_eq_arr : arr[i]'hi = arr[k]'hLastIdx := by simp [hieq]
      rw [hi_eq_arr, show i * 8 = k * 8 from by rw [hieq]]
      rw [show (k * 8 : Nat) = (writeArray writeU64 arr.pop).size + 0 from by
            simp [writeArray_size_of_uniform writeU64 8 (fun _ => writeU64_size _) arr.pop, hPopSize]]
      rw [readU64_append_right _ _ 0 (by simp), readU64_writeU64]

theorem readU64_writeArray (arr : Array UInt64) (i : Nat) (hi : i < arr.size) :
    Reader.readU64 (writeArray writeU64 arr) (i * 8) = arr[i] :=
  readU64_writeArray_aux arr.size arr rfl i hi

private theorem readU16_writeArray_aux : ∀ (n : Nat) (arr : Array UInt16) (_ : arr.size = n)
    (i : Nat) (hi : i < arr.size),
    Reader.readU16 (writeArray writeU16 arr) (i * 2) = arr[i] := by
  intro n
  induction n with
  | zero => intros; omega
  | succ k ih =>
    intros arr hSize i hi
    have hPopSize : arr.pop.size = k := by simp [Array.size_pop, hSize]
    have hLastIdx : k < arr.size := by omega
    have hReconstruct : arr.pop.push (arr[k]'hLastIdx) = arr := by
      apply Array.ext
      · simp [Array.size_push, hPopSize, hSize]
      · intros j hj _
        rw [Array.size_push, hPopSize] at hj
        rw [Array.getElem_push]
        split
        · rw [Array.getElem_pop]
        · have : j = k := by omega
          subst this; rfl
    have hwa : writeArray writeU16 arr =
        writeArray writeU16 arr.pop ++ writeU16 (arr[k]'hLastIdx) := by
      conv => lhs; rw [← hReconstruct]
      exact writeArray_push writeU16 arr.pop (arr[k]'hLastIdx)
    rw [hwa]
    by_cases hi' : i < arr.pop.size
    · rw [readU16_append_left _ _ (i * 2) (by
        rw [writeArray_size_of_uniform writeU16 2 (fun _ => writeU16_size _) arr.pop]
        omega)]
      have hLhs := ih arr.pop hPopSize i (hPopSize ▸ hi')
      rw [hLhs]
      simp [Array.getElem_pop]
    · have hieq : i = k := by simp [hPopSize] at hi'; omega
      have hi_eq_arr : arr[i]'hi = arr[k]'hLastIdx := by simp [hieq]
      rw [hi_eq_arr, show i * 2 = k * 2 from by rw [hieq]]
      rw [show (k * 2 : Nat) = (writeArray writeU16 arr.pop).size + 0 from by
            simp [writeArray_size_of_uniform writeU16 2 (fun _ => writeU16_size _) arr.pop, hPopSize]]
      rw [readU16_append_right _ _ 0 (by simp), readU16_writeU16]

theorem readU16_writeArray (arr : Array UInt16) (i : Nat) (hi : i < arr.size) :
    Reader.readU16 (writeArray writeU16 arr) (i * 2) = arr[i] :=
  readU16_writeArray_aux arr.size arr rfl i hi

/-! ## ByteWidth bundle

    Packs (size, write, read, write_size, roundtrip) for a fixed-width
    byte-level primitive/struct. `writeArray_of_width` lifts any such
    bundle to the full array-level roundtrip. -/

structure ByteWidth (α : Type) where
  size       : Nat
  sizePos    : 0 < size
  write      : α → ByteArray
  read       : ByteArray → Nat → α
  write_size : ∀ a, (write a).size = size
  roundtrip  : ∀ bs off, off + size ≤ bs.size →
                 write (read bs off) = bs.extract off (off + size)

/-- Array lift for any `ByteWidth α`. Thin shim over
    `writeArray_fixed_extract`. -/
theorem writeArray_of_width {α : Type} (W : ByteWidth α)
    (bs : ByteArray) (off : Nat) (arr : Array α)
    (hFit : off + arr.size * W.size ≤ bs.size)
    (hEach : ∀ (i : Nat) (hi : i < arr.size),
      arr[i] = W.read bs (off + i * W.size)) :
    writeArray W.write arr = bs.extract off (off + arr.size * W.size) :=
  writeArray_fixed_extract W.size W.write W.read
    W.roundtrip bs off arr hFit hEach

/-! ### Primitive instances: u16 / u32 / u64 -/

def ByteWidth.u16 : ByteWidth UInt16 where
  size       := 2
  sizePos    := by decide
  write      := writeU16
  read       := readU16
  write_size := writeU16_size
  roundtrip  := writeU16_readU16_extract

def ByteWidth.u32 : ByteWidth UInt32 where
  size       := 4
  sizePos    := by decide
  write      := writeU32
  read       := readU32
  write_size := writeU32_size
  roundtrip  := writeU32_readU32_extract

def ByteWidth.u64 : ByteWidth UInt64 where
  size       := 8
  sizePos    := by decide
  write      := writeU64
  read       := readU64
  write_size := writeU64_size
  roundtrip  := writeU64_readU64_extract

/-! ## readU{N} on extract: bridging buffer-with-offset to window-from-zero

    A read at `(off + k)` of a buffer equals a read at `k` of the
    `extract off (off + len)` window, when `k + N ≤ len` (so the read
    fits in the window).  Used to prove decoders' window-only
    dependence is reflected in their byte access. -/

theorem readU8_extract_eq (bs : ByteArray) (off len k : Nat)
    (h : k + 1 ≤ len) (hFit : off + len ≤ bs.size) :
    Reader.readU8 bs (off + k) = Reader.readU8 (bs.extract off (off + len)) k := by
  unfold Reader.readU8
  have hLT_bs : off + k < bs.size := by omega
  have hExtSz : (bs.extract off (off + len)).size = len := by
    rw [ByteArray.size_extract]; omega
  have hLT_ext : k < (bs.extract off (off + len)).size := by rw [hExtSz]; omega
  rw [dif_pos hLT_bs, dif_pos hLT_ext, ByteArray.getElem_extract]

theorem readU16_extract_eq (bs : ByteArray) (off len k : Nat)
    (h : k + 2 ≤ len) (hFit : off + len ≤ bs.size) :
    Reader.readU16 bs (off + k) = Reader.readU16 (bs.extract off (off + len)) k := by
  unfold Reader.readU16
  rw [readU8_extract_eq bs off len k (by omega) hFit,
      show off + k + 1 = off + (k + 1) from by omega,
      readU8_extract_eq bs off len (k + 1) (by omega) hFit]

theorem readU32_extract_eq (bs : ByteArray) (off len k : Nat)
    (h : k + 4 ≤ len) (hFit : off + len ≤ bs.size) :
    Reader.readU32 bs (off + k) = Reader.readU32 (bs.extract off (off + len)) k := by
  unfold Reader.readU32
  rw [readU8_extract_eq bs off len k (by omega) hFit,
      show off + k + 1 = off + (k + 1) from by omega,
      readU8_extract_eq bs off len (k + 1) (by omega) hFit,
      show off + k + 2 = off + (k + 2) from by omega,
      readU8_extract_eq bs off len (k + 2) (by omega) hFit,
      show off + k + 3 = off + (k + 3) from by omega,
      readU8_extract_eq bs off len (k + 3) (by omega) hFit]

theorem readU64_extract_eq (bs : ByteArray) (off len k : Nat)
    (h : k + 8 ≤ len) (hFit : off + len ≤ bs.size) :
    Reader.readU64 bs (off + k) = Reader.readU64 (bs.extract off (off + len)) k := by
  unfold Reader.readU64
  rw [readU32_extract_eq bs off len k (by omega) hFit,
      show off + k + 4 = off + (k + 4) from by omega,
      readU32_extract_eq bs off len (k + 4) (by omega) hFit]

/-! ## Window-form extract-of-extract.

    `(bs.extract a (a+M)).extract c (c+W) = bs.extract (a+c) (a+c+W)`
    when the inner window fits in the outer.  Used by Tier D byte-
    roundtrip to bridge per-element windows: from `extract_encode_eq_<region>_writer`,
    the i-th element's window in the encoder equals the i-th element's
    window in the writeArray. -/
theorem ByteArray.extract_extract_window (bs : ByteArray) (a M c W : Nat)
    (hOuter : a + M ≤ bs.size) (hInner : c + W ≤ M) :
    (bs.extract a (a + M)).extract c (c + W) = bs.extract (a + c) (a + c + W) := by
  apply ByteArray.ext_getElem
  · rw [ByteArray.size_extract, ByteArray.size_extract, ByteArray.size_extract]
    omega
  · intros i hi _
    rw [ByteArray.size_extract, ByteArray.size_extract] at hi
    rw [ByteArray.getElem_extract, ByteArray.getElem_extract,
        ByteArray.getElem_extract]
    congr 1
    omega

/-! ## Prefix-bounded extract: drop the right factor when the window
    fits in the left.

    `(a ++ b).extract 0 j = a.extract 0 j` when `j ≤ a.size`.

    Used to peel through writer chains like `ElfHeader.write` whose
    leftmost factor (e.g. ElfIdent.write) contains the bytes we
    want to read.  Each peel costs O(1) kernel work, vs. the
    simp-based approach which navigates the full ++ chain. -/
theorem ByteArray.extract_append_left_within (a b : ByteArray) (j : Nat) (hj : j ≤ a.size) :
    (a ++ b).extract 0 j = a.extract 0 j := by
  rw [ByteArray.extract_append]
  rw [show (0 - a.size : Nat) = 0 from by omega,
      show (j - a.size : Nat) = 0 from by omega,
      ByteArray.extract_same, ByteArray.append_empty]

/-! ## ByteArray.extract helpers used by raw_bytes-field forward proofs -/

/-- An out-of-bounds extract is empty.  Used in `raw_bytes` field
    reductions for forward roundtrip proofs of schemas with
    `raw_bytes N with_size_field sf` fields (e.g. `ElfIdent`'s
    `head` and `tail`).  When the extract window starts past the
    end of `a`, no bytes can be read. -/
theorem ByteArray.extract_empty_of_size_le (a : ByteArray) (i j : Nat)
    (h : a.size ≤ i) : a.extract i j = ByteArray.empty := by
  apply ByteArray.ext_getElem
  · simp only [ByteArray.size_extract, ByteArray.size_empty]; omega
  · intros _ hk _
    simp only [ByteArray.size_extract] at hk
    omega

/-! ## `merge_extract_at` — pairwise extract-merge tactic

    Composite rewrite used by the variable-length byte-roundtrip
    proofs (SysVHashTable / GnuHashTable).  The proofs end with a
    chain of adjacent `bs.extract a b ++ bs.extract b c` windows
    that must collapse into `bs.extract a c` via
    `ByteArray.extract_append_extract` + arithmetic normalization
    of the resulting `min`/`max` expressions.  A single invocation

        merge_extract_at bs, i, j, k

    applies the lemma at window (i, j, k) and closes the `min i j = i`
    and `max j k = k` side-goals via `omega`.  Saves 3 LOC per
    merge; a typical variable-length roundtrip has 3-6 merges. -/
macro "merge_extract_at" bs:term "," i:term "," j:term "," k:term : tactic =>
  `(tactic| (
    rw [ByteArray.extract_append_extract (a := $bs) (i := $i) (j := $j) (k := $k)]
    rw [show min $i $j = $i from by omega]
    rw [show max $j $k = $k from by omega]))

end Patchelf.Elf
