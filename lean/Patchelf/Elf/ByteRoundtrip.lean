/-
  ByteRoundtrip: Tier D master theorem for the byte-layer codec.

  Goal: `parse (encode e.elf) = .ok e` for every `e : ParsedElf`.

  ## What this file delivers, NO `sorry`s

  1. **`encode_size_eq`** — unconditional: the encoded byte array has
     size exactly `encodedFileSize e`.  Every splice in the encode
     pipeline is size-preserving (via the pre-existing `splice_size`
     family); the initial `zeroBytes (encodedFileSize e)` seeds the
     correct total.

  2. **`DecodeRoundtripWitness`** — a typed precondition bundle that
     names the four decoder-inverse facts the master theorem needs:
       * `parseHeader` succeeds on `encode e` and returns `e.header`;
       * `decodePhdrs` on `encode e` at `e.header.phoff` equals
         `e.phdrs`;
       * `decodeShdrs` on `encode e` at `e.header.shoff` equals the
         shdr-projection of `e.sections`;
       * `decodeSectionContent` on `encode e` at each shdr recovers
         the corresponding section's `content`.

  3. **`parse_encode_roundtrip`** — the master theorem, conditional on
     the `DecodeRoundtripWitness` bundle: `parse (encode e.elf) = .ok e`.
     The proof unfolds `parse`, substitutes each decoder call with its
     bundle-provided value, reassembles `e.elf`, and closes the final
     `IsValid` branch via `e.isValid`.

  ## What the bundle assumes

  Each bundle field is a concrete decode-on-encode-equals-original
  equation.  Discharging them in full reduces to proving
  `decode ∘ write = id` for each ELF sub-structure (`ElfHeader`,
  `ProgramHeader`, `SectionHeader`, `DynEntry`, `Symbol`, `StringTable`,
  `Verneed`, `SysVHashTable`, `GnuHashTable`, `UInt16` versym entries).
  Existing infrastructure (`Schemas.lean` + `ByteLevel.lean`) proves
  the **reverse** direction uniformly via the DSL
  (`write ∘ decode = extract`); producing the forward direction is a
  follow-up equivalent to ~8 per-struct bv_decide-grade theorems.

  Expressing the obligation as a typed bundle makes the gap auditable
  (every caller of `parse_encode_roundtrip` must produce a witness),
  keeps this file sorry-free, and leaves the structural proof — the
  part that doesn't depend on per-struct byte-roundtrips — fully
  unconditional and reusable.

  ## Dependencies & safety

  * No modifications to `ElfFile.lean`, `Parser.lean`,
    `Encoder.lean`, `Schemas.lean`, or `SectionOps.lean`.
  * No `sorry`s.
  * All lemmas discharge via existing `splice_size`, DSL-generated
    size lemmas, and the hypotheses bundled in
    `DecodeRoundtripWitness`.
-/

import Patchelf.Elf.ElfFile
import Patchelf.Elf.Parser
import Patchelf.Elf.Encoder
import Patchelf.Elf.Tactic.SpliceSimproc

namespace Patchelf.Elf

open Layout
open Patchelf.Elf (ElfHeader DynEntry Symbol Verneed SysVHashTable
                     GnuHashTable StringTable SectionHeader ProgramHeader
                     ParseError)
open Patchelf.Elf.Writer
open Patchelf.Elf.Encoder

/-! ## Encode size characterization -/

/-- The encoded byte array has size exactly `encodedFileSize e`.

    Each step of `encode`'s pipeline is size-preserving:
      * `zeroBytes n` has size `n` (by `zeroBytes_size`);
      * every `splice` preserves input size (`splice_size`);
      * the per-section `foldl` either skips (identity) or splices
        (size-preserving).

    No `IsValid` / `IsLoadable` hypothesis is needed — the size
    contract is structural on the encoder's pipeline shape. -/
theorem encode_size_eq (e : ElfFile) :
    (encode e).size = encodedFileSize
      (let e1 := syncDtStrszInFile e
       if layoutAlreadyValid e1 then e1 else layoutForEncoding e1) := by
  unfold encode encodeBody
  -- After the three header-class splices, the running buffer has size
  -- `encodedFileSize e` (by `zeroBytes_size` + three `splice_size`).
  -- The per-section foldl preserves this.
  have hFold : ∀ (buf : ByteArray) (ss : Array Section),
      (ss.foldl (init := buf) sectionFoldStep).size = buf.size := by
    intro buf ss
    have := @Array.foldl_induction Section ByteArray ss
      (motive := fun (_ : Nat) (b : ByteArray) => b.size = buf.size)
      (init := buf) rfl
      (f := sectionFoldStep)
      (by
        intro i b hb
        unfold sectionFoldStep
        split
        · exact hb
        · rw [splice_size]; exact hb)
    exact this
  rw [hFold, splice_size, splice_size, splice_size, zeroBytes_size]

/-! ## Per-region readU{N} preservation through encode

    For an `e` satisfying `syncDtStrszInFile e = e ∧ layoutAlreadyValid e =
    true ∧ e.spliceRegionsDisjoint`, the bytes at offsets in each splice
    region of `(encode e)` recover the splice payload.  Reasoning chain
    per region (e.g. header at `[0, ehdrSize)`):
      1. `encode e = encodeBody e` (pre-passes are no-ops).
      2. `readU{N} (sections.foldl _) r = readU{N} buf3 r` via
         `readU{N}_foldl_section_splice_preserved` (sections disjoint
         from header).
      3. `readU{N} buf3 r = readU{N} buf2 r` via `readU{N}_splice_disjoint`
         (shdr region disjoint from header).
      4. `readU{N} buf2 r = readU{N} buf1 r` via `readU{N}_splice_disjoint`
         (phdr region disjoint from header).
      5. `readU{N} buf1 r = readU{N} hdrW r` via `readU{N}_splice_at_0_inside`
         (header is the splice payload at offset 0).

    These 4 lemmas (header / phdr / shdr / section regions) feed the
    `DecodeRoundtripWitness` discharges below. -/

private theorem readU8_encode_in_header (e : ElfFile)
    (hSync : syncDtStrszInFile e = e)
    (hLay : layoutAlreadyValid e = true)
    (hDisj : e.spliceRegionsDisjoint)
    (r : Nat) (hr : r + 1 ≤ Layout.ehdrSize) :
    Reader.readU8 (encode e) r
      = Reader.readU8 (ElfHeader.write e.header) r := by
  -- Drive `encode e` to its `encodeBody` form by discharging the pre-passes.
  have hEnc : encode e = encodeBody e := by
    unfold encode; rw [hSync]; simp [hLay]
  rw [hEnc]
  unfold encodeBody
  -- Buffer aliases (definitional; no `set`-based metavars).
  let total := encodedFileSize e
  let buf0 : ByteArray := zeroBytes total
  let hdrW : ByteArray := ElfHeader.write e.header
  let buf1 : ByteArray := splice buf0 0 hdrW
  let phdrW : ByteArray := writeArray ProgramHeader.write e.phdrs
  let phoff := e.header.phoff.val
  let buf2 : ByteArray := splice buf1 phoff phdrW
  let shdrW : ByteArray := writeArray SectionHeader.write (e.sections.map toShdr)
  let shoff := e.header.shoff.val
  let buf3 : ByteArray := splice buf2 shoff shdrW
  -- Sizes.
  have hBuf0Sz : buf0.size = total := zeroBytes_size total
  have hBuf1Sz : buf1.size = total := by show (splice _ _ _).size = _; rw [splice_size]; exact hBuf0Sz
  have hBuf2Sz : buf2.size = total := by show (splice _ _ _).size = _; rw [splice_size]; exact hBuf1Sz
  have hBuf3Sz : buf3.size = total := by show (splice _ _ _).size = _; rw [splice_size]; exact hBuf2Sz
  have hHdrWSz : hdrW.size = Layout.ehdrSize := ElfHeader.write_size e.header
  have hPhdrWSz : phdrW.size = e.phdrs.size * Layout.phdrSize :=
    writeArray_size_of_uniform ProgramHeader.write Layout.phdrSize
            ProgramHeader.write_size e.phdrs
  have hShdrWSz : shdrW.size = e.sections.size * Layout.shdrSize := by
    show (writeArray _ _).size = _
    rw [writeArray_size_of_uniform SectionHeader.write Layout.shdrSize
            SectionHeader.write_size, Array.size_map]
  -- Region bounds.
  have hTotalEhdr : Layout.ehdrSize ≤ total := encodedFileSize_ge_ehdr e
  have hPhdrEnd : phoff + e.phdrs.size * Layout.phdrSize ≤ total :=
    phdr_end_le_encodedFileSize e
  have hShdrEnd : shoff + e.sections.size * Layout.shdrSize ≤ total :=
    shdr_end_le_encodedFileSize e
  -- Splice-fit conditions.
  have hHdrFit : 0 + hdrW.size ≤ buf0.size := by rw [hHdrWSz, hBuf0Sz]; omega
  have hPhdrFit : phoff + phdrW.size ≤ buf1.size := by rw [hPhdrWSz, hBuf1Sz]; exact hPhdrEnd
  have hShdrFit : shoff + shdrW.size ≤ buf2.size := by rw [hShdrWSz, hBuf2Sz]; exact hShdrEnd
  have hrLtTotal : r < total := by omega
  -- Step 1: section foldl preserves byte at offset r.
  have hStep1 : Reader.readU8
      (e.sections.foldl (init := buf3) sectionFoldStep) r
      = Reader.readU8 buf3 r := by
    apply readU8_foldl_section_splice_preserved e.sections 0 Layout.ehdrSize buf3
      (hKAll := ?_) (hrLo := Nat.zero_le _) (hrHi := hr)
      (hrFit := by rw [hBuf3Sz]; exact hrLtTotal)
    intros i hi
    -- Case-split on s.type FIRST (so we have the type negation facts).
    by_cases hN1 : (e.sections[i]'hi).type = ShType.SHT_NOBITS
    · exact Or.inl hN1
    by_cases hN2 : (e.sections[i]'hi).type = ShType.SHT_NULL
    · exact Or.inr (Or.inl hN2)
    -- Non-NOBITS, non-NULL: derive disjointness + size bound.
    refine Or.inr (Or.inr ⟨?_, ?_⟩)
    · -- IntervalDisjoint 0 ehdrSize s.offset s.end from headerSectionDisjoint.
      have hSec := hDisj.hdr_sec_disjoint i hi
      rcases hSec with hN | hN | hOK
      · exact absurd hN hN1
      · exact absurd hN hN2
      exact hOK
    · -- s.offset + s.encodedSize ≤ buf3.size
      rw [hBuf3Sz]
      exact section_end_le_encodedFileSize e i hi hN1 hN2
  -- Steps 2–4: shdr/phdr disjoint splices + header inside-splice.
  -- These three manual cascades collapse to a single `simp_splice`.
  -- ROADMAP §5.4: omega discharger handles every side condition
  -- (splice fit, read fit, disjointness, inside-bounds).
  have hShdrDisj : r + 1 ≤ shoff ∨ shoff + shdrW.size ≤ r := by
    have hI := hDisj.hdr_shdr_disjoint
    unfold ElfFile.headerShdrDisjoint IntervalDisjoint at hI
    rcases hI with hL | hR
    · left; omega
    · right; rw [hShdrWSz]; omega
  have hPhdrDisj : r + 1 ≤ phoff ∨ phoff + phdrW.size ≤ r := by
    have hI := hDisj.hdr_phdr_disjoint
    unfold ElfFile.headerPhdrDisjoint IntervalDisjoint at hI
    rcases hI with hL | hR
    · left; omega
    · right; rw [hPhdrWSz]; omega
  have hHdrInside : r < hdrW.size := by rw [hHdrWSz]; omega
  have hStep234 : Reader.readU8 buf3 r = Reader.readU8 hdrW r := by
    show Reader.readU8
      (splice (splice (splice buf0 0 hdrW) phoff phdrW) shoff shdrW) r = _
    have hr_buf0 : r < buf0.size := by rw [hBuf0Sz]; exact hrLtTotal
    have hr_buf1 : r < (splice buf0 0 hdrW).size := by
      rw [splice_size]; exact hr_buf0
    have hr_buf2 : r < (splice (splice buf0 0 hdrW) phoff phdrW).size := by
      rw [splice_size]; exact hr_buf1
    -- Make the buffer-size goals omega can see.
    have hSplBuf1 : (splice buf0 0 hdrW).size = buf0.size := splice_size _ _ _
    have hSplBuf2 :
        (splice (splice buf0 0 hdrW) phoff phdrW).size = buf0.size := by
      rw [splice_size, hSplBuf1]
    simp_splice
  -- Compose.  The goal already has the foldl form on the LHS.
  show Reader.readU8 (e.sections.foldl _ buf3) r = Reader.readU8 hdrW r
  rw [hStep1, hStep234]

/-- `readU16` analog of `readU8_encode_in_header`. -/
private theorem readU16_encode_in_header (e : ElfFile)
    (hSync : syncDtStrszInFile e = e)
    (hLay : layoutAlreadyValid e = true)
    (hDisj : e.spliceRegionsDisjoint)
    (r : Nat) (hr : r + 2 ≤ Layout.ehdrSize) :
    Reader.readU16 (encode e) r
      = Reader.readU16 (ElfHeader.write e.header) r := by
  unfold Reader.readU16
  rw [readU8_encode_in_header e hSync hLay hDisj r (by omega)]
  rw [readU8_encode_in_header e hSync hLay hDisj (r + 1) (by omega)]

/-- `readU32` analog. -/
private theorem readU32_encode_in_header (e : ElfFile)
    (hSync : syncDtStrszInFile e = e)
    (hLay : layoutAlreadyValid e = true)
    (hDisj : e.spliceRegionsDisjoint)
    (r : Nat) (hr : r + 4 ≤ Layout.ehdrSize) :
    Reader.readU32 (encode e) r
      = Reader.readU32 (ElfHeader.write e.header) r := by
  unfold Reader.readU32
  iterate 4 rw [readU8_encode_in_header e hSync hLay hDisj _ (by omega)]

/-- `readU64` analog. -/
private theorem readU64_encode_in_header (e : ElfFile)
    (hSync : syncDtStrszInFile e = e)
    (hLay : layoutAlreadyValid e = true)
    (hDisj : e.spliceRegionsDisjoint)
    (r : Nat) (hr : r + 8 ≤ Layout.ehdrSize) :
    Reader.readU64 (encode e) r
      = Reader.readU64 (ElfHeader.write e.header) r := by
  unfold Reader.readU64
  rw [readU32_encode_in_header e hSync hLay hDisj r (by omega)]
  rw [readU32_encode_in_header e hSync hLay hDisj (r + 4) (by omega)]

/-- Per-byte preservation: the i-th byte of `(encode e)` agrees with
    the i-th byte of `ElfHeader.write e.header` for `i < ehdrSize`. -/
private theorem getElem_encode_in_header (e : ElfFile)
    (hSync : syncDtStrszInFile e = e)
    (hLay : layoutAlreadyValid e = true)
    (hDisj : e.spliceRegionsDisjoint)
    (i : Nat) (hi : i < Layout.ehdrSize)
    (hI_e : i < (encode e).size) (hI_w : i < (ElfHeader.write e.header).size) :
    (encode e)[i]'hI_e = (ElfHeader.write e.header)[i]'hI_w := by
  have hRd := readU8_encode_in_header e hSync hLay hDisj i (by
    have : Layout.ehdrSize = 64 := rfl; omega)
  unfold Reader.readU8 at hRd
  rw [dif_pos hI_e, dif_pos hI_w] at hRd
  exact hRd

/-- Extract equality on the header region: `(encode e).extract 0 ehdrSize
    = ElfHeader.write e.header`.  Per-byte preservation lifted to extract. -/
private theorem extract_encode_eq_header_write (e : ElfFile)
    (hSync : syncDtStrszInFile e = e)
    (hLay : layoutAlreadyValid e = true)
    (hDisj : e.spliceRegionsDisjoint) :
    (encode e).extract 0 Layout.ehdrSize = ElfHeader.write e.header := by
  have hEncSz : (encode e).size = encodedFileSize
      (let e1 := syncDtStrszInFile e
       if layoutAlreadyValid e1 then e1 else layoutForEncoding e1) :=
    encode_size_eq e
  have hEncSz' : (encode e).size = encodedFileSize e := by
    rw [hEncSz]; show encodedFileSize _ = _; rw [hSync]; simp [hLay]
  have hWriteSz : (ElfHeader.write e.header).size = Layout.ehdrSize := ElfHeader.write_size _
  have hTotalEhdr : Layout.ehdrSize ≤ encodedFileSize e := encodedFileSize_ge_ehdr e
  apply ByteArray.ext_getElem
  · rw [ByteArray.size_extract, hEncSz', hWriteSz]
    have : Layout.ehdrSize ≤ encodedFileSize e := hTotalEhdr
    omega
  · intros i hi _
    rw [ByteArray.size_extract, hEncSz'] at hi
    have hi' : i < Layout.ehdrSize := by
      have : Layout.ehdrSize ≤ encodedFileSize e := hTotalEhdr
      omega
    -- Reduce both sides to the form `_[i]`.
    simp only [ByteArray.getElem_extract, Nat.zero_add]
    exact getElem_encode_in_header e hSync hLay hDisj i hi'
      (by rw [hEncSz']; omega) (by rw [hWriteSz]; omega)

set_option maxHeartbeats 4000000 in
/-- `decodeHeader (encode e) 0 _ = e.header`.

    Routes through `decodeHeader_eq_slice` to avoid the 14-field
    `congr 1` cascade. -/
private theorem decodeHeader_encode (e : ElfFile)
    (hSync : syncDtStrszInFile e = e)
    (hLay : layoutAlreadyValid e = true)
    (hDisj : e.spliceRegionsDisjoint)
    (hFitEntry : e.header.entry.val < UInt64.size)
    (hFitPhoff : e.header.phoff.val < UInt64.size)
    (hFitShoff : e.header.shoff.val < UInt64.size)
    (h : 0 + 64 ≤ (encode e).size) :
    Decode.decodeHeader (encode e) 0 h = e.header := by
  have hExt := extract_encode_eq_header_write e hSync hLay hDisj
  -- The slice form lets us substitute the extracted window with the
  -- writer payload via a single rewrite.
  have hSlice := decodeHeader_eq_slice (encode e) 0 (by simpa using h)
  -- LHS = decodeHeaderSlice ((encode e).extract 0 (0+64)) _
  -- After unfolding the slice and substituting via hExt:
  --   = decodeHeader (write hdr) 0 _
  --   = e.header (by ElfHeader_decode_write)
  -- We thread through Eq.trans + a cast to avoid motive issues on the
  -- dependent precondition argument.
  refine hSlice.trans ?_
  unfold Decode.decodeHeaderSlice
  -- Goal: decodeHeader ((encode e).extract 0 (0+64)) 0 _ = e.header.
  -- Build the proof in two steps: first the casted equality, then close.
  have hExtNorm : (encode e).extract 0 (0 + 64) = ElfHeader.write e.header := by
    show (encode e).extract 0 Layout.ehdrSize = _; exact hExt
  -- Use congrArg + cast to substitute the buffer in the dependent goal.
  -- More precisely: decodeHeader is dependent on its proof argument,
  -- but the result type doesn't depend on it (Prop irrelevance), so
  -- we can use Eq.mpr / Eq.ndrec to cast.
  have hWriteSz : (ElfHeader.write e.header).size = 64 := ElfHeader.write_size _
  have hX : 0 + 64 ≤ (ElfHeader.write e.header).size := by rw [hWriteSz]; omega
  rw [show Decode.decodeHeader ((encode e).extract 0 (0 + 64)) 0 _
        = Decode.decodeHeader (ElfHeader.write e.header) 0 hX from by
        congr 1]
  exact ElfHeader_decode_write e.header hX hFitEntry hFitPhoff hFitShoff

/-! ## ParsedElf-level validity

    `IdentBytesValid e` packages 6 byte-level facts about
    `e.header.ident.head` checked by `parseHeader` but NOT in
    `IsValid`: ELF magic + class + data bytes.  Real ELFs always
    satisfy these. -/
structure IdentBytesValid (e : ElfFile) : Prop where
  head_size : e.header.ident.head.size = 7
  byte0     : e.header.ident.head[0]'(by rw [head_size]; decide) = 0x7f
  byte1     : e.header.ident.head[1]'(by rw [head_size]; decide) = 0x45  -- 'E'
  byte2     : e.header.ident.head[2]'(by rw [head_size]; decide) = 0x4c  -- 'L'
  byte3     : e.header.ident.head[3]'(by rw [head_size]; decide) = 0x46  -- 'F'
  classByte : e.header.ident.head[4]'(by rw [head_size]; decide) = Layout.ElfClass.elf64.encode
  dataByte  : e.header.ident.head[5]'(by rw [head_size]; decide) = Layout.ElfData.lsb.encode

set_option maxHeartbeats 4000000 in
/-- Extract of `[0, 7)` from `ElfHeader.write hdr` recovers
    `hdr.ident.head` (the writer's leftmost factor).

    Iteratively peels the 13 outer ++s (the trailing primitive
    writes) using `extract_append_left_within`, lands on
    `(ElfIdent.write hdr.ident).extract 0 7`, then peels the
    2 inner ++s to land on `head.extract 0 7 = head` (since
    head.size = 7). -/
private theorem write_extract_head (hdr : ElfHeader) (h : hdr.ident.head.size = 7) :
    (ElfHeader.write hdr).extract 0 7 = hdr.ident.head := by
  unfold ElfHeader.write
  -- The writer chain is left-associated.  Use `extract_append_left_within`
  -- to peel each outer ++.  At every level, the prefix has size ≥ 7
  -- (it always contains ElfIdent.write hdr.ident which has size 16).
  --
  -- Build size facts as we peel.
  have hI : (ElfIdent.write hdr.ident).size = 16 := ElfIdent.write_size hdr.ident
  -- Per-level size of the prefix chain (always ≥ 16 ≥ 7).
  have hSizeFact : ∀ (chain : ByteArray) (suf : ByteArray), 7 ≤ chain.size →
      7 ≤ (chain ++ suf).size := fun chain suf hC => by
    rw [ByteArray.size_append]; omega
  -- Each peel applies extract_append_left_within with j = 7.
  -- 13 outer peels.
  rw [ByteArray.extract_append_left_within _ _ 7
        (by simp [ByteArray.size_append, hI])]
  rw [ByteArray.extract_append_left_within _ _ 7
        (by simp [ByteArray.size_append, hI])]
  rw [ByteArray.extract_append_left_within _ _ 7
        (by simp [ByteArray.size_append, hI])]
  rw [ByteArray.extract_append_left_within _ _ 7
        (by simp [ByteArray.size_append, hI])]
  rw [ByteArray.extract_append_left_within _ _ 7
        (by simp [ByteArray.size_append, hI])]
  rw [ByteArray.extract_append_left_within _ _ 7
        (by simp [ByteArray.size_append, hI])]
  rw [ByteArray.extract_append_left_within _ _ 7
        (by simp [ByteArray.size_append, hI])]
  rw [ByteArray.extract_append_left_within _ _ 7
        (by simp [ByteArray.size_append, hI])]
  rw [ByteArray.extract_append_left_within _ _ 7
        (by simp [ByteArray.size_append, hI])]
  rw [ByteArray.extract_append_left_within _ _ 7
        (by simp [ByteArray.size_append, hI])]
  rw [ByteArray.extract_append_left_within _ _ 7
        (by simp [ByteArray.size_append, hI])]
  rw [ByteArray.extract_append_left_within _ _ 7
        (by simp [ByteArray.size_append, hI])]
  rw [ByteArray.extract_append_left_within _ _ 7 (by rw [hI]; omega)]
  -- Goal: (ElfIdent.write hdr.ident).extract 0 7 = hdr.ident.head.
  unfold ElfIdent.write
  -- Goal: (head ++ writeU8 ... ++ tail).extract 0 7 = head.
  rw [ByteArray.extract_append_left_within _ _ 7 (by
    rw [ByteArray.size_append, h]
    have : (Writer.writeU8 hdr.ident.osAbi.encode).size = 1 := rfl
    omega)]
  rw [ByteArray.extract_append_left_within _ _ 7 (by rw [h]; omega)]
  -- Goal: head.extract 0 7 = head.
  rw [show (7 : Nat) = hdr.ident.head.size from h.symm]
  exact ByteArray.extract_zero_size

set_option maxHeartbeats 800000 in
/-- The encoded buffer's first 7 bytes are `e.header.ident.head`.
    Composes `extract_encode_eq_header_write` with `write_extract_head`. -/
private theorem extract_encode_eq_ident_head (e : ElfFile)
    (hSync : syncDtStrszInFile e = e)
    (hLay : layoutAlreadyValid e = true)
    (hDisj : e.spliceRegionsDisjoint)
    (hIdent : IdentBytesValid e) :
    (encode e).extract 0 7 = e.header.ident.head := by
  have hExtH := extract_encode_eq_header_write e hSync hLay hDisj
  have hExtW := write_extract_head e.header hIdent.head_size
  have h1 : (encode e).extract 0 7
          = ((encode e).extract 0 Layout.ehdrSize).extract 0 7 := by
    rw [ByteArray.extract_extract]
    rw [show min (0 + 7) Layout.ehdrSize = 7 from by
      have : Layout.ehdrSize = 64 := rfl; omega]
  rw [h1, hExtH, hExtW]

/-- Per-byte equality at offset `i < 7` of `(encode e)` recovers
    `e.header.ident.head[i]`.  Direct from `extract_encode_eq_ident_head`. -/
private theorem readU8_encode_eq_ident_head (e : ElfFile)
    (hSync : syncDtStrszInFile e = e)
    (hLay : layoutAlreadyValid e = true)
    (hDisj : e.spliceRegionsDisjoint)
    (hIdent : IdentBytesValid e)
    (i : Nat) (hi : i < 7) :
    Reader.readU8 (encode e) i =
      e.header.ident.head[i]'(by rw [hIdent.head_size]; exact hi) := by
  have hExt7 := extract_encode_eq_ident_head e hSync hLay hDisj hIdent
  have hHeadSz : e.header.ident.head.size = 7 := hIdent.head_size
  -- Read at offset i agrees on (encode e) and (encode e).extract 0 7 since
  -- both have byte i (i < 7) coming from the same place.
  have hi_ext_sz : ((encode e).extract 0 7).size ≥ 7 ∨ True := Or.inr trivial
  -- hExt7 says (encode e).extract 0 7 = head; readU8 on equal arrays equal.
  have hReadEq : Reader.readU8 (encode e) i = Reader.readU8 ((encode e).extract 0 7) i := by
    -- Both buffers agree on byte i (extract 0 7 takes the first 7 bytes).
    unfold Reader.readU8
    have hEncSz : (encode e).size = encodedFileSize e := by
      rw [encode_size_eq]; show encodedFileSize _ = _; rw [hSync]; simp [hLay]
    have hi_e : i < (encode e).size := by
      rw [hEncSz]
      have : Layout.ehdrSize ≤ encodedFileSize e := encodedFileSize_ge_ehdr e
      have : Layout.ehdrSize = 64 := rfl
      omega
    have hi_ext : i < ((encode e).extract 0 7).size := by
      rw [ByteArray.size_extract]; omega
    rw [dif_pos hi_e, dif_pos hi_ext, ByteArray.getElem_extract]
    congr 1; omega
  rw [hReadEq, hExt7]
  -- Goal: readU8 e.header.ident.head i = head[i].
  unfold Reader.readU8
  rw [dif_pos (by rw [hHeadSz]; exact hi)]

set_option maxHeartbeats 800000 in
/-- `parseHeader_ok`: the parser succeeds on `(encode e)` and returns
    `e.header`, given the appropriate preconditions on `e`.

    Composes `decodeHeader_encode` (decoder discharge),
    `readU8_encode_eq_ident_head` (per-byte ident checks),
    `e.IsValid.headerCountsConsistent` (validation), and
    `phdr/shdr_end_le_encodedFileSize` (bounds checks). -/
theorem parseHeader_encode (e : ElfFile)
    (hSync : syncDtStrszInFile e = e)
    (hLay : layoutAlreadyValid e = true)
    (hDisj : e.spliceRegionsDisjoint)
    (hVal : e.IsValid)
    (hIdent : IdentBytesValid e)
    (hFitEntry : e.header.entry.val < UInt64.size)
    (hFitPhoff : e.header.phoff.val < UInt64.size)
    (hFitShoff : e.header.shoff.val < UInt64.size) :
    Patchelf.Elf.Parse.parseHeader (encode e) = .ok e.header := by
  have hEncSz : (encode e).size = encodedFileSize e := by
    rw [encode_size_eq]; show encodedFileSize _ = _; rw [hSync]; simp [hLay]
  have hEhdrFit : Layout.ehdrSize ≤ (encode e).size := by
    rw [hEncSz]; exact encodedFileSize_ge_ehdr e
  unfold Patchelf.Elf.Parse.parseHeader
  rw [dif_neg (Nat.not_lt.mpr hEhdrFit)]
  unfold Decode.decodeIdent
  -- Magic / class / data byte facts via readU8_encode_eq_ident_head.
  have hM0 : Reader.readU8 (encode e) 0 = 0x7f := by
    rw [readU8_encode_eq_ident_head e hSync hLay hDisj hIdent 0 (by decide)]
    exact hIdent.byte0
  have hM1 : Reader.readU8 (encode e) 1 = 0x45 := by
    rw [readU8_encode_eq_ident_head e hSync hLay hDisj hIdent 1 (by decide)]
    exact hIdent.byte1
  have hM2 : Reader.readU8 (encode e) 2 = 0x4c := by
    rw [readU8_encode_eq_ident_head e hSync hLay hDisj hIdent 2 (by decide)]
    exact hIdent.byte2
  have hM3 : Reader.readU8 (encode e) 3 = 0x46 := by
    rw [readU8_encode_eq_ident_head e hSync hLay hDisj hIdent 3 (by decide)]
    exact hIdent.byte3
  have hMC : Reader.readU8 (encode e) Layout.EI_CLASS = Layout.ElfClass.elf64.encode := by
    show Reader.readU8 (encode e) 4 = _
    rw [readU8_encode_eq_ident_head e hSync hLay hDisj hIdent 4 (by decide)]
    exact hIdent.classByte
  have hMD : Reader.readU8 (encode e) Layout.EI_DATA = Layout.ElfData.lsb.encode := by
    show Reader.readU8 (encode e) 5 = _
    rw [readU8_encode_eq_ident_head e hSync hLay hDisj hIdent 5 (by decide)]
    exact hIdent.dataByte
  -- Magic check passes (combine 4 byte equalities).
  have hMagic : (Reader.readU8 (encode e) (0 + 0) == 0x7f
              && Reader.readU8 (encode e) (0 + 1) == 0x45
              && Reader.readU8 (encode e) (0 + 2) == 0x4c
              && Reader.readU8 (encode e) (0 + 3) == 0x46) = true := by
    simp only [Nat.zero_add, hM0, hM1, hM2, hM3]
    decide
  rw [if_neg (by intro h; exact h hMagic)]
  -- Class / data byte checks.
  have hClass : Reader.readU8 (encode e) (0 + Layout.EI_CLASS)
              = Layout.ElfClass.elf64.encode := by
    rw [show (0 + Layout.EI_CLASS : Nat) = Layout.EI_CLASS from by omega]
    exact hMC
  have hData : Reader.readU8 (encode e) (0 + Layout.EI_DATA)
             = Layout.ElfData.lsb.encode := by
    rw [show (0 + Layout.EI_DATA : Nat) = Layout.EI_DATA from by omega]
    exact hMD
  rw [if_neg (by rw [hClass]; exact fun h => h rfl)]
  rw [if_neg (by rw [hData]; exact fun h => h rfl)]
  -- decodeHeader.
  rw [decodeHeader_encode e hSync hLay hDisj hFitEntry hFitPhoff hFitShoff (by
    have : Layout.ehdrSize = 64 := rfl; omega)]
  -- Header validation.
  obtain ⟨hPhnum, hShnum, hPhentsize, hShentsize, hShstrndx⟩ := hVal.header_counts
  rw [if_neg (by rw [hPhentsize]; decide)]
  rw [if_neg (by rw [hShentsize]; decide)]
  have hPhdrFit : e.header.phoff.val + e.header.phnum.toNat
      * e.header.phentsize.toNat ≤ (encode e).size := by
    rw [hPhentsize, hPhnum, hEncSz]
    exact phdr_end_le_encodedFileSize e
  have hShdrFit : e.header.shoff.val + e.header.shnum.toNat
      * e.header.shentsize.toNat ≤ (encode e).size := by
    rw [hShentsize, hShnum, hEncSz]
    exact shdr_end_le_encodedFileSize e
  rw [if_neg (Nat.not_lt.mpr hPhdrFit)]
  rw [if_neg (Nat.not_lt.mpr hShdrFit)]
  rw [if_neg (by rw [hShnum]; exact Nat.not_le.mpr hShstrndx)]

/-! ## Phdr region preservation through encode

    Mirrors the per-region preservation lemmas for the header region.
    For an `e` satisfying the standard preconditions, bytes at offsets
    in `[phoff, phoff + phnum * phdrSize)` of `(encode e)` recover
    the corresponding byte of `writeArray ProgramHeader.write e.phdrs`.

    Reasoning chain per byte at `r := phoff + k`, `k < phnum * 56`:
      1. `encode e = encodeBody e` (pre-passes are no-ops).
      2. `readU{N} (sections.foldl _) r = readU{N} buf3 r` via
         `readU{N}_foldl_section_splice_preserved` over `[phoff, phoff+phnum*56)`
         (sections disjoint via `phdr_sec_disjoint`).
      3. `readU{N} buf3 r = readU{N} buf2 r` via `readU{N}_splice_disjoint`
         (shdr region disjoint from phdr region via `phdr_shdr_disjoint`).
      4. `readU{N} buf2 r = readU{N} phdrW (r - phoff) = readU{N} phdrW k` via
         `readU{N}_splice_at_off_inside` (phdr region IS the splice). -/

private theorem readU8_encode_in_phdr (e : ElfFile)
    (hSync : syncDtStrszInFile e = e)
    (hLay : layoutAlreadyValid e = true)
    (hDisj : e.spliceRegionsDisjoint)
    (k : Nat) (hk : k + 1 ≤ e.phdrs.size * Layout.phdrSize) :
    Reader.readU8 (encode e) (e.header.phoff.val + k)
      = Reader.readU8 (writeArray ProgramHeader.write e.phdrs) k := by
  -- Drive `encode e` to its `encodeBody` form.
  have hEnc : encode e = encodeBody e := by
    unfold encode; rw [hSync]; simp [hLay]
  rw [hEnc]
  unfold encodeBody
  let total := encodedFileSize e
  let buf0 : ByteArray := zeroBytes total
  let hdrW : ByteArray := ElfHeader.write e.header
  let buf1 : ByteArray := splice buf0 0 hdrW
  let phdrW : ByteArray := writeArray ProgramHeader.write e.phdrs
  let phoff := e.header.phoff.val
  let buf2 : ByteArray := splice buf1 phoff phdrW
  let shdrW : ByteArray := writeArray SectionHeader.write (e.sections.map toShdr)
  let shoff := e.header.shoff.val
  let buf3 : ByteArray := splice buf2 shoff shdrW
  -- Sizes.
  have hBuf0Sz : buf0.size = total := zeroBytes_size total
  have hBuf1Sz : buf1.size = total := by show (splice _ _ _).size = _; rw [splice_size]; exact hBuf0Sz
  have hBuf2Sz : buf2.size = total := by show (splice _ _ _).size = _; rw [splice_size]; exact hBuf1Sz
  have hBuf3Sz : buf3.size = total := by show (splice _ _ _).size = _; rw [splice_size]; exact hBuf2Sz
  have hPhdrWSz : phdrW.size = e.phdrs.size * Layout.phdrSize :=
    writeArray_size_of_uniform ProgramHeader.write Layout.phdrSize
            ProgramHeader.write_size e.phdrs
  have hShdrWSz : shdrW.size = e.sections.size * Layout.shdrSize := by
    show (writeArray _ _).size = _
    rw [writeArray_size_of_uniform SectionHeader.write Layout.shdrSize
            SectionHeader.write_size, Array.size_map]
  -- Region bounds.
  have hPhdrEnd : phoff + e.phdrs.size * Layout.phdrSize ≤ total :=
    phdr_end_le_encodedFileSize e
  have hShdrEnd : shoff + e.sections.size * Layout.shdrSize ≤ total :=
    shdr_end_le_encodedFileSize e
  -- Splice-fit conditions.
  have hPhdrFit : phoff + phdrW.size ≤ buf1.size := by rw [hPhdrWSz, hBuf1Sz]; exact hPhdrEnd
  have hShdrFit : shoff + shdrW.size ≤ buf2.size := by rw [hShdrWSz, hBuf2Sz]; exact hShdrEnd
  -- The target read offset r := phoff + k.
  have hrLtTotal : phoff + k < total := by
    have : phoff + k < phoff + e.phdrs.size * Layout.phdrSize := by omega
    exact Nat.lt_of_lt_of_le this hPhdrEnd
  -- Step 1: section foldl preserves byte at `phoff + k`.
  have hStep1 : Reader.readU8
      (e.sections.foldl (init := buf3) sectionFoldStep) (phoff + k)
      = Reader.readU8 buf3 (phoff + k) := by
    apply readU8_foldl_section_splice_preserved e.sections phoff
      (phoff + e.phdrs.size * Layout.phdrSize) buf3
      (hKAll := ?_) (hrLo := Nat.le_add_right _ _) (hrHi := by omega)
      (hrFit := by rw [hBuf3Sz]; exact hrLtTotal)
    intros i hi
    by_cases hN1 : (e.sections[i]'hi).type = ShType.SHT_NOBITS
    · exact Or.inl hN1
    by_cases hN2 : (e.sections[i]'hi).type = ShType.SHT_NULL
    · exact Or.inr (Or.inl hN2)
    refine Or.inr (Or.inr ⟨?_, ?_⟩)
    · -- phdrSectionDisjoint gives exactly the IntervalDisjoint we need.
      have hSec := hDisj.phdr_sec_disjoint i hi
      rcases hSec with hN | hN | hOK
      · exact absurd hN hN1
      · exact absurd hN hN2
      exact hOK
    · rw [hBuf3Sz]; exact section_end_le_encodedFileSize e i hi hN1 hN2
  -- Step 2: shdr splice preserves byte (shdr region disjoint from phdr).
  have hStep2 : Reader.readU8 buf3 (phoff + k) = Reader.readU8 buf2 (phoff + k) := by
    show Reader.readU8 (splice buf2 shoff shdrW) (phoff + k) = _
    apply Reader.readU8_splice_disjoint buf2 shoff shdrW hShdrFit (phoff + k)
      (by rw [hBuf2Sz]; exact hrLtTotal)
    have hI := hDisj.phdr_shdr_disjoint
    -- phdrShdrDisjoint : IntervalDisjoint phoff (phoff + phnum*56) shoff (shoff + shnum*64)
    unfold ElfFile.phdrShdrDisjoint IntervalDisjoint at hI
    rcases hI with hL | hR
    · -- phoff + phnum*56 ≤ shoff: read at phoff+k is left of shdr region.
      left; omega
    · -- shoff + shnum*64 ≤ phoff: read at phoff+k is right of shdr region.
      right; rw [hShdrWSz]; omega
  -- Step 3: phdr splice INSIDE returns the payload.
  have hStep3 : Reader.readU8 buf2 (phoff + k) = Reader.readU8 phdrW k := by
    show Reader.readU8 (splice buf1 phoff phdrW) (phoff + k) = _
    rw [Reader.readU8_splice_at_off_inside buf1 phoff phdrW hPhdrFit (phoff + k)
      (Nat.le_add_right _ _) (by rw [hPhdrWSz]; omega)]
    rw [show phoff + k - phoff = k from by omega]
  show Reader.readU8 (e.sections.foldl _ buf3) (phoff + k) = Reader.readU8 phdrW k
  rw [hStep1, hStep2, hStep3]

/-- `readU16` analog of `readU8_encode_in_phdr`. -/
private theorem readU16_encode_in_phdr (e : ElfFile)
    (hSync : syncDtStrszInFile e = e)
    (hLay : layoutAlreadyValid e = true)
    (hDisj : e.spliceRegionsDisjoint)
    (k : Nat) (hk : k + 2 ≤ e.phdrs.size * Layout.phdrSize) :
    Reader.readU16 (encode e) (e.header.phoff.val + k)
      = Reader.readU16 (writeArray ProgramHeader.write e.phdrs) k := by
  unfold Reader.readU16
  rw [readU8_encode_in_phdr e hSync hLay hDisj k (by omega)]
  rw [show e.header.phoff.val + k + 1 = e.header.phoff.val + (k + 1)
        from by omega,
      readU8_encode_in_phdr e hSync hLay hDisj (k + 1) (by omega)]

/-- `readU32` analog. -/
private theorem readU32_encode_in_phdr (e : ElfFile)
    (hSync : syncDtStrszInFile e = e)
    (hLay : layoutAlreadyValid e = true)
    (hDisj : e.spliceRegionsDisjoint)
    (k : Nat) (hk : k + 4 ≤ e.phdrs.size * Layout.phdrSize) :
    Reader.readU32 (encode e) (e.header.phoff.val + k)
      = Reader.readU32 (writeArray ProgramHeader.write e.phdrs) k := by
  unfold Reader.readU32
  rw [readU8_encode_in_phdr e hSync hLay hDisj k (by omega)]
  rw [show e.header.phoff.val + k + 1 = e.header.phoff.val + (k + 1)
        from by omega,
      readU8_encode_in_phdr e hSync hLay hDisj (k + 1) (by omega)]
  rw [show e.header.phoff.val + k + 2 = e.header.phoff.val + (k + 2)
        from by omega,
      readU8_encode_in_phdr e hSync hLay hDisj (k + 2) (by omega)]
  rw [show e.header.phoff.val + k + 3 = e.header.phoff.val + (k + 3)
        from by omega,
      readU8_encode_in_phdr e hSync hLay hDisj (k + 3) (by omega)]

/-- `readU64` analog. -/
private theorem readU64_encode_in_phdr (e : ElfFile)
    (hSync : syncDtStrszInFile e = e)
    (hLay : layoutAlreadyValid e = true)
    (hDisj : e.spliceRegionsDisjoint)
    (k : Nat) (hk : k + 8 ≤ e.phdrs.size * Layout.phdrSize) :
    Reader.readU64 (encode e) (e.header.phoff.val + k)
      = Reader.readU64 (writeArray ProgramHeader.write e.phdrs) k := by
  unfold Reader.readU64
  rw [readU32_encode_in_phdr e hSync hLay hDisj k (by omega)]
  rw [show e.header.phoff.val + k + 4 = e.header.phoff.val + (k + 4)
        from by omega,
      readU32_encode_in_phdr e hSync hLay hDisj (k + 4) (by omega)]

/-- Per-byte preservation: the i-th byte of `(encode e)` agrees with
    the i-th byte of `writeArray PH.write e.phdrs` when `i ∈ [phoff, phoff + phnum*56)`. -/
private theorem getElem_encode_in_phdr (e : ElfFile)
    (hSync : syncDtStrszInFile e = e)
    (hLay : layoutAlreadyValid e = true)
    (hDisj : e.spliceRegionsDisjoint)
    (k : Nat) (hk : k < e.phdrs.size * Layout.phdrSize)
    (hI_e : e.header.phoff.val + k < (encode e).size)
    (hI_w : k < (writeArray ProgramHeader.write e.phdrs).size) :
    (encode e)[e.header.phoff.val + k]'hI_e
      = (writeArray ProgramHeader.write e.phdrs)[k]'hI_w := by
  have hRd := readU8_encode_in_phdr e hSync hLay hDisj k (by omega)
  unfold Reader.readU8 at hRd
  rw [dif_pos hI_e, dif_pos hI_w] at hRd
  exact hRd

/-- Extract equality on the phdr region: `(encode e).extract phoff (phoff +
    phnum*56) = writeArray PH.write e.phdrs`.  Per-byte preservation
    lifted to extract via `ext_getElem`. -/
private theorem extract_encode_eq_phdrs_writer (e : ElfFile)
    (hSync : syncDtStrszInFile e = e)
    (hLay : layoutAlreadyValid e = true)
    (hDisj : e.spliceRegionsDisjoint) :
    (encode e).extract e.header.phoff.val
        (e.header.phoff.val + e.phdrs.size * Layout.phdrSize)
      = writeArray ProgramHeader.write e.phdrs := by
  have hEncSz : (encode e).size = encodedFileSize e := by
    rw [encode_size_eq]; show encodedFileSize _ = _; rw [hSync]; simp [hLay]
  have hPhdrWSz : (writeArray ProgramHeader.write e.phdrs).size
                  = e.phdrs.size * Layout.phdrSize :=
    writeArray_size_of_uniform ProgramHeader.write Layout.phdrSize
            ProgramHeader.write_size e.phdrs
  have hPhdrEnd : e.header.phoff.val + e.phdrs.size * Layout.phdrSize
                  ≤ encodedFileSize e := phdr_end_le_encodedFileSize e
  apply ByteArray.ext_getElem
  · rw [ByteArray.size_extract, hEncSz, hPhdrWSz]; omega
  · intros i hi _
    rw [ByteArray.size_extract, hEncSz] at hi
    have hi' : i < e.phdrs.size * Layout.phdrSize := by omega
    simp only [ByteArray.getElem_extract]
    exact getElem_encode_in_phdr e hSync hLay hDisj i hi'
      (by rw [hEncSz]; omega) (by rw [hPhdrWSz]; exact hi')

/-- Per-element decoder bridge: decoding the i-th window of
    `writeArray PH.write arr` recovers `arr[i]`.  Composes
    `writeArray_uniform_extract_at_index` (window = `(arr[i]).write`)
    with `decodePhdr_eq_slice` and `ProgramHeader_decode_write`. -/
private theorem decodePhdr_writeArray_at_index (arr : Array ProgramHeader)
    (i : Nat) (hi : i < arr.size)
    (hFitOff : (arr[i]'hi).offset.val < UInt64.size)
    (hFitVAddr : (arr[i]'hi).vaddr.val < UInt64.size)
    (hFitPAddr : (arr[i]'hi).paddr.val < UInt64.size)
    (hFitFsz : (arr[i]'hi).filesz.val < UInt64.size)
    (hFitMsz : (arr[i]'hi).memsz.val < UInt64.size)
    (hFitAlign : (arr[i]'hi).align.val < UInt64.size) :
    Decode.decodePhdr (writeArray ProgramHeader.write arr) (i * Layout.phdrSize)
      = arr[i]'hi := by
  have hWaSz : (writeArray ProgramHeader.write arr).size = arr.size * Layout.phdrSize :=
    writeArray_size_of_uniform ProgramHeader.write Layout.phdrSize
            ProgramHeader.write_size arr
  -- Window-form decoder.
  have hFit : i * Layout.phdrSize + Layout.phdrSize
              ≤ (writeArray ProgramHeader.write arr).size := by
    rw [hWaSz]
    have : i + 1 ≤ arr.size := hi
    have := Nat.mul_le_mul_right Layout.phdrSize this
    rw [Nat.succ_mul] at this; omega
  rw [decodePhdr_eq_slice (writeArray ProgramHeader.write arr) (i * Layout.phdrSize) hFit]
  -- Substitute the window with `(arr[i]).write` via the writeArray-uniform
  -- extract-at-index lemma.
  rw [show i * Layout.phdrSize + 56 = i * Layout.phdrSize + Layout.phdrSize from rfl]
  rw [writeArray_uniform_extract_at_index Layout.phdrSize ProgramHeader.write
        ProgramHeader.write_size arr i hi]
  -- Now: decodePhdr ((arr[i]).write) 0 = arr[i].
  exact ProgramHeader_decode_write (arr[i]'hi)
    hFitOff hFitVAddr hFitPAddr hFitFsz hFitMsz hFitAlign

set_option maxHeartbeats 800000 in
/-- The phdr-table decoder on `encode e` recovers `e.phdrs`.

    Composes:
      * `extract_encode_eq_phdrs_writer` — phdr region of `encode e` is
        `writeArray PH.write e.phdrs`.
      * `decodePhdr_writeArray_at_index` — per-element bridge.
      * `ByteArray.extract_extract_window` — to substitute element
        windows from the encoder buffer with element windows from the
        writeArray.

    The result holds modulo:
      * `syncDtStrszInFile e = e` (no-op for already-synced inputs)
      * `layoutAlreadyValid e = true` (offsets in `e.header` match physical layout)
      * `e.spliceRegionsDisjoint` (all 4 region kinds pairwise disjoint)
      * `e.IsValid` (for `phnum.toNat = phdrs.size`).
-/
theorem phdrs_decode_encode (e : ElfFile)
    (hSync : syncDtStrszInFile e = e)
    (hLay : layoutAlreadyValid e = true)
    (hDisj : e.spliceRegionsDisjoint)
    (hVal : e.IsValid)
    (hPhdrFit : ∀ (i : Nat) (h : i < e.phdrs.size),
      (e.phdrs[i]'h).offset.val < UInt64.size ∧
      (e.phdrs[i]'h).vaddr.val < UInt64.size ∧
      (e.phdrs[i]'h).paddr.val < UInt64.size ∧
      (e.phdrs[i]'h).filesz.val < UInt64.size ∧
      (e.phdrs[i]'h).memsz.val < UInt64.size ∧
      (e.phdrs[i]'h).align.val < UInt64.size) :
    Patchelf.Elf.Decode.decodePhdrs (encode e)
      e.header.phoff.val e.header.phnum.toNat
      = e.phdrs := by
  obtain ⟨hPhnum, _, _, _, _⟩ := hVal.header_counts
  -- Sizes match.
  have hSizeEq : (Decode.decodePhdrs (encode e)
      e.header.phoff.val e.header.phnum.toNat).size = e.phdrs.size := by
    rw [Decode.decodePhdrs_size, hPhnum]
  -- Per-element equality.
  apply Array.ext hSizeEq
  intros i hLhs hRhs
  -- LHS: decodePhdr (encode e) (phoff + i*56)
  rw [Decode.decodePhdrs_getElem]
  -- Bound i < e.phdrs.size: hRhs gives that directly.
  have hi : i < e.phdrs.size := hRhs
  -- Sizes & bounds.
  have hExt := extract_encode_eq_phdrs_writer e hSync hLay hDisj
  have hEncSz : (encode e).size = encodedFileSize e := by
    rw [encode_size_eq]; show encodedFileSize _ = _; rw [hSync]; simp [hLay]
  have hPhdrEnd : e.header.phoff.val + e.phdrs.size * Layout.phdrSize
                  ≤ (encode e).size := by
    rw [hEncSz]; exact phdr_end_le_encodedFileSize e
  have hWinFit : e.header.phoff.val + i * 56 + 56 ≤ (encode e).size := by
    have hSucc : i + 1 ≤ e.phdrs.size := hi
    have hMul : (i + 1) * 56 ≤ e.phdrs.size * 56 :=
      Nat.mul_le_mul_right _ hSucc
    rw [Nat.succ_mul] at hMul
    have hPhdrSz : Layout.phdrSize = 56 := rfl
    rw [hEncSz]; have hEnd := phdr_end_le_encodedFileSize e
    rw [hPhdrSz] at hEnd; omega
  -- Step 1: decodePhdr_eq_slice → window form.
  rw [decodePhdr_eq_slice (encode e) (e.header.phoff.val + i * 56) hWinFit]
  -- Step 2: bridge encoder-window to writeArray-window via extract_extract_window.
  -- Outer phdr extract = writeArray; inner i-th element window from outer.
  have hOuter : e.header.phoff.val + e.phdrs.size * Layout.phdrSize
                ≤ (encode e).size := hPhdrEnd
  have hInner : i * 56 + 56 ≤ e.phdrs.size * Layout.phdrSize := by
    have hSucc : i + 1 ≤ e.phdrs.size := hi
    have hMul : (i + 1) * 56 ≤ e.phdrs.size * 56 :=
      Nat.mul_le_mul_right _ hSucc
    rw [Nat.succ_mul] at hMul
    have hPhdrSz : Layout.phdrSize = 56 := rfl
    rw [hPhdrSz]; omega
  have hEEW := ByteArray.extract_extract_window (encode e) e.header.phoff.val
                  (e.phdrs.size * Layout.phdrSize) (i * 56) 56 hOuter hInner
  -- hEEW : ((encode e).extract phoff (phoff + phnum*56)).extract (i*56) (i*56+56)
  --        = (encode e).extract (phoff + i*56) (phoff + i*56 + 56)
  -- Rewrite our goal's window with hEEW.symm, then substitute via hExt.
  rw [show (e.header.phoff.val + i * 56 + 56 : Nat)
        = e.header.phoff.val + i * 56 + 56 from rfl]
  rw [← hEEW]
  rw [hExt]
  -- Now LHS: decodePhdr ((writeArray PH.write e.phdrs).extract (i*56) (i*56+56)) 0
  rw [show (i * 56 + 56 : Nat) = i * Layout.phdrSize + Layout.phdrSize from by
        show i * 56 + 56 = i * 56 + 56; rfl]
  rw [show (i * 56 : Nat) = i * Layout.phdrSize from rfl]
  rw [writeArray_uniform_extract_at_index Layout.phdrSize ProgramHeader.write
        ProgramHeader.write_size e.phdrs i hi]
  obtain ⟨hO, hVA, hPA, hF, hM, hAl⟩ := hPhdrFit i hi
  exact ProgramHeader_decode_write (e.phdrs[i]'hi) hO hVA hPA hF hM hAl

/-! ## Shdr region preservation through encode

    Same shape as the phdr-region preservation lemmas: per-byte
    preservation through the encode pipeline for offsets in `[shoff,
    shoff + shnum*64)`.

    Disjointness chain at offset `r := shoff + k`, `k < shnum*64`:
      1. section foldl preserves r (sections disjoint via `shdr_sec_disjoint`).
      2. `readU{N} buf3 r = readU{N} shdrW (r - shoff)`: buf3 is the
         shdr splice itself; this is `splice_at_off_inside`.
      3. (Skipped: read is already at the splice payload, no need to
         go further down the buffer chain.)
    The shdr splice is the LAST splice in the encoder pipeline, so we
    don't need to traverse phdr / header splices for shdr-region reads. -/

private theorem readU8_encode_in_shdr (e : ElfFile)
    (hSync : syncDtStrszInFile e = e)
    (hLay : layoutAlreadyValid e = true)
    (hDisj : e.spliceRegionsDisjoint)
    (k : Nat) (hk : k + 1 ≤ e.sections.size * Layout.shdrSize) :
    Reader.readU8 (encode e) (e.header.shoff.val + k)
      = Reader.readU8 (writeArray SectionHeader.write (e.sections.map toShdr)) k := by
  have hEnc : encode e = encodeBody e := by
    unfold encode; rw [hSync]; simp [hLay]
  rw [hEnc]
  unfold encodeBody
  let total := encodedFileSize e
  let buf0 : ByteArray := zeroBytes total
  let hdrW : ByteArray := ElfHeader.write e.header
  let buf1 : ByteArray := splice buf0 0 hdrW
  let phdrW : ByteArray := writeArray ProgramHeader.write e.phdrs
  let phoff := e.header.phoff.val
  let buf2 : ByteArray := splice buf1 phoff phdrW
  let shdrW : ByteArray := writeArray SectionHeader.write (e.sections.map toShdr)
  let shoff := e.header.shoff.val
  let buf3 : ByteArray := splice buf2 shoff shdrW
  -- Sizes.
  have hBuf0Sz : buf0.size = total := zeroBytes_size total
  have hBuf1Sz : buf1.size = total := by show (splice _ _ _).size = _; rw [splice_size]; exact hBuf0Sz
  have hBuf2Sz : buf2.size = total := by show (splice _ _ _).size = _; rw [splice_size]; exact hBuf1Sz
  have hBuf3Sz : buf3.size = total := by show (splice _ _ _).size = _; rw [splice_size]; exact hBuf2Sz
  have hShdrWSz : shdrW.size = e.sections.size * Layout.shdrSize := by
    show (writeArray _ _).size = _
    rw [writeArray_size_of_uniform SectionHeader.write Layout.shdrSize
            SectionHeader.write_size, Array.size_map]
  -- Region bounds.
  have hShdrEnd : shoff + e.sections.size * Layout.shdrSize ≤ total :=
    shdr_end_le_encodedFileSize e
  -- Splice-fit conditions.
  have hShdrFit : shoff + shdrW.size ≤ buf2.size := by rw [hShdrWSz, hBuf2Sz]; exact hShdrEnd
  -- Read offset r := shoff + k.
  have hrLtTotal : shoff + k < total := by
    have : shoff + k < shoff + e.sections.size * Layout.shdrSize := by omega
    exact Nat.lt_of_lt_of_le this hShdrEnd
  -- Step 1: section foldl preserves byte at `shoff + k`.
  have hStep1 : Reader.readU8
      (e.sections.foldl (init := buf3) sectionFoldStep) (shoff + k)
      = Reader.readU8 buf3 (shoff + k) := by
    apply readU8_foldl_section_splice_preserved e.sections shoff
      (shoff + e.sections.size * Layout.shdrSize) buf3
      (hKAll := ?_) (hrLo := Nat.le_add_right _ _) (hrHi := by omega)
      (hrFit := by rw [hBuf3Sz]; exact hrLtTotal)
    intros i hi
    by_cases hN1 : (e.sections[i]'hi).type = ShType.SHT_NOBITS
    · exact Or.inl hN1
    by_cases hN2 : (e.sections[i]'hi).type = ShType.SHT_NULL
    · exact Or.inr (Or.inl hN2)
    refine Or.inr (Or.inr ⟨?_, ?_⟩)
    · have hSec := hDisj.shdr_sec_disjoint i hi
      rcases hSec with hN | hN | hOK
      · exact absurd hN hN1
      · exact absurd hN hN2
      exact hOK
    · rw [hBuf3Sz]; exact section_end_le_encodedFileSize e i hi hN1 hN2
  -- Step 2: shdr splice INSIDE returns the payload.
  have hStep2 : Reader.readU8 buf3 (shoff + k) = Reader.readU8 shdrW k := by
    show Reader.readU8 (splice buf2 shoff shdrW) (shoff + k) = _
    rw [Reader.readU8_splice_at_off_inside buf2 shoff shdrW hShdrFit (shoff + k)
      (Nat.le_add_right _ _) (by rw [hShdrWSz]; omega)]
    rw [show shoff + k - shoff = k from by omega]
  show Reader.readU8 (e.sections.foldl _ buf3) (shoff + k) = Reader.readU8 shdrW k
  rw [hStep1, hStep2]

/-- `readU16` analog of `readU8_encode_in_shdr`. -/
private theorem readU16_encode_in_shdr (e : ElfFile)
    (hSync : syncDtStrszInFile e = e)
    (hLay : layoutAlreadyValid e = true)
    (hDisj : e.spliceRegionsDisjoint)
    (k : Nat) (hk : k + 2 ≤ e.sections.size * Layout.shdrSize) :
    Reader.readU16 (encode e) (e.header.shoff.val + k)
      = Reader.readU16 (writeArray SectionHeader.write (e.sections.map toShdr)) k := by
  unfold Reader.readU16
  rw [readU8_encode_in_shdr e hSync hLay hDisj k (by omega)]
  rw [show e.header.shoff.val + k + 1 = e.header.shoff.val + (k + 1)
        from by omega,
      readU8_encode_in_shdr e hSync hLay hDisj (k + 1) (by omega)]

/-- `readU32` analog. -/
private theorem readU32_encode_in_shdr (e : ElfFile)
    (hSync : syncDtStrszInFile e = e)
    (hLay : layoutAlreadyValid e = true)
    (hDisj : e.spliceRegionsDisjoint)
    (k : Nat) (hk : k + 4 ≤ e.sections.size * Layout.shdrSize) :
    Reader.readU32 (encode e) (e.header.shoff.val + k)
      = Reader.readU32 (writeArray SectionHeader.write (e.sections.map toShdr)) k := by
  unfold Reader.readU32
  rw [readU8_encode_in_shdr e hSync hLay hDisj k (by omega)]
  rw [show e.header.shoff.val + k + 1 = e.header.shoff.val + (k + 1)
        from by omega,
      readU8_encode_in_shdr e hSync hLay hDisj (k + 1) (by omega)]
  rw [show e.header.shoff.val + k + 2 = e.header.shoff.val + (k + 2)
        from by omega,
      readU8_encode_in_shdr e hSync hLay hDisj (k + 2) (by omega)]
  rw [show e.header.shoff.val + k + 3 = e.header.shoff.val + (k + 3)
        from by omega,
      readU8_encode_in_shdr e hSync hLay hDisj (k + 3) (by omega)]

/-- `readU64` analog. -/
private theorem readU64_encode_in_shdr (e : ElfFile)
    (hSync : syncDtStrszInFile e = e)
    (hLay : layoutAlreadyValid e = true)
    (hDisj : e.spliceRegionsDisjoint)
    (k : Nat) (hk : k + 8 ≤ e.sections.size * Layout.shdrSize) :
    Reader.readU64 (encode e) (e.header.shoff.val + k)
      = Reader.readU64 (writeArray SectionHeader.write (e.sections.map toShdr)) k := by
  unfold Reader.readU64
  rw [readU32_encode_in_shdr e hSync hLay hDisj k (by omega)]
  rw [show e.header.shoff.val + k + 4 = e.header.shoff.val + (k + 4)
        from by omega,
      readU32_encode_in_shdr e hSync hLay hDisj (k + 4) (by omega)]

/-- Per-byte preservation: the i-th byte of `(encode e)` agrees with
    the i-th byte of `writeArray SectionHeader.write (e.sections.map toShdr)`
    when `i ∈ [shoff, shoff + shnum*64)`. -/
private theorem getElem_encode_in_shdr (e : ElfFile)
    (hSync : syncDtStrszInFile e = e)
    (hLay : layoutAlreadyValid e = true)
    (hDisj : e.spliceRegionsDisjoint)
    (k : Nat) (hk : k < e.sections.size * Layout.shdrSize)
    (hI_e : e.header.shoff.val + k < (encode e).size)
    (hI_w : k < (writeArray SectionHeader.write (e.sections.map toShdr)).size) :
    (encode e)[e.header.shoff.val + k]'hI_e
      = (writeArray SectionHeader.write (e.sections.map toShdr))[k]'hI_w := by
  have hRd := readU8_encode_in_shdr e hSync hLay hDisj k (by omega)
  unfold Reader.readU8 at hRd
  rw [dif_pos hI_e, dif_pos hI_w] at hRd
  exact hRd

/-- Extract equality on the shdr region: `(encode e).extract shoff (shoff +
    shnum*64) = writeArray SectionHeader.write (e.sections.map toShdr)`. -/
private theorem extract_encode_eq_shdrs_writer (e : ElfFile)
    (hSync : syncDtStrszInFile e = e)
    (hLay : layoutAlreadyValid e = true)
    (hDisj : e.spliceRegionsDisjoint) :
    (encode e).extract e.header.shoff.val
        (e.header.shoff.val + e.sections.size * Layout.shdrSize)
      = writeArray SectionHeader.write (e.sections.map toShdr) := by
  have hEncSz : (encode e).size = encodedFileSize e := by
    rw [encode_size_eq]; show encodedFileSize _ = _; rw [hSync]; simp [hLay]
  have hShdrWSz : (writeArray SectionHeader.write (e.sections.map toShdr)).size
                  = e.sections.size * Layout.shdrSize := by
    rw [writeArray_size_of_uniform SectionHeader.write Layout.shdrSize
            SectionHeader.write_size, Array.size_map]
  have hShdrEnd : e.header.shoff.val + e.sections.size * Layout.shdrSize
                  ≤ encodedFileSize e := shdr_end_le_encodedFileSize e
  apply ByteArray.ext_getElem
  · rw [ByteArray.size_extract, hEncSz, hShdrWSz]; omega
  · intros i hi _
    rw [ByteArray.size_extract, hEncSz] at hi
    have hi' : i < e.sections.size * Layout.shdrSize := by omega
    simp only [ByteArray.getElem_extract]
    exact getElem_encode_in_shdr e hSync hLay hDisj i hi'
      (by rw [hEncSz]; omega) (by rw [hShdrWSz]; exact hi')

set_option maxHeartbeats 800000 in
/-- The shdr-table decoder on `encode e` recovers the shdr-projection
    of `e.sections`.

    Same composition pattern as `phdrs_decode_encode`:
      * `extract_encode_eq_shdrs_writer` — shdr region of `encode e` is
        `writeArray SectionHeader.write (e.sections.map toShdr)`.
      * `decodeShdr_eq_slice` — window-form decoder bridge.
      * `writeArray_uniform_extract_at_index` — per-element window.
      * `SectionHeader_decode_write` — DSL-emitted forward roundtrip.

    The result `e.sections.map toShdr` matches the
    `DecodeRoundtripWitness.shdrs_decode` field literally (the lambda
    in the witness is `toShdr` inlined). -/
theorem shdrs_decode_encode (e : ElfFile)
    (hSync : syncDtStrszInFile e = e)
    (hLay : layoutAlreadyValid e = true)
    (hDisj : e.spliceRegionsDisjoint)
    (hVal : e.IsValid)
    (hSizeFit : ∀ (i : Nat) (h : i < e.sections.size),
      (e.sections[i]'h).encodedSize < UInt64.size)
    (hShdrFit : ∀ (i : Nat) (h : i < e.sections.size),
      (e.sections[i]'h).addr.val < UInt64.size ∧
      (e.sections[i]'h).offset.val < UInt64.size ∧
      (e.sections[i]'h).addralign.val < UInt64.size ∧
      (e.sections[i]'h).entsize.val < UInt64.size) :
    Patchelf.Elf.Decode.decodeShdrs (encode e)
      e.header.shoff.val e.header.shnum.toNat
      = e.sections.map toShdr := by
  obtain ⟨_, hShnum, _, _, _⟩ := hVal.header_counts
  have hSizeEq : (Decode.decodeShdrs (encode e)
      e.header.shoff.val e.header.shnum.toNat).size
      = (e.sections.map toShdr).size := by
    rw [Decode.decodeShdrs_size, hShnum, Array.size_map]
  apply Array.ext hSizeEq
  intros i hLhs hRhs
  rw [Decode.decodeShdrs_getElem]
  -- hRhs : i < (e.sections.map toShdr).size = e.sections.size
  rw [Array.size_map] at hRhs
  have hi : i < e.sections.size := hRhs
  have hExt := extract_encode_eq_shdrs_writer e hSync hLay hDisj
  have hEncSz : (encode e).size = encodedFileSize e := by
    rw [encode_size_eq]; show encodedFileSize _ = _; rw [hSync]; simp [hLay]
  have hShdrEnd : e.header.shoff.val + e.sections.size * Layout.shdrSize
                  ≤ (encode e).size := by
    rw [hEncSz]; exact shdr_end_le_encodedFileSize e
  have hWinFit : e.header.shoff.val + i * 64 + 64 ≤ (encode e).size := by
    have hSucc : i + 1 ≤ e.sections.size := hi
    have hMul : (i + 1) * 64 ≤ e.sections.size * 64 :=
      Nat.mul_le_mul_right _ hSucc
    rw [Nat.succ_mul] at hMul
    have hShdrSz : Layout.shdrSize = 64 := rfl
    rw [hEncSz]; have hEnd := shdr_end_le_encodedFileSize e
    rw [hShdrSz] at hEnd; omega
  rw [decodeShdr_eq_slice (encode e) (e.header.shoff.val + i * 64) hWinFit]
  have hOuter : e.header.shoff.val + e.sections.size * Layout.shdrSize
                ≤ (encode e).size := hShdrEnd
  have hInner : i * 64 + 64 ≤ e.sections.size * Layout.shdrSize := by
    have hSucc : i + 1 ≤ e.sections.size := hi
    have hMul : (i + 1) * 64 ≤ e.sections.size * 64 :=
      Nat.mul_le_mul_right _ hSucc
    rw [Nat.succ_mul] at hMul
    have hShdrSz : Layout.shdrSize = 64 := rfl
    rw [hShdrSz]; omega
  have hEEW := ByteArray.extract_extract_window (encode e) e.header.shoff.val
                  (e.sections.size * Layout.shdrSize) (i * 64) 64 hOuter hInner
  rw [show (e.header.shoff.val + i * 64 + 64 : Nat)
        = e.header.shoff.val + i * 64 + 64 from rfl]
  rw [← hEEW]
  rw [hExt]
  rw [show (i * 64 + 64 : Nat) = i * Layout.shdrSize + Layout.shdrSize from rfl]
  rw [show (i * 64 : Nat) = i * Layout.shdrSize from rfl]
  rw [writeArray_uniform_extract_at_index Layout.shdrSize SectionHeader.write
        SectionHeader.write_size (e.sections.map toShdr) i (by
          rw [Array.size_map]; exact hi)]
  -- Goal: decodeShdr (((e.sections.map toShdr)[i]).write) 0 = (e.sections.map toShdr)[i]
  have hMapElem : (e.sections.map toShdr)[i]'(by rw [Array.size_map]; exact hi)
                  = toShdr (e.sections[i]'hi) := by
    simp [Array.getElem_map]
  rw [hMapElem]
  obtain ⟨hAddr, hOff, hAlign, hEnt⟩ := hShdrFit i hi
  -- toShdr's `size = ⟨s.encodedSize⟩`, so the size-fit follows from sizeFit.
  have hSize : (toShdr (e.sections[i]'hi)).size.val < UInt64.size := hSizeFit i hi
  exact SectionHeader_decode_write (toShdr (e.sections[i]'hi)) hAddr hOff hSize hAlign hEnt

/-! ## Per-section region recovery through encode

    For non-NOBITS/non-NULL section i, bytes at offsets in
    `[s_i.offset, s_i.offset + s_i.encodedSize)` of `(encode e)`
    recover `s_i.writeContent`.  Composes:
      * `encode e = encodeBody e` (pre-passes are no-ops).
      * `encodeBody e = sections.foldl _ buf3` (matches the encoder body shape).
      * `readU{N}_foldl_section_recovers` — single-shot the entire
        foldl, knowing section i is non-skipped and other sections are
        disjoint from it. -/

private theorem readU8_encode_in_section (e : ElfFile)
    (hSync : syncDtStrszInFile e = e)
    (hLay : layoutAlreadyValid e = true)
    (hDisj : e.spliceRegionsDisjoint)
    (i : Nat) (hi : i < e.sections.size)
    (hType_NB : (e.sections[i]'hi).type ≠ ShType.SHT_NOBITS)
    (hType_NL : (e.sections[i]'hi).type ≠ ShType.SHT_NULL)
    (k : Nat) (hk : k < (e.sections[i]'hi).encodedSize) :
    Reader.readU8 (encode e) ((e.sections[i]'hi).offset.val + k)
      = Reader.readU8 (e.sections[i]'hi).writeContent k := by
  have hEnc : encode e = encodeBody e := by
    unfold encode; rw [hSync]; simp [hLay]
  rw [hEnc]
  unfold encodeBody
  -- Buffer aliases.
  let total := encodedFileSize e
  let buf0 : ByteArray := zeroBytes total
  let hdrW : ByteArray := ElfHeader.write e.header
  let buf1 : ByteArray := splice buf0 0 hdrW
  let phdrW : ByteArray := writeArray ProgramHeader.write e.phdrs
  let phoff := e.header.phoff.val
  let buf2 : ByteArray := splice buf1 phoff phdrW
  let shdrW : ByteArray := writeArray SectionHeader.write (e.sections.map toShdr)
  let shoff := e.header.shoff.val
  let buf3 : ByteArray := splice buf2 shoff shdrW
  have hBuf0Sz : buf0.size = total := zeroBytes_size total
  have hBuf1Sz : buf1.size = total := by show (splice _ _ _).size = _; rw [splice_size]; exact hBuf0Sz
  have hBuf2Sz : buf2.size = total := by show (splice _ _ _).size = _; rw [splice_size]; exact hBuf1Sz
  have hBuf3Sz : buf3.size = total := by show (splice _ _ _).size = _; rw [splice_size]; exact hBuf2Sz
  -- Section i fits in buf3.
  have hSectionFit : (e.sections[i]'hi).offset.val
                  + (e.sections[i]'hi).encodedSize ≤ buf3.size := by
    rw [hBuf3Sz]
    exact section_end_le_encodedFileSize e i hi hType_NB hType_NL
  -- All sections fit (for the hSizesFit precondition).
  have hAllSizesFit : ∀ (j : Nat) (hj : j < e.sections.size),
      (e.sections[j]'hj).type = ShType.SHT_NOBITS ∨
      (e.sections[j]'hj).type = ShType.SHT_NULL ∨
      (e.sections[j]'hj).offset.val
        + (e.sections[j]'hj).encodedSize ≤ buf3.size := by
    intros j hj
    by_cases hN1 : (e.sections[j]'hj).type = ShType.SHT_NOBITS
    · exact Or.inl hN1
    by_cases hN2 : (e.sections[j]'hj).type = ShType.SHT_NULL
    · exact Or.inr (Or.inl hN2)
    refine Or.inr (Or.inr ?_)
    rw [hBuf3Sz]
    exact section_end_le_encodedFileSize e j hj hN1 hN2
  -- Other sections disjoint from section i (from sectionsNonOverlapping).
  have hOverlap : ∀ (j : Nat) (hj : j < e.sections.size), i ≠ j →
      (e.sections[j]'hj).type = ShType.SHT_NOBITS ∨
      (e.sections[j]'hj).type = ShType.SHT_NULL ∨
      IntervalDisjoint
        (e.sections[j]'hj).offset.val
        ((e.sections[j]'hj).offset.val + (e.sections[j]'hj).encodedSize)
        (e.sections[i]'hi).offset.val
        ((e.sections[i]'hi).offset.val + (e.sections[i]'hi).encodedSize) := by
    intros j hj hij
    have hSec := hDisj.sections_disjoint j hj i hi (Ne.symm hij)
    -- hSec gives: NOBITS_j ∨ NOBITS_i ∨ NULL_j ∨ NULL_i ∨ Disjoint.
    rcases hSec with hN | hN | hN | hN | hOK
    · exact Or.inl hN
    · exact absurd hN hType_NB
    · exact Or.inr (Or.inl hN)
    · exact absurd hN hType_NL
    · exact Or.inr (Or.inr hOK)
  -- Apply readU8_foldl_section_recovers.
  exact readU8_foldl_section_recovers e.sections buf3 i hi hType_NB hType_NL
    hSectionFit hOverlap hAllSizesFit k hk

private theorem readU16_encode_in_section (e : ElfFile)
    (hSync : syncDtStrszInFile e = e)
    (hLay : layoutAlreadyValid e = true)
    (hDisj : e.spliceRegionsDisjoint)
    (i : Nat) (hi : i < e.sections.size)
    (hType_NB : (e.sections[i]'hi).type ≠ ShType.SHT_NOBITS)
    (hType_NL : (e.sections[i]'hi).type ≠ ShType.SHT_NULL)
    (k : Nat) (hk : k + 2 ≤ (e.sections[i]'hi).encodedSize) :
    Reader.readU16 (encode e) ((e.sections[i]'hi).offset.val + k)
      = Reader.readU16 (e.sections[i]'hi).writeContent k := by
  unfold Reader.readU16
  rw [readU8_encode_in_section e hSync hLay hDisj i hi hType_NB hType_NL k (by omega)]
  rw [show (e.sections[i]'hi).offset.val + k + 1
        = (e.sections[i]'hi).offset.val + (k + 1) from by omega,
      readU8_encode_in_section e hSync hLay hDisj i hi hType_NB hType_NL (k + 1) (by omega)]

/-! ## Per-content-type roundtrips

    For each `Section.content` constructor, prove that decoding the
    encoder's payload recovers the original content. -/

/-- Reading `s.encodedSize` bytes of `s.writeContent` recovers a buffer
    of that size, from offset 0.  This trivially captures the splice
    payload's bytes. -/
private theorem readBytes_writeContent_eq (s : Section)
    (hSize : s.writeContent.size = s.encodedSize) :
    Reader.readBytes s.writeContent 0 s.encodedSize = s.writeContent := by
  unfold Reader.readBytes
  rw [show 0 + s.encodedSize = s.encodedSize from by omega]
  apply ByteArray.ext_getElem
  · rw [ByteArray.size_extract, hSize]; omega
  · intros j hj _
    rw [ByteArray.getElem_extract]
    show s.writeContent[0 + j]'_ = s.writeContent[j]'_
    congr 1; omega

/-- Reading bytes from `(encode e)` at section i's region recovers
    `s_i.writeContent`, given the standard preconditions and section i
    being non-NOBITS/non-NULL. -/
private theorem readBytes_encode_in_section (e : ElfFile)
    (hSync : syncDtStrszInFile e = e)
    (hLay : layoutAlreadyValid e = true)
    (hDisj : e.spliceRegionsDisjoint)
    (i : Nat) (hi : i < e.sections.size)
    (hType_NB : (e.sections[i]'hi).type ≠ ShType.SHT_NOBITS)
    (hType_NL : (e.sections[i]'hi).type ≠ ShType.SHT_NULL) :
    Reader.readBytes (encode e) (e.sections[i]'hi).offset.val
        (e.sections[i]'hi).encodedSize
      = (e.sections[i]'hi).writeContent := by
  have hEncSz : (encode e).size = encodedFileSize e := by
    rw [encode_size_eq]; show encodedFileSize _ = _; rw [hSync]; simp [hLay]
  have hSecEnd : (e.sections[i]'hi).offset.val
                + (e.sections[i]'hi).encodedSize ≤ (encode e).size := by
    rw [hEncSz]
    exact section_end_le_encodedFileSize e i hi hType_NB hType_NL
  have hWcSz : (e.sections[i]'hi).writeContent.size
              = (e.sections[i]'hi).encodedSize :=
    Section_writeContent_size_eq _
  unfold Reader.readBytes
  apply ByteArray.ext_getElem
  · rw [ByteArray.size_extract, hWcSz]; omega
  · intros j hj _
    rw [ByteArray.size_extract] at hj
    have hjN : j < (e.sections[i]'hi).encodedSize := by omega
    rw [ByteArray.getElem_extract]
    have hRd := readU8_encode_in_section e hSync hLay hDisj i hi
                  hType_NB hType_NL j hjN
    unfold Reader.readU8 at hRd
    rw [dif_pos (by omega), dif_pos (by rw [hWcSz]; exact hjN)] at hRd
    exact hRd

/-! ## Forward roundtrip for `decodeDynamic`

    For a non-empty `ds : Array DynEntry` whose last entry has
    `tag = .null` and where no earlier entry has `tag = .null`,
    decoding the writeArray-encoded bytes recovers `ds`.

    Used by `section_decode_encode` to discharge the `.dynamic ds`
    case. -/

/-- Per-element decoder bridge for dynamic entries. -/
private theorem decodeDynEntry_writeArray_at_index (arr : Array DynEntry)
    (i : Nat) (hi : i < arr.size) :
    Decode.decodeDynEntry (writeArray DynEntry.write arr) (i * Layout.dynEntrySize)
      = arr[i]'hi := by
  have hWaSz : (writeArray DynEntry.write arr).size = arr.size * Layout.dynEntrySize :=
    writeArray_size_of_uniform DynEntry.write Layout.dynEntrySize
            DynEntry.write_size arr
  have hDynSz : Layout.dynEntrySize = 16 := rfl
  have hFitBy16 : i * Layout.dynEntrySize + 16 ≤ (writeArray DynEntry.write arr).size := by
    rw [hWaSz]
    have hSucc : i + 1 ≤ arr.size := hi
    have hMul : (i + 1) * 16 ≤ arr.size * 16 := Nat.mul_le_mul_right _ hSucc
    rw [Nat.succ_mul] at hMul
    rw [hDynSz]; omega
  rw [decodeDynEntry_eq_slice (writeArray DynEntry.write arr)
      (i * Layout.dynEntrySize) hFitBy16]
  rw [show (i * Layout.dynEntrySize + 16 : Nat)
        = i * Layout.dynEntrySize + Layout.dynEntrySize from by rw [hDynSz]]
  rw [writeArray_uniform_extract_at_index Layout.dynEntrySize DynEntry.write
        DynEntry.write_size arr i hi]
  exact DynEntry_decode_write (arr[i]'hi)

/-- Loop-induction: starting from index `i` with accumulator
    `arr.extract 0 i`, the loop appends entries `i, i+1, ...` and
    terminates when it sees the DT_NULL entry at `arr.size - 1`. -/
private theorem decodeDynamicLoop_writeArray_step
    (arr : Array DynEntry) (hSizePos : 0 < arr.size)
    (hLastNull : (arr[arr.size - 1]'(by omega)).tag = DynTag.null)
    (hNoEarlyNull : ∀ (j : Nat) (h : j < arr.size),
      (arr[j]'h).tag = DynTag.null → j = arr.size - 1) :
    ∀ (i : Nat) (hi : i ≤ arr.size - 1),
      Decode.decodeDynamicLoop (writeArray DynEntry.write arr) 0
          arr.size i (arr.extract 0 i) = arr := by
  intro i hi
  -- Strong induction on `arr.size - 1 - i`.
  let n := arr.size - 1 - i
  have hn : arr.size - 1 - i = n := rfl
  clear_value n
  induction n generalizing i with
  | zero =>
    -- arr.size - 1 - i = 0 → i = arr.size - 1.
    have hiEq : i = arr.size - 1 := by omega
    subst hiEq
    unfold Decode.decodeDynamicLoop
    have hiLt : arr.size - 1 < arr.size := by omega
    rw [dif_neg (Nat.not_le.mpr hiLt)]
    have hReadE : Decode.decodeDynEntry (writeArray DynEntry.write arr)
                    (0 + (arr.size - 1) * Layout.dynEntrySize)
                  = arr[arr.size - 1]'hiLt := by
      rw [show 0 + (arr.size - 1) * Layout.dynEntrySize
            = (arr.size - 1) * Layout.dynEntrySize from by omega]
      exact decodeDynEntry_writeArray_at_index arr (arr.size - 1) hiLt
    simp only [hReadE]
    rw [hLastNull]
    -- Goal: (arr.extract 0 (arr.size - 1)).push arr[arr.size - 1] = arr.
    apply Array.ext
    · rw [Array.size_push, Array.size_extract]; omega
    · intros j hj _
      rw [Array.size_push, Array.size_extract] at hj
      have hjLt : j < arr.size := by
        have : min (arr.size - 1) arr.size = arr.size - 1 := by omega
        rw [this] at hj; omega
      rw [Array.getElem_push]
      split <;> rename_i hjBound
      · rw [Array.size_extract] at hjBound
        have hjLtI : j < arr.size - 1 := by
          have : min (arr.size - 1) arr.size = arr.size - 1 := by omega
          rw [this] at hjBound; exact hjBound
        rw [Array.getElem_extract]
        show arr[0 + j]'(by omega) = arr[j]'hjLt
        congr 1; omega
      · rw [Array.size_extract] at hjBound
        have : min (arr.size - 1) arr.size = arr.size - 1 := by omega
        rw [this] at hjBound
        have hjEqI : j = arr.size - 1 := by omega
        subst hjEqI; rfl
  | succ k ih =>
    -- arr.size - 1 - i = k + 1, so i < arr.size - 1.
    unfold Decode.decodeDynamicLoop
    have hiLt : i < arr.size := by omega
    have hiLtSize1 : i < arr.size - 1 := by omega
    rw [dif_neg (Nat.not_le.mpr hiLt)]
    have hReadE : Decode.decodeDynEntry (writeArray DynEntry.write arr)
                    (0 + i * Layout.dynEntrySize) = arr[i]'hiLt := by
      rw [show 0 + i * Layout.dynEntrySize = i * Layout.dynEntrySize from by omega]
      exact decodeDynEntry_writeArray_at_index arr i hiLt
    simp only [hReadE]
    have hT : (arr[i]'hiLt).tag ≠ DynTag.null := by
      intro hN
      have := hNoEarlyNull i hiLt hN
      omega
    -- The match on arr[i].tag goes to the recursive branch.  Replace
    -- the entire match with the recursive call by case-splitting on the
    -- tag, which (since not .null) always lands on the catchall branch.
    -- Use `split` on the goal to dispatch.
    split
    · rename_i hN; exact absurd hN hT
    -- Catchall branch.
    have hAccNext : (arr.extract 0 i).push (arr[i]'hiLt) = arr.extract 0 (i + 1) := by
      apply Array.ext
      · rw [Array.size_push, Array.size_extract, Array.size_extract]; omega
      · intros j hj _
        rw [Array.size_push, Array.size_extract] at hj
        have hjBound : j < i + 1 := by
          have : min i arr.size = i := by omega
          rw [this] at hj; omega
        rw [Array.getElem_push]
        split <;> rename_i hjPush
        · rw [Array.size_extract] at hjPush
          have hjLtI : j < i := by
            have : min i arr.size = i := by omega
            rw [this] at hjPush; exact hjPush
          rw [Array.getElem_extract, Array.getElem_extract]
        · rw [Array.size_extract] at hjPush
          have hMin : min i arr.size = i := by omega
          rw [hMin] at hjPush
          have hjEqI : j = i := by omega
          rw [Array.getElem_extract]
          show arr[i]'hiLt = arr[0 + j]'_
          congr 1; omega
    rw [hAccNext]
    -- Recursive call: arr.size - 1 - (i+1) = k.
    have hNNext : arr.size - 1 - (i + 1) = k := by omega
    have hINext : i + 1 ≤ arr.size - 1 := by omega
    exact ih (i + 1) hINext hNNext

theorem decodeDynamic_writeArray_eq (ds : Array DynEntry)
    (hSizePos : 0 < ds.size)
    (hLastNull : (ds[ds.size - 1]'(by omega)).tag = DynTag.null)
    (hNoEarlyNull : ∀ (j : Nat) (h : j < ds.size),
      (ds[j]'h).tag = DynTag.null → j = ds.size - 1) :
    Decode.decodeDynamic (writeArray DynEntry.write ds) 0 ds.size = ds := by
  unfold Decode.decodeDynamic
  have hInit : (#[] : Array DynEntry) = ds.extract 0 0 := by
    apply Array.ext
    · simp [Array.size_extract]
    · intros j hj _
      simp at hj
  rw [hInit]
  exact decodeDynamicLoop_writeArray_step ds hSizePos hLastNull hNoEarlyNull 0 (by omega)

/-- `decodeDynamicLoop` only inspects bytes via per-entry decodes; if
    two buffers/offsets agree on every per-entry decode in the
    iteration range, the loop produces equal outputs. -/
private theorem decodeDynamicLoop_congr
    (bs1 bs2 : ByteArray) (baseOff1 baseOff2 maxCount : Nat)
    (hAgree : ∀ (j : Nat), j < maxCount →
      Decode.decodeDynEntry bs1 (baseOff1 + j * Layout.dynEntrySize)
      = Decode.decodeDynEntry bs2 (baseOff2 + j * Layout.dynEntrySize)) :
    ∀ (i : Nat) (acc : Array DynEntry),
      Decode.decodeDynamicLoop bs1 baseOff1 maxCount i acc
      = Decode.decodeDynamicLoop bs2 baseOff2 maxCount i acc := by
  intro i acc
  let n := maxCount - i
  have hn : maxCount - i = n := rfl
  clear_value n
  induction n generalizing i acc with
  | zero =>
    have hiGe : i ≥ maxCount := by omega
    unfold Decode.decodeDynamicLoop
    rw [dif_pos hiGe, dif_pos hiGe]
  | succ k ih =>
    have hiLt : i < maxCount := by omega
    unfold Decode.decodeDynamicLoop
    rw [dif_neg (Nat.not_le.mpr hiLt), dif_neg (Nat.not_le.mpr hiLt)]
    rw [hAgree i hiLt]
    -- After this, both sides start with `let e := decodeDynEntry bs2 ...`,
    -- diverging only in the catchall recursive call (bs1 vs bs2).
    have hNNext : maxCount - (i + 1) = k := by omega
    cases hT : (Decode.decodeDynEntry bs2 (baseOff2 + i * Layout.dynEntrySize)).tag with
    | null => simp only [hT]
    | _ => simp only [hT]; exact ih (i + 1) _ hNNext

/-- `decodeDynamic` agrees on two buffers when per-entry decodes agree
    over the iteration range. -/
private theorem decodeDynamic_congr
    (bs1 bs2 : ByteArray) (baseOff1 baseOff2 maxCount : Nat)
    (hAgree : ∀ (j : Nat), j < maxCount →
      Decode.decodeDynEntry bs1 (baseOff1 + j * Layout.dynEntrySize)
      = Decode.decodeDynEntry bs2 (baseOff2 + j * Layout.dynEntrySize)) :
    Decode.decodeDynamic bs1 baseOff1 maxCount
    = Decode.decodeDynamic bs2 baseOff2 maxCount := by
  unfold Decode.decodeDynamic
  exact decodeDynamicLoop_congr bs1 bs2 baseOff1 baseOff2 maxCount hAgree 0 #[]

/-! ## .dynamic section discharge

    Composes `decodeDynamic_congr` (bridge encoder bytes to writeArray
    bytes) with `decodeDynamic_writeArray_eq` (the loop induction). -/

private theorem decodeDynamic_encode_dynamic (e : ElfFile)
    (hSync : syncDtStrszInFile e = e)
    (hLay : layoutAlreadyValid e = true)
    (hDisj : e.spliceRegionsDisjoint)
    (i : Nat) (hi : i < e.sections.size)
    (hType_NB : (e.sections[i]'hi).type ≠ ShType.SHT_NOBITS)
    (hType_NL : (e.sections[i]'hi).type ≠ ShType.SHT_NULL)
    (ds : Array DynEntry)
    (hContent : (e.sections[i]'hi).content = .dynamic ds)
    (hSizePos : 0 < ds.size)
    (hLastNull : (ds[ds.size - 1]'(by omega)).tag = DynTag.null)
    (hNoEarlyNull : ∀ (j : Nat) (h : j < ds.size),
      (ds[j]'h).tag = DynTag.null → j = ds.size - 1) :
    Decode.decodeDynamic (encode e) (e.sections[i]'hi).offset.val
        ((e.sections[i]'hi).encodedSize / Layout.dynEntrySize)
      = ds := by
  have hDynSz : Layout.dynEntrySize = 16 := rfl
  have hEncSize : (e.sections[i]'hi).encodedSize = ds.size * Layout.dynEntrySize := by
    unfold Section.encodedSize; rw [hContent]
  have hCount : (e.sections[i]'hi).encodedSize / Layout.dynEntrySize = ds.size := by
    rw [hEncSize, Nat.mul_div_cancel _ (by decide : 0 < Layout.dynEntrySize)]
  rw [hCount]
  have hWriteContent : (e.sections[i]'hi).writeContent
                       = writeArray DynEntry.write ds := by
    unfold Section.writeContent; rw [hContent]
  have hWcSz : (e.sections[i]'hi).writeContent.size = (e.sections[i]'hi).encodedSize :=
    Section_writeContent_size_eq _
  have hSecEnd : (e.sections[i]'hi).offset.val
                + (e.sections[i]'hi).encodedSize ≤ (encode e).size := by
    have hEncSz : (encode e).size = encodedFileSize e := by
      rw [encode_size_eq]; show encodedFileSize _ = _; rw [hSync]; simp [hLay]
    rw [hEncSz]
    exact section_end_le_encodedFileSize e i hi hType_NB hType_NL
  -- Per-entry agreement: decodeDynEntry on (encode e) at section
  -- offset matches decodeDynEntry on writeArray at offset 0.
  have hAgree : ∀ (j : Nat), j < ds.size →
      Decode.decodeDynEntry (encode e)
        ((e.sections[i]'hi).offset.val + j * Layout.dynEntrySize)
      = Decode.decodeDynEntry (writeArray DynEntry.write ds)
        (0 + j * Layout.dynEntrySize) := by
    intros j hj
    have hWinFit : (e.sections[i]'hi).offset.val + j * 16 + 16
                   ≤ (encode e).size := by
      have hSucc : j + 1 ≤ ds.size := hj
      have hMul : (j + 1) * 16 ≤ ds.size * 16 := Nat.mul_le_mul_right _ hSucc
      rw [Nat.succ_mul] at hMul
      rw [hEncSize, hDynSz] at hSecEnd
      omega
    rw [show (e.sections[i]'hi).offset.val + j * Layout.dynEntrySize
          = (e.sections[i]'hi).offset.val + j * 16 from by rw [hDynSz]]
    rw [decodeDynEntry_eq_slice (encode e)
          ((e.sections[i]'hi).offset.val + j * 16) hWinFit]
    have hOuter : (e.sections[i]'hi).offset.val
                  + (e.sections[i]'hi).encodedSize ≤ (encode e).size := hSecEnd
    have hInner : j * 16 + 16 ≤ (e.sections[i]'hi).encodedSize := by
      rw [hEncSize, hDynSz]
      have hSucc : j + 1 ≤ ds.size := hj
      have hMul : (j + 1) * 16 ≤ ds.size * 16 := Nat.mul_le_mul_right _ hSucc
      rw [Nat.succ_mul] at hMul; omega
    have hExtSection : (encode e).extract (e.sections[i]'hi).offset.val
        ((e.sections[i]'hi).offset.val + (e.sections[i]'hi).encodedSize)
        = (e.sections[i]'hi).writeContent := by
      apply ByteArray.ext_getElem
      · rw [ByteArray.size_extract, hWcSz]
        have hEncSz : (encode e).size = encodedFileSize e := by
          rw [encode_size_eq]; show encodedFileSize _ = _; rw [hSync]; simp [hLay]
        rw [hEncSz]
        have := section_end_le_encodedFileSize e i hi hType_NB hType_NL
        omega
      · intros r hr _
        have hEncSz : (encode e).size = encodedFileSize e := by
          rw [encode_size_eq]; show encodedFileSize _ = _; rw [hSync]; simp [hLay]
        rw [ByteArray.size_extract, hEncSz] at hr
        have hrSec : r < (e.sections[i]'hi).encodedSize := by
          have := section_end_le_encodedFileSize e i hi hType_NB hType_NL
          omega
        rw [ByteArray.getElem_extract]
        have hRd := readU8_encode_in_section e hSync hLay hDisj i hi
                      hType_NB hType_NL r hrSec
        unfold Reader.readU8 at hRd
        rw [dif_pos (by
              rw [hEncSz]
              have := section_end_le_encodedFileSize e i hi hType_NB hType_NL
              omega),
            dif_pos (by rw [hWcSz]; exact hrSec)] at hRd
        exact hRd
    have hEEW := ByteArray.extract_extract_window (encode e)
                    (e.sections[i]'hi).offset.val
                    (e.sections[i]'hi).encodedSize (j * 16) 16 hOuter hInner
    rw [show ((e.sections[i]'hi).offset.val + j * 16 + 16 : Nat)
          = (e.sections[i]'hi).offset.val + j * 16 + 16 from rfl]
    rw [← hEEW]
    rw [hExtSection]
    rw [hWriteContent]
    -- Goal: decodeDynEntry ((writeArray ... ds).extract (j*16) (j*16+16)) 0
    --     = decodeDynEntry (writeArray ... ds) (0 + j * dynEntrySize)
    rw [show 0 + j * Layout.dynEntrySize = j * Layout.dynEntrySize from by omega]
    have hWaFit : j * Layout.dynEntrySize + Layout.dynEntrySize
                ≤ (writeArray DynEntry.write ds).size := by
      rw [writeArray_size_of_uniform DynEntry.write Layout.dynEntrySize
            DynEntry.write_size]
      have hSucc : j + 1 ≤ ds.size := hj
      have hMul : (j + 1) * Layout.dynEntrySize ≤ ds.size * Layout.dynEntrySize :=
        Nat.mul_le_mul_right _ hSucc
      rw [Nat.succ_mul] at hMul; omega
    rw [show (j * 16 + 16 : Nat) = j * Layout.dynEntrySize + Layout.dynEntrySize
          from by rw [hDynSz]]
    rw [show (j * 16 : Nat) = j * Layout.dynEntrySize from by rw [hDynSz]]
    rw [decodeDynEntry_eq_slice (writeArray DynEntry.write ds)
          (j * Layout.dynEntrySize) (by rw [hDynSz] at hWaFit ⊢; exact hWaFit)]
    congr 1
  rw [decodeDynamic_congr (encode e) (writeArray DynEntry.write ds)
        (e.sections[i]'hi).offset.val 0 ds.size hAgree]
  exact decodeDynamic_writeArray_eq ds hSizePos hLastNull hNoEarlyNull

/-! ## Per-content-type decoder roundtrips (.dynsym, .versym)

    For the bulk-array contents `.dynsym` and `.versym`, decoding the
    encoded payload recovers the original array.  Same composition
    template as `decodePhdr_writeArray_at_index`. -/

/-- Per-element decoder bridge for symbols. -/
private theorem decodeSym_writeArray_at_index (arr : Array Symbol)
    (i : Nat) (hi : i < arr.size) :
    Decode.decodeSym (writeArray Symbol.write arr) (i * Layout.symEntrySize)
      = arr[i]'hi := by
  have hWaSz : (writeArray Symbol.write arr).size = arr.size * Layout.symEntrySize :=
    writeArray_size_of_uniform Symbol.write Layout.symEntrySize
            Symbol.write_size arr
  have hSymSz : Layout.symEntrySize = 24 := rfl
  have hFitBy24 : i * Layout.symEntrySize + 24 ≤ (writeArray Symbol.write arr).size := by
    rw [hWaSz]
    have hSucc : i + 1 ≤ arr.size := hi
    have hMul : (i + 1) * 24 ≤ arr.size * 24 :=
      Nat.mul_le_mul_right _ hSucc
    rw [Nat.succ_mul] at hMul
    rw [hSymSz]; omega
  rw [decodeSym_eq_slice (writeArray Symbol.write arr) (i * Layout.symEntrySize) hFitBy24]
  rw [show (i * Layout.symEntrySize + 24 : Nat)
        = i * Layout.symEntrySize + Layout.symEntrySize from by rw [hSymSz]]
  rw [writeArray_uniform_extract_at_index Layout.symEntrySize Symbol.write
        Symbol.write_size arr i hi]
  exact Symbol_decode_write (arr[i]'hi)

/-- Per-element decoder bridge for `.versym` (UInt16 array). -/
private theorem readU16_writeArray_writeU16_at (vs : Array UInt16)
    (i : Nat) (hi : i < vs.size) :
    Reader.readU16 (writeArray Writer.writeU16 vs) (i * 2) = vs[i]'hi :=
  readU16_writeArray vs i hi

/-! ## .versym section discharge

    For a `.versym vs`-content section, decoding via `decodeVersym`
    recovers `vs`.  Composes:
      * `decodeVersym = buildArray n (fun i => readU16 bs (off + i*2))`
      * Per-byte preservation `readU16_encode_in_section`
      * `readU16_writeArray` to bridge back to per-element.

    `Section.encodedSize = vs.size * 2` from `Section.encodedSize` on `.versym`. -/
private theorem decodeVersym_encode_versym (e : ElfFile)
    (hSync : syncDtStrszInFile e = e)
    (hLay : layoutAlreadyValid e = true)
    (hDisj : e.spliceRegionsDisjoint)
    (i : Nat) (hi : i < e.sections.size)
    (hType_NB : (e.sections[i]'hi).type ≠ ShType.SHT_NOBITS)
    (hType_NL : (e.sections[i]'hi).type ≠ ShType.SHT_NULL)
    (vs : Array UInt16)
    (hContent : (e.sections[i]'hi).content = .versym vs) :
    Decode.decodeVersym (encode e) (e.sections[i]'hi).offset.val
        ((e.sections[i]'hi).encodedSize / 2)
      = vs := by
  have hEncSize : (e.sections[i]'hi).encodedSize = vs.size * 2 := by
    show (e.sections[i]'hi).encodedSize = vs.size * 2
    unfold Section.encodedSize; rw [hContent]
  have hCount : (e.sections[i]'hi).encodedSize / 2 = vs.size := by
    rw [hEncSize, Nat.mul_div_cancel _ (by decide : 0 < 2)]
  rw [hCount]
  have hWriteContent : (e.sections[i]'hi).writeContent
                       = writeArray Writer.writeU16 vs := by
    unfold Section.writeContent; rw [hContent]
  -- decodeVersym = buildArray vs.size (fun j => readU16 bs (off + j*2))
  unfold Decode.decodeVersym
  -- Use buildArray_size + buildArray_getElem to match each element.
  apply Array.ext
  · rw [Decode.buildArray_size]
  · intros j hLhs hRhs
    rw [Decode.buildArray_getElem]
    -- Goal: readU16 (encode e) (s.offset + j * 2) = vs[j]
    have hjSz : j < vs.size := by
      rw [Decode.buildArray_size] at hLhs; exact hLhs
    have hkBound : j * 2 + 2 ≤ (e.sections[i]'hi).encodedSize := by
      rw [hEncSize]
      have hSucc : j + 1 ≤ vs.size := hjSz
      have := Nat.mul_le_mul_right 2 hSucc
      rw [Nat.succ_mul] at this; omega
    rw [readU16_encode_in_section e hSync hLay hDisj i hi hType_NB hType_NL
          (j * 2) hkBound]
    rw [hWriteContent]
    exact readU16_writeArray vs j hjSz

/-! ## .dynsym section discharge

    For a `.dynsym syms`-content section, decoding via `decodeDynsym`
    recovers `syms`.  Mirrors `phdrs_decode_encode` exactly, swapping
    Phdr/Sym artifacts. -/
private theorem decodeDynsym_encode_dynsym (e : ElfFile)
    (hSync : syncDtStrszInFile e = e)
    (hLay : layoutAlreadyValid e = true)
    (hDisj : e.spliceRegionsDisjoint)
    (i : Nat) (hi : i < e.sections.size)
    (hType_NB : (e.sections[i]'hi).type ≠ ShType.SHT_NOBITS)
    (hType_NL : (e.sections[i]'hi).type ≠ ShType.SHT_NULL)
    (syms : Array Symbol)
    (hContent : (e.sections[i]'hi).content = .dynsym syms) :
    Decode.decodeDynsym (encode e) (e.sections[i]'hi).offset.val
        ((e.sections[i]'hi).encodedSize / Layout.symEntrySize)
      = syms := by
  have hSymSz : Layout.symEntrySize = 24 := rfl
  have hEncSize : (e.sections[i]'hi).encodedSize = syms.size * Layout.symEntrySize := by
    unfold Section.encodedSize; rw [hContent]
  have hCount : (e.sections[i]'hi).encodedSize / Layout.symEntrySize = syms.size := by
    rw [hEncSize, Nat.mul_div_cancel _ (by decide : 0 < Layout.symEntrySize)]
  rw [hCount]
  have hWriteContent : (e.sections[i]'hi).writeContent
                       = writeArray Symbol.write syms := by
    unfold Section.writeContent; rw [hContent]
  -- Per-element via Array.ext + decodeDynsym_getElem.
  apply Array.ext
  · rw [Decode.decodeDynsym_size]
  · intros j hLhs hRhs
    have hjSz : j < syms.size := by
      rw [Decode.decodeDynsym_size] at hLhs; exact hLhs
    rw [Decode.decodeDynsym_getElem]
    -- Goal: decodeSym (encode e) (s.offset + j * 24) = syms[j]
    -- Step 1: decodeSym_eq_slice on the encoder side.
    have hSucc : j + 1 ≤ syms.size := hjSz
    have hMul : (j + 1) * 24 ≤ syms.size * 24 := Nat.mul_le_mul_right _ hSucc
    rw [Nat.succ_mul] at hMul
    have hSecEnd : (e.sections[i]'hi).offset.val
                  + (e.sections[i]'hi).encodedSize ≤ (encode e).size := by
      have hEncSz : (encode e).size = encodedFileSize e := by
        rw [encode_size_eq]; show encodedFileSize _ = _; rw [hSync]; simp [hLay]
      rw [hEncSz]
      exact section_end_le_encodedFileSize e i hi hType_NB hType_NL
    have hWinFit : (e.sections[i]'hi).offset.val + j * 24 + 24
                   ≤ (encode e).size := by
      have hLitSz : Layout.symEntrySize = 24 := rfl
      rw [hEncSize, hLitSz] at hSecEnd; omega
    rw [decodeSym_eq_slice (encode e)
          ((e.sections[i]'hi).offset.val + j * 24) hWinFit]
    -- Step 2: bridge encoder window → s.writeContent window.
    have hWcSz : (e.sections[i]'hi).writeContent.size
                 = (e.sections[i]'hi).encodedSize :=
      Section_writeContent_size_eq _
    -- Build extract_encode_eq_section_writer (specialized to this section).
    have hExtSection : (encode e).extract (e.sections[i]'hi).offset.val
        ((e.sections[i]'hi).offset.val + (e.sections[i]'hi).encodedSize)
        = (e.sections[i]'hi).writeContent := by
      apply ByteArray.ext_getElem
      · rw [ByteArray.size_extract, hWcSz]
        have hEncSz : (encode e).size = encodedFileSize e := by
          rw [encode_size_eq]; show encodedFileSize _ = _; rw [hSync]; simp [hLay]
        rw [hEncSz]
        have := section_end_le_encodedFileSize e i hi hType_NB hType_NL
        omega
      · intros r hr _
        have hEncSz : (encode e).size = encodedFileSize e := by
          rw [encode_size_eq]; show encodedFileSize _ = _; rw [hSync]; simp [hLay]
        rw [ByteArray.size_extract, hEncSz] at hr
        have hrSec : r < (e.sections[i]'hi).encodedSize := by
          have := section_end_le_encodedFileSize e i hi hType_NB hType_NL
          omega
        rw [ByteArray.getElem_extract]
        have hRd := readU8_encode_in_section e hSync hLay hDisj i hi
                      hType_NB hType_NL r hrSec
        unfold Reader.readU8 at hRd
        rw [dif_pos (by
              rw [hEncSz]
              have := section_end_le_encodedFileSize e i hi hType_NB hType_NL
              omega),
            dif_pos (by rw [hWcSz]; exact hrSec)] at hRd
        exact hRd
    -- extract_extract_window: bridge encoder element-window to
    -- writeArray element-window.
    have hOuter : (e.sections[i]'hi).offset.val
                  + (e.sections[i]'hi).encodedSize ≤ (encode e).size := hSecEnd
    have hInner : j * 24 + 24 ≤ (e.sections[i]'hi).encodedSize := by
      rw [hEncSize]
      have : Layout.symEntrySize = 24 := rfl
      rw [this] at *; omega
    have hEEW := ByteArray.extract_extract_window (encode e)
                    (e.sections[i]'hi).offset.val
                    (e.sections[i]'hi).encodedSize (j * 24) 24 hOuter hInner
    rw [show ((e.sections[i]'hi).offset.val + j * 24 + 24 : Nat)
          = (e.sections[i]'hi).offset.val + j * 24 + 24 from rfl]
    rw [← hEEW]
    rw [hExtSection]
    rw [hWriteContent]
    rw [show (j * 24 + 24 : Nat) = j * Layout.symEntrySize + Layout.symEntrySize from rfl]
    rw [show (j * 24 : Nat) = j * Layout.symEntrySize from rfl]
    rw [writeArray_uniform_extract_at_index Layout.symEntrySize Symbol.write
          Symbol.write_size syms j hjSz]
    exact Symbol_decode_write (syms[j]'hjSz)

/-! ## .strtab section discharge -/

private theorem decodeStringTable_encode_strtab (e : ElfFile)
    (hSync : syncDtStrszInFile e = e)
    (hLay : layoutAlreadyValid e = true)
    (hDisj : e.spliceRegionsDisjoint)
    (i : Nat) (hi : i < e.sections.size)
    (hType_NB : (e.sections[i]'hi).type ≠ ShType.SHT_NOBITS)
    (hType_NL : (e.sections[i]'hi).type ≠ ShType.SHT_NULL)
    (st : StringTable)
    (hContent : (e.sections[i]'hi).content = .strtab st) :
    Decode.decodeStringTable (encode e) (e.sections[i]'hi).offset.val
        (e.sections[i]'hi).encodedSize
      = st := by
  have hEncSize : (e.sections[i]'hi).encodedSize = st.bytes.size := by
    show (e.sections[i]'hi).encodedSize = st.bytes.size
    unfold Section.encodedSize; rw [hContent]
  have hWriteContent : (e.sections[i]'hi).writeContent = st.bytes := by
    unfold Section.writeContent; rw [hContent]
  unfold Decode.decodeStringTable
  -- Goal: ⟨readBytes (encode e) s.offset s.encodedSize⟩ = st
  show { bytes := Reader.readBytes (encode e) (e.sections[i]'hi).offset.val
                    (e.sections[i]'hi).encodedSize } = st
  have hReadBytes := readBytes_encode_in_section e hSync hLay hDisj i hi
                       hType_NB hType_NL
  rw [hReadBytes, hWriteContent]

/-! ## .raw section discharge -/

private theorem decodeRaw_encode_raw (e : ElfFile)
    (hSync : syncDtStrszInFile e = e)
    (hLay : layoutAlreadyValid e = true)
    (hDisj : e.spliceRegionsDisjoint)
    (i : Nat) (hi : i < e.sections.size)
    (hType_NB : (e.sections[i]'hi).type ≠ ShType.SHT_NOBITS)
    (hType_NL : (e.sections[i]'hi).type ≠ ShType.SHT_NULL)
    (bs : ByteArray)
    (hContent : (e.sections[i]'hi).content = .raw bs) :
    Reader.readBytes (encode e) (e.sections[i]'hi).offset.val
        (e.sections[i]'hi).encodedSize
      = bs := by
  have hEncSize : (e.sections[i]'hi).encodedSize = bs.size := by
    show (e.sections[i]'hi).encodedSize = bs.size
    unfold Section.encodedSize; rw [hContent]
  have hWriteContent : (e.sections[i]'hi).writeContent = bs := by
    unfold Section.writeContent; rw [hContent]
  rw [readBytes_encode_in_section e hSync hLay hDisj i hi hType_NB hType_NL]
  exact hWriteContent

/-! ## SHT_NULL discharge: the conventional sections[0] case.

    For SHT_NULL sections, the encoder's `sectionFoldStep` skips them
    entirely (NOBITS/NULL → no splice).  In well-formed inputs, NULL
    sections satisfy the type/content invariant via `.raw bs`, which
    forces `Section.encodedSize = bs.size`.  When `bs = ByteArray.empty`
    (the standard convention for the sentinel sections[0]), the
    decoder reads 0 bytes from any offset, producing
    `.raw ByteArray.empty` which matches the content.

    We DON'T need byte preservation for NULL sections — the equation
    is structurally trivial: both sides reduce to
    `.raw ByteArray.empty`. -/

private theorem decodeRaw_encode_null (e : ElfFile)
    (i : Nat) (hi : i < e.sections.size)
    (_hType_NL : (e.sections[i]'hi).type = ShType.SHT_NULL)
    (bs : ByteArray)
    (hContent : (e.sections[i]'hi).content = .raw bs)
    (hEmpty : bs.size = 0) :
    Reader.readBytes (encode e) (e.sections[i]'hi).offset.val
        (e.sections[i]'hi).encodedSize
      = bs := by
  have hEncSize : (e.sections[i]'hi).encodedSize = 0 := by
    unfold Section.encodedSize
    rw [hContent]
    exact hEmpty
  unfold Reader.readBytes
  rw [hEncSize]
  -- Goal: (encode e).extract s.offset (s.offset + 0) = bs.
  -- Both are empty.
  apply ByteArray.ext_getElem
  · rw [ByteArray.size_extract, hEmpty]; omega
  · intros j hj _
    rw [ByteArray.size_extract] at hj
    omega

/-! ## section_decode_encode dispatch

    Case-split on `s.type` for each section, dispatching to the
    matching per-content discharge.

    Preconditions:
      * Standard 4 (sync, layout, disjoint, IsValid).
      * `e.sectionsTypeContentMatch` — type↔content invariant.
      * `s.encodedSize < UInt64.size` for every section — required to
        bridge `(toShdr s).size.val = s.encodedSize` (UInt64
        round-trips through Nat losslessly only in this range).  Real
        ELFs satisfy this trivially (file sizes are far below 2^64).
      * `dynamicWellFormed` is included in `IsValid`, providing the
        DT_NULL termination + no-early-null invariant for the .dynamic
        case.

    For SHT_NULL sections (the conventional `sections[0]`), no decode
    is performed; the witness field's bound `i < e.sections.size`
    requires non-NULL handling for the .raw default branch.  We take
    `e.sectionsWellFormed` (in IsValid) which guarantees `sections[0]`
    is SHT_NULL but says nothing about other indices having SHT_NULL —
    this is enforced by the caller passing only non-NULL sections, OR
    we exclude `i = 0` from the theorem.  For simplicity, the theorem
    asserts the equation for ALL sections including the SHT_NULL
    section[0] (which has content=.nobits in well-formed ELFs but the
    decoder dispatches to .raw on SHT_NULL).  We add a precondition
    `e.sectionsAllNonNullExceptZero` to make this clean. -/

/-- Helper: `(toShdr s).size.val = s.encodedSize` definitionally.
    No fit precondition needed since `.val` is now `Nat`. -/
private theorem encodedSize_toUInt64_toNat (s : Section)
    (_h : s.encodedSize < UInt64.size) :
    s.encodedSize = s.encodedSize := rfl

/-- Bridge: when section i has `.dynamic ds` content and the section's
    type is `SHT_DYNAMIC` (from typeContentMatch + the case being .dynamic),
    `e.dynamic = some ds`.  Composes `findUniqueTypeIdx_eq_some` (using
    `sectionsAtDistinctTypes` for uniqueness) with the `e.dynamic`
    accessor's match. -/
private theorem dynamic_eq_some_of_section (e : ElfFile)
    (hUnique : e.typeUniqueAt ShType.SHT_DYNAMIC)
    (i : Nat) (hi : i < e.sections.size)
    (hType : (e.sections[i]'hi).type = ShType.SHT_DYNAMIC)
    (ds : Array DynEntry)
    (hContent : (e.sections[i]'hi).content = .dynamic ds) :
    e.dynamic = some ds := by
  have hContentAt : e.contentAt e.dynamicIdx = some (.dynamic ds) := by
    unfold ElfFile.contentAt ElfFile.dynamicIdx
    rw [ElfFile.findUniqueTypeIdx_eq_some e ShType.SHT_DYNAMIC i hi hType hUnique]
    show (if h : i < e.sections.size then some (e.sections[i]'h).content else none)
       = some (.dynamic ds)
    rw [dif_pos hi, hContent]
  show (match e.contentAt e.dynamicIdx with
        | some (.dynamic x) => some x
        | _                 => none) = some ds
  rw [hContentAt]

/-- Bridge `e.IsValid + sectionsTypeContentMatch + section[i] non-NULL`
    to the per-section `hDynWF` precondition.  When section i has
    `.dynamic ds` content, `IsValid.dynamic_wf` (specifically the
    `dynamicTerminated` clause) gives us:
      0 < ds.size ∧ DT_NULL bookend ∧ no early null. -/
theorem isValid_to_hDynWF (e : ElfFile) (hVal : e.IsValid)
    (hTCM : e.sectionsTypeContentMatch) :
    ∀ (i : Nat) (h : i < e.sections.size) (ds : Array DynEntry),
      (e.sections[i]'h).content = .dynamic ds →
      ∃ (hSizePos : 0 < ds.size),
        (ds[ds.size - 1]'(by omega)).tag = DynTag.null ∧
        (∀ (j : Nat) (hj : j < ds.size),
          (ds[j]'hj).tag = DynTag.null → j = ds.size - 1) := by
  intros i hi ds hContent
  -- Get type = SHT_DYNAMIC from the type/content invariant.
  have hTCMi : ElfFile.Section.typeContentMatchesB (e.sections[i]'hi) = true := by
    have hAll := hTCM
    unfold ElfFile.sectionsTypeContentMatch at hAll
    rw [Array.all_iff_forall] at hAll
    exact hAll i hi ⟨Nat.zero_le _, hi⟩
  have hType : (e.sections[i]'hi).type = ShType.SHT_DYNAMIC := by
    unfold ElfFile.Section.typeContentMatchesB at hTCMi
    -- Case-split on type via the matchesB unfolding.
    by_cases hT_NB : (e.sections[i]'hi).type = ShType.SHT_NOBITS
    · rw [if_pos hT_NB] at hTCMi
      rw [hContent] at hTCMi; simp at hTCMi
    rw [if_neg hT_NB] at hTCMi
    by_cases hT_ST : (e.sections[i]'hi).type = ShType.SHT_STRTAB
    · rw [if_pos hT_ST] at hTCMi
      rw [hContent] at hTCMi; simp at hTCMi
    rw [if_neg hT_ST] at hTCMi
    by_cases hT_DY : (e.sections[i]'hi).type = ShType.SHT_DYNAMIC
    · exact hT_DY
    rw [if_neg hT_DY] at hTCMi
    by_cases hT_DS : (e.sections[i]'hi).type = ShType.SHT_DYNSYM
    · rw [if_pos hT_DS] at hTCMi
      rw [hContent] at hTCMi; simp at hTCMi
    rw [if_neg hT_DS] at hTCMi
    by_cases hT_VS : (e.sections[i]'hi).type = ShType.SHT_GNU_VERSYM
    · rw [if_pos hT_VS] at hTCMi
      rw [hContent] at hTCMi; simp at hTCMi
    · rw [if_neg hT_VS] at hTCMi
      rw [hContent] at hTCMi; simp at hTCMi
  -- e.dynamic = some ds via the bridge.
  have hDyn : e.dynamic = some ds :=
    dynamic_eq_some_of_section e hVal.types_distinct.1 i hi hType ds hContent
  -- Pull the three properties from dynamicTerminated.
  have hTerm := hVal.dynamic_wf.1
  exact hTerm ds hDyn

set_option maxHeartbeats 1600000 in
/-- The unconditional `section_decode` theorem.  Case-splits on
    `s.type`, dispatches to the matching per-content discharge.

    Preconditions:
      * `syncDtStrszInFile e = e`, `layoutAlreadyValid e = true`,
        `e.spliceRegionsDisjoint`, `e.IsValid` — standard four.
      * `e.sectionsTypeContentMatch` — type↔content invariant.
      * `hSizeFit` — each section's encoded size fits in UInt64.
      * `hNonNull` — only sections[0] is SHT_NULL.
      * `hDynWF` — for any section with `.dynamic ds` content, ds is
        non-empty, terminates in DT_NULL, and has no earlier null.
        Caller can derive this from `e.IsValid.dynamic_wf` once the
        per-section ↔ e.dynamic bridge is in place; expressed
        per-section here to avoid the `findUniqueTypeIdx` chase. -/
theorem section_decode_encode (e : ElfFile)
    (hSync : syncDtStrszInFile e = e)
    (hLay : layoutAlreadyValid e = true)
    (hDisj : e.spliceRegionsDisjoint)
    (hVal : e.IsValid)
    (hTCM : e.sectionsTypeContentMatch)
    (hSizeFit : ∀ (i : Nat) (h : i < e.sections.size),
      (e.sections[i]'h).encodedSize < UInt64.size)
    (hNullEmpty : ∀ (i : Nat) (h : i < e.sections.size),
      (e.sections[i]'h).type = ShType.SHT_NULL →
      ∃ bs, (e.sections[i]'h).content = .raw bs ∧ bs.size = 0)
    (hDynWF : ∀ (i : Nat) (h : i < e.sections.size) (ds : Array DynEntry),
      (e.sections[i]'h).content = .dynamic ds →
      ∃ (hSizePos : 0 < ds.size),
        (ds[ds.size - 1]'(by omega)).tag = DynTag.null ∧
        (∀ (j : Nat) (hj : j < ds.size),
          (ds[j]'hj).tag = DynTag.null → j = ds.size - 1)) :
    ∀ (i : Nat) (h : i < e.sections.size),
      Patchelf.Elf.decodeSectionContent (encode e) (toShdr (e.sections[i]'h))
        = (e.sections[i]'h).content := by
  intros i hi
  -- Compute (toShdr s).type / .offset / .size.val.
  have hToShdrType : (toShdr (e.sections[i]'hi)).type = (e.sections[i]'hi).type := rfl
  have hToShdrOff : (toShdr (e.sections[i]'hi)).offset = (e.sections[i]'hi).offset := rfl
  have hToShdrSz : (toShdr (e.sections[i]'hi)).size.val
                   = (e.sections[i]'hi).encodedSize := rfl
  -- Type-content match for this i.
  have hTCMi : ElfFile.Section.typeContentMatchesB (e.sections[i]'hi) = true := by
    have hAll := hTCM
    unfold ElfFile.sectionsTypeContentMatch at hAll
    rw [Array.all_iff_forall] at hAll
    exact hAll i hi ⟨Nat.zero_le _, hi⟩
  -- decodeSectionContent's dispatch.
  unfold Patchelf.Elf.decodeSectionContent
  rw [hToShdrType, hToShdrOff, hToShdrSz]
  -- Case-split on s.type.
  by_cases hT_NB : (e.sections[i]'hi).type = ShType.SHT_NOBITS
  · rw [if_pos hT_NB]
    unfold ElfFile.Section.typeContentMatchesB at hTCMi
    rw [if_pos hT_NB] at hTCMi
    match hC : (e.sections[i]'hi).content with
    | .nobits => rfl
    | .raw _      => simp [hC] at hTCMi
    | .strtab _   => simp [hC] at hTCMi
    | .dynamic _  => simp [hC] at hTCMi
    | .dynsym _   => simp [hC] at hTCMi
    | .versym _   => simp [hC] at hTCMi
  · rw [if_neg hT_NB]
    by_cases hT_ST : (e.sections[i]'hi).type = ShType.SHT_STRTAB
    · rw [if_pos hT_ST]
      have hT_NL : (e.sections[i]'hi).type ≠ ShType.SHT_NULL := by
        rw [hT_ST]; decide
      unfold ElfFile.Section.typeContentMatchesB at hTCMi
      rw [if_neg hT_NB, if_pos hT_ST] at hTCMi
      match hC : (e.sections[i]'hi).content with
      | .strtab st =>
        rw [decodeStringTable_encode_strtab e hSync hLay hDisj i hi hT_NB hT_NL st hC]
      | .nobits     => simp [hC] at hTCMi
      | .raw _      => simp [hC] at hTCMi
      | .dynamic _  => simp [hC] at hTCMi
      | .dynsym _   => simp [hC] at hTCMi
      | .versym _   => simp [hC] at hTCMi
    · rw [if_neg hT_ST]
      by_cases hT_DY : (e.sections[i]'hi).type = ShType.SHT_DYNAMIC
      · rw [if_pos hT_DY]
        have hT_NL : (e.sections[i]'hi).type ≠ ShType.SHT_NULL := by
          rw [hT_DY]; decide
        unfold ElfFile.Section.typeContentMatchesB at hTCMi
        rw [if_neg hT_NB, if_neg hT_ST, if_pos hT_DY] at hTCMi
        match hC : (e.sections[i]'hi).content with
        | .dynamic ds =>
          obtain ⟨hDS_size, hDS_lastNull, hDS_noEarly⟩ := hDynWF i hi ds hC
          rw [decodeDynamic_encode_dynamic e hSync hLay hDisj i hi hT_NB hT_NL
                ds hC hDS_size hDS_lastNull hDS_noEarly]
        | .nobits     => simp [hC] at hTCMi
        | .raw _      => simp [hC] at hTCMi
        | .strtab _   => simp [hC] at hTCMi
        | .dynsym _   => simp [hC] at hTCMi
        | .versym _   => simp [hC] at hTCMi
      · rw [if_neg hT_DY]
        by_cases hT_DS : (e.sections[i]'hi).type = ShType.SHT_DYNSYM
        · rw [if_pos hT_DS]
          have hT_NL : (e.sections[i]'hi).type ≠ ShType.SHT_NULL := by
            rw [hT_DS]; decide
          unfold ElfFile.Section.typeContentMatchesB at hTCMi
          rw [if_neg hT_NB, if_neg hT_ST, if_neg hT_DY, if_pos hT_DS] at hTCMi
          match hC : (e.sections[i]'hi).content with
          | .dynsym syms =>
            rw [decodeDynsym_encode_dynsym e hSync hLay hDisj i hi hT_NB hT_NL syms hC]
          | .nobits     => simp [hC] at hTCMi
          | .raw _      => simp [hC] at hTCMi
          | .strtab _   => simp [hC] at hTCMi
          | .dynamic _  => simp [hC] at hTCMi
          | .versym _   => simp [hC] at hTCMi
        · rw [if_neg hT_DS]
          by_cases hT_VS : (e.sections[i]'hi).type = ShType.SHT_GNU_VERSYM
          · rw [if_pos hT_VS]
            have hT_NL : (e.sections[i]'hi).type ≠ ShType.SHT_NULL := by
              rw [hT_VS]; decide
            unfold ElfFile.Section.typeContentMatchesB at hTCMi
            rw [if_neg hT_NB, if_neg hT_ST, if_neg hT_DY, if_neg hT_DS,
                if_pos hT_VS] at hTCMi
            match hC : (e.sections[i]'hi).content with
            | .versym vs =>
              rw [decodeVersym_encode_versym e hSync hLay hDisj i hi hT_NB hT_NL vs hC]
            | .nobits     => simp [hC] at hTCMi
            | .raw _      => simp [hC] at hTCMi
            | .strtab _   => simp [hC] at hTCMi
            | .dynamic _  => simp [hC] at hTCMi
            | .dynsym _   => simp [hC] at hTCMi
          · rw [if_neg hT_VS]
            -- Default branch: handles both SHT_NULL and other "anything else" types.
            unfold ElfFile.Section.typeContentMatchesB at hTCMi
            rw [if_neg hT_NB, if_neg hT_ST, if_neg hT_DY, if_neg hT_DS,
                if_neg hT_VS] at hTCMi
            match hC : (e.sections[i]'hi).content with
            | .raw bs =>
              by_cases hT_NL_default : (e.sections[i]'hi).type = ShType.SHT_NULL
              · -- SHT_NULL: use the empty-bs discharge.
                obtain ⟨bs', hContent', hEmpty'⟩ := hNullEmpty i hi hT_NL_default
                -- hContent' : content = .raw bs'; hC : content = .raw bs.  So bs = bs'.
                have hBsEq : bs = bs' := by
                  rw [hC] at hContent'
                  injection hContent'
                subst hBsEq
                rw [decodeRaw_encode_null e i hi hT_NL_default bs hC hEmpty']
              · rw [decodeRaw_encode_raw e hSync hLay hDisj i hi hT_NB hT_NL_default bs hC]
            | .nobits     => simp [hC] at hTCMi
            | .strtab _   => simp [hC] at hTCMi
            | .dynamic _  => simp [hC] at hTCMi
            | .dynsym _   => simp [hC] at hTCMi
            | .versym _   => simp [hC] at hTCMi

/-! ## DecodeRoundtripWitness

    The master theorem requires that each decoder in `parse` recovers
    the value `encode` wrote at the matching offset.  This structure
    bundles those four facts.  Discharging it reduces to proving
    `decode ∘ write = id` for each ELF sub-structure — obligations
    tracked separately. -/

/-- Precondition bundle for `parse_encode_roundtrip`.

    Each field is a concrete statement of the shape
    "decoder on `encode e` at the encoder's offset = original value".
    The fields correspond one-to-one to the decoder calls inside
    `parse`'s do-block.

    **Note on layout interaction:** these fields reference the ORIGINAL
    `e.header.phoff`, `e.header.shoff`, and `e.sections[i].offset`.
    When `encode e` needs to run `layoutForEncoding` (i.e.,
    `layoutAlreadyValid e = false`), those offsets change and the
    bundle becomes undischargeable for `e`.  The theorem as stated
    therefore applies cleanly only to inputs that are already well-
    laid-out (parser output is one such class).  A more general
    statement would assert
    `parse (encode e) = .ok ⟨layoutForEncoding (syncDtStrszInFile e), _⟩`
    and is left for future work. -/
structure DecodeRoundtripWitness (e : ElfFile) : Prop where
  /-- The header parser succeeds on `encode e` and returns `e.header`. -/
  parseHeader_ok :
    Patchelf.Elf.Parse.parseHeader (encode e) = .ok e.header
  /-- `decodePhdrs` at `e.header.phoff` recovers `e.phdrs`. -/
  phdrs_decode :
    Patchelf.Elf.Decode.decodePhdrs (encode e)
      e.header.phoff.val e.header.phnum.toNat
      = e.phdrs
  /-- `decodeShdrs` at `e.header.shoff` recovers the shdr-projection
      of `e.sections`. -/
  shdrs_decode :
    Patchelf.Elf.Decode.decodeShdrs (encode e)
      e.header.shoff.val e.header.shnum.toNat
      = e.sections.map (fun s =>
          ({ name := s.name, type := s.type, flags := s.flags, addr := s.addr,
             offset := s.offset, size := ⟨s.encodedSize⟩,
             link := s.link, info := s.info, addralign := s.addralign,
             entsize := s.entsize }
            : SectionHeader))
  /-- For every section, decoding its content from `encode e` using the
      shdr-projection recovers the original content. -/
  section_decode :
    ∀ (i : Nat) (h : i < e.sections.size),
      decodeSectionContent (encode e)
        ({ name := (e.sections[i]'h).name,
           type := (e.sections[i]'h).type,
           flags := (e.sections[i]'h).flags,
           addr := (e.sections[i]'h).addr,
           offset := (e.sections[i]'h).offset,
           size := ⟨(e.sections[i]'h).encodedSize⟩,
           link := (e.sections[i]'h).link,
           info := (e.sections[i]'h).info,
           addralign := (e.sections[i]'h).addralign,
           entsize := (e.sections[i]'h).entsize }
          : SectionHeader)
      = (e.sections[i]'h).content

/-! ## EncodePreconditions: bundles the preconditions for the
    unconditional master theorem.  11 fields total; 9 conceptual
    clauses (the `headerFit_*` row expands into 3 separate fields
    covering the Nat-wrapper-to-`UInt64`-fit conditions). -/

/-- Preconditions for `parse_encode_roundtrip`.  Bundles the
    layout/synchronization/disjointness/identity facts needed for
    every decoder discharge to compose. -/
structure EncodePreconditions (e : ElfFile) : Prop where
  /-- DT_STRSZ is already in sync with `.dynstr.bytes.size`. -/
  syncOk : syncDtStrszInFile e = e
  /-- All 4 splice region kinds are pairwise disjoint.  Subsumes
      `layoutAlreadyValid e = true` via
      `layoutAlreadyValid_of_spliceRegionsDisjoint`. -/
  spliceDisjoint : e.spliceRegionsDisjoint
  /-- ELF magic + class + data ident bytes are present (per the spec). -/
  identValid : IdentBytesValid e
  /-- Each section's type matches its content constructor. -/
  typesMatch : e.sectionsTypeContentMatch
  /-- Each section's encodedSize fits in UInt64. -/
  sizeFit : ∀ (i : Nat) (h : i < e.sections.size),
    (e.sections[i]'h).encodedSize < UInt64.size
  /-- SHT_NULL sections (e.g. the conventional sections[0]) have
      `.raw ByteArray.empty` content. -/
  nullEmpty : ∀ (i : Nat) (h : i < e.sections.size),
    (e.sections[i]'h).type = ShType.SHT_NULL →
    ∃ bs, (e.sections[i]'h).content = .raw bs ∧ bs.size = 0
  /-- ElfHeader's wrap_nat fields fit in UInt64.  Trivially true for
      parser-derived headers (values came from `readU64`). -/
  headerFit_entry : e.header.entry.val < UInt64.size
  headerFit_phoff : e.header.phoff.val < UInt64.size
  headerFit_shoff : e.header.shoff.val < UInt64.size
  /-- ProgramHeader's wrap_nat fields fit in UInt64. -/
  phdrFit : ∀ (i : Nat) (h : i < e.phdrs.size),
    (e.phdrs[i]'h).offset.val < UInt64.size ∧
    (e.phdrs[i]'h).vaddr.val < UInt64.size ∧
    (e.phdrs[i]'h).paddr.val < UInt64.size ∧
    (e.phdrs[i]'h).filesz.val < UInt64.size ∧
    (e.phdrs[i]'h).memsz.val < UInt64.size ∧
    (e.phdrs[i]'h).align.val < UInt64.size
  /-- SectionHeader's wrap_nat fields fit in UInt64.  Note: `size` of
      a Section is derived (`encodedSize`); covered by `sizeFit`. -/
  shdrFit : ∀ (i : Nat) (h : i < e.sections.size),
    (e.sections[i]'h).addr.val < UInt64.size ∧
    (e.sections[i]'h).offset.val < UInt64.size ∧
    (e.sections[i]'h).addralign.val < UInt64.size ∧
    (e.sections[i]'h).entsize.val < UInt64.size

/-- `layoutOk` view of `EncodePreconditions` — `layoutAlreadyValid e =
    true` is derivable from `spliceDisjoint` via
    `layoutAlreadyValid_of_spliceRegionsDisjoint`. -/
theorem EncodePreconditions.layoutOk {e : ElfFile} (hPre : EncodePreconditions e) :
    layoutAlreadyValid e = true :=
  layoutAlreadyValid_of_spliceRegionsDisjoint e hPre.spliceDisjoint

/-- A `DecodeRoundtripWitness` is derivable from `EncodePreconditions`
    plus `IsValid`.  Each field follows from the matching
    unconditional theorem.  Useful as a stepping stone for callers who
    have older code structured around the bundle. -/
theorem decodeRoundtripWitness_of_preconditions (e : ElfFile)
    (hVal : e.IsValid) (hPre : EncodePreconditions e) :
    DecodeRoundtripWitness e where
  parseHeader_ok :=
    parseHeader_encode e hPre.syncOk hPre.layoutOk hPre.spliceDisjoint hVal hPre.identValid
      hPre.headerFit_entry hPre.headerFit_phoff hPre.headerFit_shoff
  phdrs_decode :=
    phdrs_decode_encode e hPre.syncOk hPre.layoutOk hPre.spliceDisjoint hVal
      hPre.phdrFit
  shdrs_decode :=
    shdrs_decode_encode e hPre.syncOk hPre.layoutOk hPre.spliceDisjoint hVal
      hPre.sizeFit hPre.shdrFit
  section_decode := by
    intros i h
    have hDynWF := isValid_to_hDynWF e hVal hPre.typesMatch
    exact section_decode_encode e hPre.syncOk hPre.layoutOk hPre.spliceDisjoint
      hVal hPre.typesMatch hPre.sizeFit hPre.nullEmpty hDynWF i h

/-! ## Master theorem (unconditional)

    The proof threads each decoder call in `parse` through the
    corresponding unconditional theorem, reassembles `e.elf`, and
    takes the `IsValid` branch using `e.isValid`. -/

/-- `sectionsFromShdrs` on the shdr-projection recovers `e.sections`,
    given the section_decode_encode discharge. -/
private theorem sectionsFromShdrs_eq (e : ElfFile)
    (hSync : syncDtStrszInFile e = e)
    (hLay : layoutAlreadyValid e = true)
    (hDisj : e.spliceRegionsDisjoint)
    (hVal : e.IsValid)
    (hTCM : e.sectionsTypeContentMatch)
    (hSizeFit : ∀ (i : Nat) (h : i < e.sections.size),
      (e.sections[i]'h).encodedSize < UInt64.size)
    (hNullEmpty : ∀ (i : Nat) (h : i < e.sections.size),
      (e.sections[i]'h).type = ShType.SHT_NULL →
      ∃ bs, (e.sections[i]'h).content = .raw bs ∧ bs.size = 0) :
    sectionsFromShdrs (encode e) (e.sections.map toShdr)
      = e.sections := by
  unfold sectionsFromShdrs
  rw [Array.map_map]
  apply Array.ext
  · simp
  · intro i hi _
    rw [Array.getElem_map]
    unfold sectionFromShdr
    simp only [Function.comp_apply]
    have hi' : i < e.sections.size := by
      rw [Array.size_map] at hi; exact hi
    have hDynWF := isValid_to_hDynWF e hVal hTCM
    have hDec := section_decode_encode e hSync hLay hDisj hVal hTCM
                   hSizeFit hNullEmpty hDynWF i hi'
    -- Goal has decodeSectionContent applied to a structure literal;
    -- hDec has it applied to `toShdr e.sections[i]`.  These are definitionally
    -- equal — the structure literal IS toShdr e.sections[i] inlined.
    show { name := (e.sections[i]'hi').name, type := (e.sections[i]'hi').type,
           flags := (e.sections[i]'hi').flags, addr := (e.sections[i]'hi').addr,
           offset := (e.sections[i]'hi').offset,
           link := (e.sections[i]'hi').link, info := (e.sections[i]'hi').info,
           addralign := (e.sections[i]'hi').addralign,
           entsize := (e.sections[i]'hi').entsize,
           content := decodeSectionContent (encode e) (toShdr (e.sections[i]'hi')) }
        = e.sections[i]'hi'
    rw [hDec]

/-- **Master theorem (unconditional)**: parsing the encoded bytes of a
    validated ELF file with appropriate preconditions recovers the
    original `ParsedElf`. -/
theorem parse_encode_roundtrip (e : ParsedElf) (hPre : EncodePreconditions e.elf) :
    parse (encode e.elf) = .ok e := by
  unfold parse
  rw [parseHeader_encode e.elf hPre.syncOk hPre.layoutOk hPre.spliceDisjoint
        e.isValid hPre.identValid
        hPre.headerFit_entry hPre.headerFit_phoff hPre.headerFit_shoff]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [phdrs_decode_encode e.elf hPre.syncOk hPre.layoutOk hPre.spliceDisjoint e.isValid
        hPre.phdrFit,
      shdrs_decode_encode e.elf hPre.syncOk hPre.layoutOk hPre.spliceDisjoint e.isValid
        hPre.sizeFit hPre.shdrFit]
  have hSecs := sectionsFromShdrs_eq e.elf hPre.syncOk hPre.layoutOk hPre.spliceDisjoint
                  e.isValid hPre.typesMatch hPre.sizeFit hPre.nullEmpty
  simp only [hSecs]
  have hElfEq :
      ({ header := e.elf.header, phdrs := e.elf.phdrs,
         sections := e.elf.sections } : ElfFile) = e.elf := by
    rfl
  rw [dif_pos (hElfEq ▸ e.isValid)]

/-- Bundle-form variant kept for callers structured around
    `DecodeRoundtripWitness`.  Derives from
    `decodeRoundtripWitness_of_preconditions` + `parse_encode_roundtrip`. -/
theorem parse_encode_roundtrip_witness (e : ParsedElf)
    (hDRW : DecodeRoundtripWitness e.elf) :
    parse (encode e.elf) = .ok e := by
  unfold parse
  rw [hDRW.parseHeader_ok]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [hDRW.phdrs_decode, hDRW.shdrs_decode]
  -- Inline `sectionsFromShdrs_from_witness`'s logic since we kept the
  -- existing bundle-form proof structure here.
  have hSecs : sectionsFromShdrs (encode e.elf)
      (e.elf.sections.map (fun s =>
        ({ name := s.name, type := s.type, flags := s.flags, addr := s.addr,
           offset := s.offset, size := ⟨s.encodedSize⟩,
           link := s.link, info := s.info, addralign := s.addralign,
           entsize := s.entsize }
          : SectionHeader)))
      = e.elf.sections := by
    unfold sectionsFromShdrs
    rw [Array.map_map]
    apply Array.ext
    · simp
    · intro i hi _
      rw [Array.getElem_map]
      unfold sectionFromShdr
      simp only [Function.comp_apply]
      have hi' : i < e.elf.sections.size := by
        rw [Array.size_map] at hi; exact hi
      rw [hDRW.section_decode i hi']
  simp only [hSecs]
  have hElfEq :
      ({ header := e.elf.header, phdrs := e.elf.phdrs,
         sections := e.elf.sections } : ElfFile) = e.elf := by
    rfl
  rw [dif_pos (hElfEq ▸ e.isValid)]

/-! ## Establishing `EncodePreconditions` from parser-output sections.

    Parser output (`sectionsFromShdrs`) constructs `Section.content`
    via `decodeSectionContent`'s type dispatch.  By construction:
      * SHT_NOBITS → `.nobits`
      * SHT_STRTAB → `.strtab _`
      * SHT_DYNAMIC → `.dynamic _`
      * SHT_DYNSYM → `.dynsym _`
      * SHT_GNU_VERSYM → `.versym _`
      * else → `.raw _`

    The first 5 lemmas here prove `Section.typeContentMatchesB` for
    each of the 6 cases; the per-section result composes into
    `sectionsTypeContentMatch` for any parser output. -/

theorem sectionFromShdr_typeContentMatches (bs : ByteArray) (sh : SectionHeader) :
    ElfFile.Section.typeContentMatchesB (sectionFromShdr bs sh) = true := by
  unfold sectionFromShdr ElfFile.Section.typeContentMatchesB decodeSectionContent
  by_cases hT_NB : sh.type = ShType.SHT_NOBITS
  · rw [if_pos hT_NB, if_pos hT_NB]
  · rw [if_neg hT_NB, if_neg hT_NB]
    by_cases hT_ST : sh.type = ShType.SHT_STRTAB
    · rw [if_pos hT_ST, if_pos hT_ST]
    · rw [if_neg hT_ST, if_neg hT_ST]
      by_cases hT_DY : sh.type = ShType.SHT_DYNAMIC
      · rw [if_pos hT_DY, if_pos hT_DY]
      · rw [if_neg hT_DY, if_neg hT_DY]
        by_cases hT_DS : sh.type = ShType.SHT_DYNSYM
        · rw [if_pos hT_DS, if_pos hT_DS]
        · rw [if_neg hT_DS, if_neg hT_DS]
          by_cases hT_VS : sh.type = ShType.SHT_GNU_VERSYM
          · rw [if_pos hT_VS, if_pos hT_VS]
          · rw [if_neg hT_VS, if_neg hT_VS]

/-- Parser output satisfies the `sectionsTypeContentMatch` invariant. -/
theorem sectionsFromShdrs_typeContentMatch (bs : ByteArray) (shdrs : Array SectionHeader) :
    (Array.all (sectionsFromShdrs bs shdrs) ElfFile.Section.typeContentMatchesB) = true := by
  rw [Array.all_iff_forall]
  intros i hi _
  unfold sectionsFromShdrs at hi ⊢
  rw [Array.size_map] at hi
  rw [Array.getElem_map]
  exact sectionFromShdr_typeContentMatches bs (shdrs[i]'hi)

/-! ## `IdentBytesValid` from raw byte facts

    `IdentBytesValid e` holds when `e.header.ident.head` has the
    standard magic / class / data byte values.  The decoder
    `decodeHeader bs 0 _` builds `header.ident.head = bs.extract 0 7`,
    so the `head[i]` values are pulled directly from `bs[i]`.

    `identBytesValid_of_decodeHeader` takes the byte values as
    preconditions; `parseHeader_to_ident_byte_facts` derives those
    facts from a successful `parseHeader bs = .ok h`. -/
theorem identBytesValid_of_decodeHeader (bs : ByteArray)
    (hSize : 0 + 64 ≤ bs.size)
    (hM0 : Reader.readU8 bs 0 = 0x7f)
    (hM1 : Reader.readU8 bs 1 = 0x45)
    (hM2 : Reader.readU8 bs 2 = 0x4c)
    (hM3 : Reader.readU8 bs 3 = 0x46)
    (hCls : Reader.readU8 bs 4 = Layout.ElfClass.elf64.encode)
    (hDat : Reader.readU8 bs 5 = Layout.ElfData.lsb.encode) :
    IdentBytesValid { header := Decode.decodeHeader bs 0 hSize,
                      phdrs := #[], sections := #[] } := by
  have hM0' : bs[0]'(by omega) = 0x7f       := (Reader.readU8_eq_getElem bs 0 (by omega)).symm.trans hM0
  have hM1' : bs[1]'(by omega) = 0x45       := (Reader.readU8_eq_getElem bs 1 (by omega)).symm.trans hM1
  have hM2' : bs[2]'(by omega) = 0x4c       := (Reader.readU8_eq_getElem bs 2 (by omega)).symm.trans hM2
  have hM3' : bs[3]'(by omega) = 0x46       := (Reader.readU8_eq_getElem bs 3 (by omega)).symm.trans hM3
  have hCls' : bs[4]'(by omega) = Layout.ElfClass.elf64.encode :=
    (Reader.readU8_eq_getElem bs 4 (by omega)).symm.trans hCls
  have hDat' : bs[5]'(by omega) = Layout.ElfData.lsb.encode :=
    (Reader.readU8_eq_getElem bs 5 (by omega)).symm.trans hDat
  refine {
    head_size := ?_
    byte0 := ?_, byte1 := ?_, byte2 := ?_, byte3 := ?_
    classByte := ?_, dataByte := ?_ }
  · show (Reader.readBytes bs (0 + 0) 7).size = 7
    unfold Reader.readBytes
    rw [ByteArray.size_extract]; omega
  all_goals {
    show ((Reader.readBytes bs (0 + 0) 7))[_]'_ = _
    unfold Reader.readBytes
    rw [ByteArray.getElem_extract]
    first
      | (show bs[0 + 0 + 0]'_ = _; exact hM0')
      | (show bs[0 + 0 + 1]'_ = _; exact hM1')
      | (show bs[0 + 0 + 2]'_ = _; exact hM2')
      | (show bs[0 + 0 + 3]'_ = _; exact hM3')
      | (show bs[0 + 0 + 4]'_ = _; exact hCls')
      | (show bs[0 + 0 + 5]'_ = _; exact hDat')
  }

/-- Bridge: a successful `parseHeader bs = .ok h` implies the 6
    magic / class / data bytes of `bs` match the ELF spec values.
    With the explicit if-chain refactor of `parseHeader`, each early-
    error branch contradicts hParse, leaving the success path. -/
theorem parseHeader_byte_facts (bs : ByteArray) (h : ElfHeader)
    (hParse : Patchelf.Elf.Parse.parseHeader bs = .ok h) :
    Layout.ehdrSize ≤ bs.size ∧
    Reader.readU8 bs 0 = 0x7f ∧
    Reader.readU8 bs 1 = 0x45 ∧
    Reader.readU8 bs 2 = 0x4c ∧
    Reader.readU8 bs 3 = 0x46 ∧
    Reader.readU8 bs 4 = Layout.ElfClass.elf64.encode ∧
    Reader.readU8 bs 5 = Layout.ElfData.lsb.encode ∧
    h = Decode.decodeHeader bs 0 (by
      have h1 : bs.size ≥ Layout.ehdrSize := by
        unfold Patchelf.Elf.Parse.parseHeader at hParse
        by_cases hSz : bs.size < Layout.ehdrSize
        · rw [dif_pos hSz] at hParse; cases hParse
        · exact Nat.le_of_not_lt hSz
      have : Layout.ehdrSize = 64 := rfl; omega) := by
  unfold Patchelf.Elf.Parse.parseHeader at hParse
  by_cases hSize : bs.size < Layout.ehdrSize
  · rw [dif_pos hSize] at hParse; cases hParse
  rw [dif_neg hSize] at hParse
  have hEhdrLe : Layout.ehdrSize ≤ bs.size := Nat.le_of_not_lt hSize
  have h16Bound : 0 + 16 ≤ bs.size := by
    have : Layout.ehdrSize = 64 := rfl; omega
  have h64Bound : 0 + 64 ≤ bs.size := by
    have : Layout.ehdrSize = 64 := rfl; omega
  by_cases hMagic : ¬ (Decode.decodeIdent bs 0 h16Bound).magicOk
  · rw [if_pos hMagic] at hParse; cases hParse
  rw [if_neg hMagic] at hParse
  have hMagic' := Classical.not_not.mp hMagic
  by_cases hClass : (Decode.decodeIdent bs 0 h16Bound).classByte
                    ≠ Layout.ElfClass.elf64.encode
  · rw [if_pos hClass] at hParse; cases hParse
  rw [if_neg hClass] at hParse
  have hClass' := Classical.not_not.mp hClass
  by_cases hData : (Decode.decodeIdent bs 0 h16Bound).dataByte
                   ≠ Layout.ElfData.lsb.encode
  · rw [if_pos hData] at hParse; cases hParse
  rw [if_neg hData] at hParse
  have hData' := Classical.not_not.mp hData
  by_cases hPhE : (Decode.decodeHeader bs 0 h64Bound).phentsize.toNat ≠ Layout.phdrSize
  · rw [if_pos hPhE] at hParse; cases hParse
  rw [if_neg hPhE] at hParse
  by_cases hShE : (Decode.decodeHeader bs 0 h64Bound).shentsize.toNat ≠ Layout.shdrSize
  · rw [if_pos hShE] at hParse; cases hParse
  rw [if_neg hShE] at hParse
  by_cases hPhO : (Decode.decodeHeader bs 0 h64Bound).phoff.val
                  + (Decode.decodeHeader bs 0 h64Bound).phnum.toNat
                  * (Decode.decodeHeader bs 0 h64Bound).phentsize.toNat > bs.size
  · rw [if_pos hPhO] at hParse; cases hParse
  rw [if_neg hPhO] at hParse
  by_cases hShO : (Decode.decodeHeader bs 0 h64Bound).shoff.val
                  + (Decode.decodeHeader bs 0 h64Bound).shnum.toNat
                  * (Decode.decodeHeader bs 0 h64Bound).shentsize.toNat > bs.size
  · rw [if_pos hShO] at hParse; cases hParse
  rw [if_neg hShO] at hParse
  by_cases hShN : (Decode.decodeHeader bs 0 h64Bound).shstrndx.toNat
                  ≥ (Decode.decodeHeader bs 0 h64Bound).shnum.toNat
  · rw [if_pos hShN] at hParse; cases hParse
  rw [if_neg hShN] at hParse
  have hHEq : h = Decode.decodeHeader bs 0 h64Bound := by
    injection hParse with hEq; exact hEq.symm
  simp only [Decode.decodeIdent] at hMagic' hClass' hData'
  obtain ⟨⟨⟨hM0, hM1⟩, hM2⟩, hM3⟩ := by
    simpa only [Bool.and_eq_true, beq_iff_eq] using hMagic'
  exact ⟨hEhdrLe, hM0, hM1, hM2, hM3, hClass', hData', hHEq⟩

/-! ## `syncOk` from `dynStrszCoherent`

    `syncDtStrszInFile e = e` (the `EncodePreconditions.syncOk` clause)
    holds when `e.dynStrszCoherent` (already in `IsFullyValid`).  The
    derivation:
    - `dynStrszCoherent`: every DT_STRSZ entry has `value.toNat = ds.bytes.size`.
    - Since `value : UInt64`, `value.toNat.toUInt64 = value` always; so
      `value = ds.bytes.size.toUInt64`.
    - Thus `syncDtStrsz dyn ds.bytes.size.toUInt64 = dyn` (no rewrites
      change anything).
    - `e.updateSectionContent iDyn (.dynamic dyn) = e` when
      `e.sections[iDyn].content = .dynamic dyn` — which holds because
      `e.dynamic = some dyn` is derived from the section's content. -/

/-- Helper: `v = v.toNat.toUInt64` for any UInt64 v. -/
private theorem uint64_toNat_toUInt64 (v : UInt64) : v.toNat.toUInt64 = v := by
  unfold Nat.toUInt64 UInt64.ofNat UInt64.toNat
  simp

/-- `updateSectionContent iDyn newContent = e` when `newContent` equals
    the existing content at iDyn. -/
private theorem updateSectionContent_eq_self (e : ElfFile) (iDyn : Nat)
    (h : iDyn < e.sections.size) (newContent : SectionContent)
    (heq : (e.sections[iDyn]'h).content = newContent) :
    e.updateSectionContent iDyn newContent = e := by
  unfold ElfFile.updateSectionContent
  rw [dif_pos h]
  rcases e with ⟨header, phdrs, sections⟩
  simp only at h heq ⊢
  congr 1
  apply Array.ext
  · simp
  · intros j hj _
    rw [Array.size_set] at hj
    by_cases hjEq : j = iDyn
    · subst hjEq
      rw [Array.getElem_set_self]
      rcases hS : sections[j]'h with ⟨name, type, flags, addr, offset, link, info, addralign, entsize, content⟩
      simp only [hS] at heq
      simp only [heq]
    · have hjNe : iDyn ≠ j := fun h => hjEq h.symm
      rw [Array.getElem_set_ne (h' := h) hj hjNe]

theorem syncDtStrszInFile_eq_id (e : ElfFile) (h : e.dynStrszCoherent) :
    syncDtStrszInFile e = e := by
  unfold syncDtStrszInFile
  -- Use rcases to handle the 3-way match at top.
  generalize hDs : e.dynstr = ods
  generalize hDyn : e.dynamic = odyn
  generalize hIdx : e.dynamicIdx = oIdx
  cases ods with
  | none => simp
  | some ds =>
    cases odyn with
    | none => simp
    | some dyn =>
      cases oIdx with
      | none => simp
      | some iDyn =>
        simp only []
        by_cases hLt : iDyn < e.sections.size
        · rw [dif_pos hLt]
          have hSyncId : Patchelf.Elf.syncDtStrsz dyn ds.bytes.size.toUInt64 = dyn := by
            apply syncDtStrsz_eq_id
            intros i hi hT
            have hCo := h dyn ds hDyn hDs i hi hT
            have hRT := uint64_toNat_toUInt64 (dyn[i]'hi).value
            rw [hCo] at hRT
            exact hRT.symm
          rw [hSyncId]
          -- Need e.sections[iDyn].content = .dynamic dyn.
          have hContent : (e.sections[iDyn]'hLt).content = .dynamic dyn := by
            have hOrig := hDyn
            unfold ElfFile.dynamic ElfFile.contentAt at hOrig
            rw [hIdx] at hOrig
            simp only [Option.bind_some] at hOrig
            rw [dif_pos hLt] at hOrig
            generalize hC : (e.sections[iDyn]'hLt).content = c at hOrig ⊢
            cases c with
            | dynamic dyn' =>
              simp at hOrig; rw [hOrig]
            | _ => simp at hOrig
          exact updateSectionContent_eq_self e iDyn hLt _ hContent
        · rw [dif_neg hLt]

/-! ## `layoutOk` + `spliceDisjoint` from parser output (gap)

    The remaining `spliceDisjoint` field of `EncodePreconditions`
    does NOT hold for arbitrary parser output (10 of 11 fields are
    parser-derivable via `encodePreconditions_of_parser`):

    * `layoutAlreadyValid e = true` requires file-resident sections to
      have pairwise-disjoint `[offset, offset + encodedSize)` ranges.
      The parser only checks `phoff/shoff + count*size ≤ bs.size`,
      not section-section disjointness.
    * `spliceRegionsDisjoint` is the structural counterpart with 7
      named fields covering pairwise disjointness across 4 region
      kinds (header / phdrs / shdrs / sections).

    Real ELF files satisfy both, but the parser doesn't prove it.
    Two paths to closing the gap:

    (a) Extend `Parser.parse` to validate disjointness as part of
        `IsValid` (returns `ParseError.layoutInvalid` on failure).
        This makes `layoutAlreadyValid e = true` follow from
        `IsValid e` directly.  Minimal parser refactor; ~80-120 LOC
        for the predicate + parse extension + bridge theorem.

    (b) Restate `parse_encode_roundtrip` to acknowledge the encoder's
        layout pass:
          `parse (encode pe.elf) = .ok ⟨layoutForEncoding (...), _⟩`
        This is more honest about what `encode` does but changes the
        theorem shape and complicates downstream reasoning.

    Path (a) is preferred — see ROADMAP item 1.3a.  Both deferred
    from this session. -/

/-- `IdentBytesValid` only depends on `e.header`, not on `phdrs` or
    `sections`.  Transport across ElfFile shapes that share the
    header. -/
theorem identBytesValid_of_header (e e' : ElfFile) (hHdr : e.header = e'.header)
    (h : IdentBytesValid e) : IdentBytesValid e' := by
  have hSize : e'.header.ident.head.size = 7 := by rw [← hHdr]; exact h.head_size
  refine {
    head_size := hSize
    byte0 := ?_, byte1 := ?_, byte2 := ?_, byte3 := ?_
    classByte := ?_, dataByte := ?_ }
  all_goals
    show e'.header.ident.head[_]'(by rw [hSize]; decide) = _
  all_goals
    have hHead : e'.header.ident.head = e.header.ident.head := by rw [hHdr]
    have h0 := h.byte0
    have h1 := h.byte1
    have h2 := h.byte2
    have h3 := h.byte3
    have hC := h.classByte
    have hD := h.dataByte
    simp only [hHead]
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact hC
  · exact hD

/-- Composes `parseHeader_byte_facts` with `identBytesValid_of_decodeHeader`
    to give the canonical bridge: a successful `parseHeader bs = .ok h`
    yields `IdentBytesValid` for any ElfFile whose header is `h`. -/
theorem identBytesValid_of_parseHeader_ok (bs : ByteArray) (e : ElfFile)
    (hParse : Patchelf.Elf.Parse.parseHeader bs = .ok e.header) :
    IdentBytesValid e := by
  obtain ⟨hSize, hM0, hM1, hM2, hM3, hCls, hDat, hHEq⟩ :=
    parseHeader_byte_facts bs e.header hParse
  have h64 : 0 + 64 ≤ bs.size := by
    have : Layout.ehdrSize = 64 := rfl; omega
  apply identBytesValid_of_header
    { header := Decode.decodeHeader bs 0 h64, phdrs := #[], sections := #[] } e (hHEq.symm)
  exact identBytesValid_of_decodeHeader bs h64 hM0 hM1 hM2 hM3 hCls hDat

/-! ## `sizeFit` for parser output

    `Section.encodedSize` for any parser-output section is bounded by
    `sh.size.val` unconditionally: each content kind is built
    from `readBytes`/`buildArray` whose output size is bounded by the
    requested length.  Caller separately establishes
    `sh.size.val < UInt64.size` from the input buffer's size
    bound. -/
theorem sectionFromShdr_encodedSize_le (bs : ByteArray) (sh : SectionHeader) :
    (sectionFromShdr bs sh).encodedSize ≤ sh.size.val := by
  unfold sectionFromShdr Section.encodedSize decodeSectionContent
  by_cases hT_NB : sh.type = ShType.SHT_NOBITS
  · simp [hT_NB]
  by_cases hT_ST : sh.type = ShType.SHT_STRTAB
  · simp [hT_ST]
    show (Decode.decodeStringTable bs sh.offset.val sh.size.val).bytes.size
         ≤ sh.size.val
    unfold Decode.decodeStringTable
    show (Reader.readBytes bs sh.offset.val sh.size.val).size ≤ sh.size.val
    unfold Reader.readBytes
    rw [ByteArray.size_extract]; omega
  by_cases hT_DY : sh.type = ShType.SHT_DYNAMIC
  · simp [hT_DY]
    show (Decode.decodeDynamic bs sh.offset.val
            (sh.size.val / Layout.dynEntrySize)).size * Layout.dynEntrySize
          ≤ sh.size.val
    have hSize := Decode.decodeDynamic_size_le bs sh.offset.val
                    (sh.size.val / Layout.dynEntrySize)
    have hMul := Nat.mul_le_mul_right Layout.dynEntrySize hSize
    have hDiv : (sh.size.val / Layout.dynEntrySize) * Layout.dynEntrySize
                ≤ sh.size.val := Nat.div_mul_le_self _ _
    omega
  by_cases hT_DS : sh.type = ShType.SHT_DYNSYM
  · simp [hT_DS]
    show (Decode.decodeDynsym bs sh.offset.val
            (sh.size.val / Layout.symEntrySize)).size * Layout.symEntrySize
          ≤ sh.size.val
    rw [Decode.decodeDynsym_size]
    have hDiv : (sh.size.val / Layout.symEntrySize) * Layout.symEntrySize
                ≤ sh.size.val := Nat.div_mul_le_self _ _
    exact hDiv
  by_cases hT_VS : sh.type = ShType.SHT_GNU_VERSYM
  · simp [hT_VS]
    show (Decode.decodeVersym bs sh.offset.val (sh.size.val / 2)).size * 2
          ≤ sh.size.val
    rw [Decode.decodeVersym_size]
    have hDiv : (sh.size.val / 2) * 2 ≤ sh.size.val :=
      Nat.div_mul_le_self _ _
    exact hDiv
  · -- default: .raw branch.
    simp [hT_NB, hT_ST, hT_DY, hT_DS, hT_VS]
    show (Reader.readBytes bs sh.offset.val sh.size.val).size ≤ sh.size.val
    unfold Reader.readBytes
    rw [ByteArray.size_extract]; omega

/-- For SHT_NULL parser-output sections with `sh.size = 0` (the spec
    convention), the content is `.raw <empty bytes>`. -/
theorem sectionFromShdr_null_empty (bs : ByteArray) (sh : SectionHeader)
    (hT : sh.type = ShType.SHT_NULL) (hSize : sh.size.val = 0) :
    ∃ rawBs, (sectionFromShdr bs sh).content = .raw rawBs ∧ rawBs.size = 0 := by
  have hContentEq : (sectionFromShdr bs sh).content
                  = .raw (Reader.readBytes bs sh.offset.val sh.size.val) := by
    unfold sectionFromShdr decodeSectionContent
    have hNB : sh.type ≠ ShType.SHT_NOBITS := by rw [hT]; decide
    have hST : sh.type ≠ ShType.SHT_STRTAB := by rw [hT]; decide
    have hDY : sh.type ≠ ShType.SHT_DYNAMIC := by rw [hT]; decide
    have hDS : sh.type ≠ ShType.SHT_DYNSYM := by rw [hT]; decide
    have hVS : sh.type ≠ ShType.SHT_GNU_VERSYM := by rw [hT]; decide
    simp only [if_neg hNB, if_neg hST, if_neg hDY, if_neg hDS, if_neg hVS]
  refine ⟨_, hContentEq, ?_⟩
  unfold Reader.readBytes
  rw [hSize]
  rw [show sh.offset.val + 0 = sh.offset.val from by omega]
  rw [ByteArray.size_extract]
  omega

/-! ## Consolidated bridge: parser output → EncodePreconditions

    Builds the full `EncodePreconditions e` from the per-clause
    bridges proven above, plus the 2 unproven clauses (`layoutOk`,
    `spliceDisjoint`) supplied by the caller.

    The 5 derivable clauses come from:
    - `identValid` ← `identBytesValid_of_parseHeader_ok` (parseHeader bs = .ok e.header).
    - `typesMatch` ← `e.sections = sectionsFromShdrs bs ...` + `sectionsFromShdrs_typeContentMatch`.
    - `nullEmpty` ← `e.sections = sectionsFromShdrs bs ...` + `sectionFromShdr_null_empty`
      (one per SHT_NULL section, with `sh.size = 0` precondition).
    - `sizeFit` ← `e.sections = sectionsFromShdrs bs ...` + `sectionFromShdr_encodedSize_le`
      (with `sh.size < UInt64.size` precondition).
    - `syncOk` ← `syncDtStrszInFile_eq_id` (with `dynStrszCoherent`).

    Caller supplies:
    - `hParseHeader` — parseHeader on bs returned the same header.
    - `hSections` — e.sections came from sectionsFromShdrs on the
      same bs (with some shdrs array — its identity doesn't matter
      for typesMatch/nullEmpty/sizeFit, just that .map sectionFromShdr
      was applied).
    - `hShdrSizes` — for each `i < e.sections.size`, the shdr that
      produced section i had `sh.size.val < UInt64.size`.
    - `hShdrNullSize` — same but for SHT_NULL: `sh.size.val = 0`.
    - `hCoherent` — `e.dynStrszCoherent`.
    - `hSpliceDisjoint` — `e.spliceRegionsDisjoint`.  This is the one
      structural disjointness predicate the caller must establish;
      `layoutOk` is derived from it via
      `layoutAlreadyValid_of_spliceRegionsDisjoint`. -/
theorem encodePreconditions_of_parser
    (bs : ByteArray) (shdrs : Array SectionHeader) (e : ElfFile)
    (hParseHeader : Patchelf.Elf.Parse.parseHeader bs = .ok e.header)
    (hSections : e.sections = sectionsFromShdrs bs shdrs)
    (hShdrSizes : ∀ (i : Nat) (h : i < shdrs.size),
      (shdrs[i]'h).size.val < UInt64.size)
    (hShdrNullSize : ∀ (i : Nat) (h : i < shdrs.size),
      (shdrs[i]'h).type = ShType.SHT_NULL → (shdrs[i]'h).size.val = 0)
    (hPhdrs : e.phdrs = Decode.decodePhdrs bs e.header.phoff.val e.header.phnum.toNat)
    (hShdrsSrc : shdrs = Decode.decodeShdrs bs e.header.shoff.val e.header.shnum.toNat)
    (hCoherent : e.dynStrszCoherent)
    (hSpliceDisjoint : e.spliceRegionsDisjoint) :
    EncodePreconditions e where
  syncOk := syncDtStrszInFile_eq_id e hCoherent
  spliceDisjoint := hSpliceDisjoint
  identValid := identBytesValid_of_parseHeader_ok bs e hParseHeader
  typesMatch := by
    unfold ElfFile.sectionsTypeContentMatch
    rw [hSections]
    exact sectionsFromShdrs_typeContentMatch bs shdrs
  -- Header fit: header came from `decodeHeader`; every wrap_nat field is
  -- `⟨(readU64 ...).toNat⟩`, and `(u : UInt64).toNat < UInt64.size`.
  headerFit_entry := by
    have ⟨_, _, _, _, _, _, _, hHeq⟩ := parseHeader_byte_facts bs e.header hParseHeader
    rw [hHeq]; show (Reader.readU64 bs (0 + 24)).toNat < _; exact (Reader.readU64 bs _).toNat_lt
  headerFit_phoff := by
    have ⟨_, _, _, _, _, _, _, hHeq⟩ := parseHeader_byte_facts bs e.header hParseHeader
    rw [hHeq]; show (Reader.readU64 bs (0 + 32)).toNat < _; exact (Reader.readU64 bs _).toNat_lt
  headerFit_shoff := by
    have ⟨_, _, _, _, _, _, _, hHeq⟩ := parseHeader_byte_facts bs e.header hParseHeader
    rw [hHeq]; show (Reader.readU64 bs (0 + 40)).toNat < _; exact (Reader.readU64 bs _).toNat_lt
  -- Phdr fit: phdrs came from `decodePhdrs`; per-element each field is
  -- `⟨(readU64 ...).toNat⟩` (for wrap_nat) so trivially fits.
  phdrFit := by
    intros i hi
    -- Substitute via hPhdrs to read e.phdrs[i] as decodePhdrs[i].
    have hi' : i < (Decode.decodePhdrs bs e.header.phoff.val e.header.phnum.toNat).size := by
      rw [← hPhdrs]; exact hi
    have hPi : e.phdrs[i]'hi
              = (Decode.decodePhdrs bs e.header.phoff.val e.header.phnum.toNat)[i]'hi' := by
      congr 1
    rw [hPi, Decode.decodePhdrs_getElem]
    refine ⟨(Reader.readU64 bs _).toNat_lt, (Reader.readU64 bs _).toNat_lt,
            (Reader.readU64 bs _).toNat_lt, (Reader.readU64 bs _).toNat_lt,
            (Reader.readU64 bs _).toNat_lt, (Reader.readU64 bs _).toNat_lt⟩
  -- Shdr fit: each section came from a shdr, which came from `decodeShdr bs k`;
  -- per-element addr/offset/addralign/entsize are `⟨(readU64 ...).toNat⟩` and
  -- trivially fit.
  shdrFit := by
    intros i hi
    have hShSize : e.sections.size = shdrs.size := by
      rw [hSections]; unfold sectionsFromShdrs; rw [Array.size_map]
    have hShdrI : i < shdrs.size := hShSize ▸ hi
    have hSecEq : (e.sections[i]'hi) = sectionFromShdr bs (shdrs[i]'hShdrI) := by
      have h' : i < (sectionsFromShdrs bs shdrs).size := by
        unfold sectionsFromShdrs; rw [Array.size_map]; exact hShdrI
      have : (sectionsFromShdrs bs shdrs)[i]'h' = sectionFromShdr bs (shdrs[i]'hShdrI) := by
        unfold sectionsFromShdrs; rw [Array.getElem_map]
      rw [show (e.sections[i]'hi) = (sectionsFromShdrs bs shdrs)[i]'h' from by congr 1]
      exact this
    rw [hSecEq]
    -- `sectionFromShdr` inherits the shdr's addr/offset/addralign/entsize.
    -- Substitute the shdr via hShdrsSrc to read it as decodeShdrs[i].
    have hShdrI' : i < (Decode.decodeShdrs bs e.header.shoff.val
                          e.header.shnum.toNat).size := by
      rw [← hShdrsSrc]; exact hShdrI
    have hShEq : shdrs[i]'hShdrI
                = (Decode.decodeShdrs bs e.header.shoff.val
                      e.header.shnum.toNat)[i]'hShdrI' := by
      congr 1
    -- `sectionFromShdr bs sh`'s addr/offset/addralign/entsize all come
    -- from `sh.<field>`.  After hShEq, sh = decodeShdr bs k.
    show (sectionFromShdr bs (shdrs[i]'hShdrI)).addr.val < _ ∧
         (sectionFromShdr bs (shdrs[i]'hShdrI)).offset.val < _ ∧
         (sectionFromShdr bs (shdrs[i]'hShdrI)).addralign.val < _ ∧
         (sectionFromShdr bs (shdrs[i]'hShdrI)).entsize.val < _
    unfold sectionFromShdr
    show (shdrs[i]'hShdrI).addr.val < _ ∧ (shdrs[i]'hShdrI).offset.val < _ ∧
         (shdrs[i]'hShdrI).addralign.val < _ ∧ (shdrs[i]'hShdrI).entsize.val < _
    rw [hShEq, Decode.decodeShdrs_getElem]
    refine ⟨(Reader.readU64 bs _).toNat_lt, (Reader.readU64 bs _).toNat_lt,
            (Reader.readU64 bs _).toNat_lt, (Reader.readU64 bs _).toNat_lt⟩
  sizeFit := by
    intros i h
    have hShSize : e.sections.size = shdrs.size := by
      rw [hSections]; unfold sectionsFromShdrs; rw [Array.size_map]
    have hShdrI : i < shdrs.size := hShSize ▸ h
    have hSecEq : (e.sections[i]'h) = sectionFromShdr bs (shdrs[i]'hShdrI) := by
      have h' : i < (sectionsFromShdrs bs shdrs).size := by
        unfold sectionsFromShdrs; rw [Array.size_map]; exact hShdrI
      have : (sectionsFromShdrs bs shdrs)[i]'h' = sectionFromShdr bs (shdrs[i]'hShdrI) := by
        unfold sectionsFromShdrs; rw [Array.getElem_map]
      rw [show (e.sections[i]'h) = (sectionsFromShdrs bs shdrs)[i]'h' from by
        congr 1]
      exact this
    rw [hSecEq]
    have := sectionFromShdr_encodedSize_le bs (shdrs[i]'hShdrI)
    have hShFit := hShdrSizes i hShdrI
    omega
  nullEmpty := by
    intros i h hT
    have hShSize : e.sections.size = shdrs.size := by
      rw [hSections]; unfold sectionsFromShdrs; rw [Array.size_map]
    have hShdrI : i < shdrs.size := hShSize ▸ h
    have hSecEq : (e.sections[i]'h) = sectionFromShdr bs (shdrs[i]'hShdrI) := by
      have h' : i < (sectionsFromShdrs bs shdrs).size := by
        unfold sectionsFromShdrs; rw [Array.size_map]; exact hShdrI
      have : (sectionsFromShdrs bs shdrs)[i]'h' = sectionFromShdr bs (shdrs[i]'hShdrI) := by
        unfold sectionsFromShdrs; rw [Array.getElem_map]
      rw [show (e.sections[i]'h) = (sectionsFromShdrs bs shdrs)[i]'h' from by
        congr 1]
      exact this
    rw [hSecEq] at hT ⊢
    have hType : (shdrs[i]'hShdrI).type = ShType.SHT_NULL := hT
    exact sectionFromShdr_null_empty bs (shdrs[i]'hShdrI) hType (hShdrNullSize i hShdrI hType)

end Patchelf.Elf
