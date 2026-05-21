/-
  DSL-generated schemas for the 7 fixed-layout ELF structs:
  `DynEntry`, `ElfIdent`, `Vernaux`, `Symbol`, `ProgramHeader`,
  `SectionHeader`, `ElfHeader`.  Each `elf_schema` declaration
  emits the write / decode / size-lemma / byte-roundtrip /
  `ByteWidth` artifacts for one struct.

  Also hosted here (alongside the DSL invocations) are the
  variable-length / chained serializers and decoders whose on-disk
  length depends on runtime data:

  * `decodeVernauxChain` — walks the linked-list of Vernaux via
    `.vna_next`, terminates at 0.
  * `decodeVerneed` — pairs Verneed header + chained Vernauxes.
  * `decodeVerneedChain` — walks the Verneed chain via `.vn_next`.
  * `decodeDynamic` / `decodeDynamicLoop` — decodes `.dynamic`
    entries until DT_NULL is observed.
  * `Verneed.writeHeader` / `Verneed.write` — uses
    `writeArray Vernaux.write`.
  * `SysVHashTable.write` / `GnuHashTable.write` — 4/16-byte
    headers + `writeArray`-wrapped buckets / chains / bloom.
  * `SysVHashTable_write_decode_extract` /
    `GnuHashTable_write_decode_extract` — the variable-length
    byte-roundtrip theorems.
-/

import Patchelf.Elf.Basic
import Patchelf.Elf.Layout
import Patchelf.Elf.Writer
import Patchelf.Elf.Reader
import Patchelf.Elf.Serialize
import Patchelf.Elf.Decode
import Patchelf.Elf.ByteLevel
import Patchelf.Elf.SchemaDSL

namespace Patchelf.Elf

open Layout
open Decode
open Patchelf.Elf.SchemaDSL

/-! ## DynEntry (16 bytes, tag codec + primitive value)

    The `tag` field has a UInt64 on-disk representation but its Lean-
    level type is the `DynTag` inductive; the `codec` field kind
    bridges the two via the `DynTag.encodeU64` / `DynTag.decodeU64`
    pair and the `DynTag.encodeU64_decodeU64` identity. -/

elf_schema DynEntry := 16
  decode_as decodeDynEntry
  roundtrip_as DynEntry_write_decodeDynEntry_extract
  bytewidth_as dynEntry
  tag   : DynTag via u64 @ 0 codec DynTag.encodeU64 DynTag.decodeU64 DynTag.encodeU64_decodeU64 DynTag.decodeU64_encodeU64
  value : u64 @ 8

/-- Array-write size: `writeArray DynEntry.write dyn` totals
    `dyn.size * 16` bytes. Wraps `writeArray_size_of_uniform` with the
    DSL-generated `DynEntry.write_size`. -/
theorem writeArray_DynEntry_size (dyn : Array DynEntry) :
    (writeArray DynEntry.write dyn).size = dyn.size * Layout.dynEntrySize :=
  writeArray_size_of_uniform DynEntry.write _ DynEntry.write_size dyn

-- `DynEntry_decode_write` is DSL-emitted from the `elf_schema`
-- declaration above (forward direction added once the `tag` codec's
-- forward identity `DynTag.decodeU64_encodeU64` was proved).

/-! ## ElfIdent (16 bytes: 7 raw + 1 codec + 8 raw)

    The DSL's v2 `raw_bytes N with_size_field sf` supplies both the
    `ByteArray` field and its dependent size-proof field (e.g.
    `head_size : head.size = 7`), and the codec rule handles the
    1-byte `osAbi` encoding via `OsAbi.encode` / `OsAbi.ofByte`.

    The decoder signature picks up a precondition arg
    `(h : off + 16 ≤ bs.size)` because `Reader.readBytes_size` is
    only total in-bounds. `skip_bytewidth` suppresses the `ByteWidth`
    instance (incompatible with a preconditioned decoder);
    `ByteWidth ElfIdent` is not needed anyway — ElfIdent never
    appears in an `Array` that's the `writeArray`'d. -/

elf_schema ElfIdent := 16
  decode_as decodeElfIdent
  roundtrip_as ElfIdent_write_decodeElfIdent_extract
  skip_bytewidth
  head  : raw_bytes 7 @ 0  with_size_field head_size
  osAbi : OsAbi via u8 @ 7 codec OsAbi.encode OsAbi.ofByte OsAbi.encode_ofByte OsAbi.ofByte_encode
  tail  : raw_bytes 8 @ 8  with_size_field tail_size

/-- Forward byte-roundtrip for `ElfIdent`.  Three fields:
      `head` (raw_bytes 7), `osAbi` (codec u8), `tail` (raw_bytes 8).
    The `head`/`tail` fields use `extract_append` decomposition + the
    `extract_empty_of_size_le` helper to discard out-of-window slices.
    The `osAbi` field uses the standard left/right peel through the
    surrounding ByteArray, then the now-provable `OsAbi.ofByte_encode`
    (which the canonicalization unblocked). -/
theorem ElfIdent_decode_write (id : ElfIdent) (h : 0 + 16 ≤ (ElfIdent.write id).size) :
    Decode.decodeElfIdent (ElfIdent.write id) 0 h = id := by
  unfold Decode.decodeElfIdent ElfIdent.write
  congr 1
  · -- head
    show (id.head ++ Writer.writeU8 id.osAbi.encode ++ id.tail).extract
            (0 + 0) (0 + 0 + 7) = id.head
    simp only [Nat.zero_add, ByteArray.extract_append, id.head_size,
               ByteArray.size_append, writeU8_size]
    rw [ByteArray.extract_same, ByteArray.extract_same,
        ByteArray.append_empty, ByteArray.append_empty,
        show (7 : Nat) = id.head.size from id.head_size.symm]
    exact ByteArray.extract_zero_size
  · -- osAbi
    show OsAbi.ofByte (Reader.readU8 (id.head ++ Writer.writeU8 id.osAbi.encode ++ id.tail) (0 + 7)) = id.osAbi
    simp only [Nat.zero_add]
    rw [readU8_append_left _ _ 7 (by simp [ByteArray.size_append, id.head_size]),
        show (7 : Nat) = id.head.size + 0 from by simp [id.head_size],
        readU8_append_right _ _ 0 (by simp),
        readU8_writeU8]
    exact OsAbi.ofByte_encode id.osAbi
  · -- tail
    show (id.head ++ Writer.writeU8 id.osAbi.encode ++ id.tail).extract (0 + 8) (0 + 8 + 8) = id.tail
    simp only [Nat.zero_add, ByteArray.extract_append, id.head_size,
               ByteArray.size_append, writeU8_size]
    rw [show (8 - 7 : Nat) = 1 from by omega,
        show (8 + 8 - 7 : Nat) = 9 from by omega,
        show (8 - (7 + 1) : Nat) = 0 from by omega,
        show (8 + 8 - (7 + 1) : Nat) = 8 from by omega]
    rw [ByteArray.extract_empty_of_size_le id.head 8 16 (by rw [id.head_size]; omega),
        ByteArray.extract_empty_of_size_le (Writer.writeU8 id.osAbi.encode) 1 9 (by simp)]
    rw [ByteArray.empty_append, ByteArray.empty_append,
        show (8 : Nat) = id.tail.size from id.tail_size.symm,
        ByteArray.extract_zero_size]

/-- Composition: `decodeElfIdent` on `(a ++ b)` reads only from `a`'s
    first 16 bytes, so it equals `decodeElfIdent a 0 _`.

    Used by ElfHeader's forward roundtrip: the writer prepends
    `e.ident.write` (16 bytes) before all other fields, so reading
    the embedded ident at offset 0 of the deeply-nested append peels
    through to the original ident bytes. -/
theorem decodeElfIdent_append_left (a b : ByteArray) (h : 16 ≤ a.size)
    (h' : 0 + 16 ≤ (a ++ b).size) (h'' : 0 + 16 ≤ a.size) :
    Decode.decodeElfIdent (a ++ b) 0 h' = Decode.decodeElfIdent a 0 h'' := by
  unfold Decode.decodeElfIdent
  congr 1
  · show (a ++ b).extract (0+0) (0+0+7) = a.extract (0+0) (0+0+7)
    simp only [Nat.zero_add, ByteArray.extract_append]
    rw [show (0 - a.size : Nat) = 0 from by omega,
        show (7 - a.size : Nat) = 0 from by omega,
        ByteArray.extract_same, ByteArray.append_empty]
  · show OsAbi.ofByte (Reader.readU8 (a ++ b) (0+7))
        = OsAbi.ofByte (Reader.readU8 a (0+7))
    simp only [Nat.zero_add]
    rw [readU8_append_left _ _ 7 (by omega)]
  · show (a ++ b).extract (0+8) (0+8+8) = a.extract (0+8) (0+8+8)
    simp only [Nat.zero_add, ByteArray.extract_append]
    rw [show (8 - a.size : Nat) = 0 from by omega,
        show (8+8 - a.size : Nat) = 0 from by omega,
        ByteArray.extract_same, ByteArray.append_empty]

/-! ### Parser-side `decodeIdent` wrapper

    The DSL-generated `decodeElfIdent` returns a bare `ElfIdent`. The
    parser needs to *validate* the ident (check the ELF magic bytes,
    the ELF-class byte indicating 64-bit, the data byte indicating
    little-endian) and wants access to the diagnostic bytes so it can
    produce a specific `ParseError` rather than a generic reject. We
    factor this into `DecodedIdent` — the parsed `ElfIdent` plus three
    validation facts — and `Decode.decodeIdent` — a thin wrapper
    around `decodeElfIdent` that additionally reads the diagnostic
    bytes. -/

structure DecodedIdent where
  ident     : ElfIdent
  classByte : UInt8      -- EI_CLASS byte, for error reporting
  dataByte  : UInt8      -- EI_DATA byte, for error reporting
  magicOk   : Bool       -- EI_MAG0..3 match 0x7f 'E' 'L' 'F'
  deriving Repr

namespace Decode

def decodeIdent (bs : ByteArray) (off : Nat) (h : off + 16 ≤ bs.size) :
    DecodedIdent :=
  let m0 := Reader.readU8 bs (off + 0)
  let m1 := Reader.readU8 bs (off + 1)
  let m2 := Reader.readU8 bs (off + 2)
  let m3 := Reader.readU8 bs (off + 3)
  let magicOk := m0 == 0x7f && m1 == 0x45 && m2 == 0x4c && m3 == 0x46
  {
    ident     := decodeElfIdent bs off h
    classByte := Reader.readU8 bs (off + Layout.EI_CLASS)
    dataByte  := Reader.readU8 bs (off + Layout.EI_DATA)
    magicOk   := magicOk
  }

end Decode

/-! ## Vernaux (16 bytes, all primitive) -/

elf_schema Vernaux := 16
  bytewidth_as vernaux
  vna_hash  : u32 @ 0
  vna_flags : u16 @ 4
  vna_other : u16 @ 6
  vna_name  : u32 @ 8
  vna_next  : u32 @ 12

-- `Vernaux_decode_write` is DSL-emitted from the `elf_schema`
-- declaration above.

/-! ## Symbol (24 bytes, all primitive, mixed widths) -/

elf_schema Symbol := 24
  decode_as decodeSym
  roundtrip_as Symbol_write_decodeSymbol_extract
  bytewidth_as symbol
  with_array_decoder decodeDynsym
  st_name  : u32 @ 0
  st_info  : u8  @ 4
  st_other : u8  @ 5
  st_shndx : u16 @ 6
  st_value : u64 @ 8
  st_size  : u64 @ 16

-- `Symbol_decode_write` is DSL-emitted from the `elf_schema`
-- declaration above.

/-! ## ProgramHeader (56 bytes, all wrapped) -/

elf_schema ProgramHeader := 56
  decode_as decodePhdr
  roundtrip_as ProgramHeader_write_decodePhdr_extract
  bytewidth_as phdr
  with_array_decoder decodePhdrs
  type   : u32 @ 0  wrap PhType raw
  flags  : u32 @ 4
  offset : u64 @ 8  wrap_nat FileOffset val
  vaddr  : u64 @ 16 wrap_nat VirtualAddr val
  paddr  : u64 @ 24 wrap_nat PhysicalAddr val
  filesz : u64 @ 32 wrap_nat ByteSize val
  memsz  : u64 @ 40 wrap_nat ByteSize val
  align  : u64 @ 48 wrap_nat Alignment val

-- `ProgramHeader_decode_write` is DSL-emitted from the `elf_schema`
-- declaration above.

/-! ## SectionHeader (64 bytes, mixed wrapped/unwrapped) -/

elf_schema SectionHeader := 64
  decode_as decodeShdr
  roundtrip_as SectionHeader_write_decodeShdr_extract
  bytewidth_as shdr
  with_array_decoder decodeShdrs
  name      : u32 @ 0
  type      : u32 @ 4  wrap ShType raw
  flags     : u64 @ 8
  addr      : u64 @ 16 wrap_nat VirtualAddr val
  offset    : u64 @ 24 wrap_nat FileOffset val
  size      : u64 @ 32 wrap_nat ByteSize val
  link      : u32 @ 40
  info      : u32 @ 44
  addralign : u64 @ 48 wrap_nat Alignment val
  entsize   : u64 @ 56 wrap_nat ByteSize val

-- `SectionHeader_decode_write` is DSL-emitted from the `elf_schema`
-- declaration above.

-- `decodePhdrs`, `decodeShdrs`, `decodeDynsym` and the matching
-- `writeArray_Foo_write_extract` theorems are DSL-generated from
-- the `with_array_decoder <Name>` clauses on the schemas above.

namespace Decode

open Layout

/-! ## `.dynamic` loop-decoder (terminates at DT_NULL) -/

/-- Decode dynamic entries starting at `baseOff` until a DT_NULL is seen
    (inclusive). Caller provides `maxCount` (from DT_DYNAMIC section
    size) as a termination bound. Returns the entries read including
    the DT_NULL terminator if found; otherwise all `maxCount` entries.
    Totality: `maxCount - i` strictly decreases on each recursive
    call. -/
def decodeDynamicLoop (bs : ByteArray) (baseOff : Nat)
    (maxCount i : Nat) (acc : Array DynEntry) : Array DynEntry :=
  if h : i ≥ maxCount then acc
  else
    let e := decodeDynEntry bs (baseOff + i * dynEntrySize)
    let acc' := acc.push e
    match e.tag with
    | .null => acc'
    | _     =>
      have : maxCount - (i + 1) < maxCount - i := by
        have hLt : i < maxCount := Nat.lt_of_not_le h
        omega
      decodeDynamicLoop bs baseOff maxCount (i + 1) acc'
  termination_by maxCount - i

def decodeDynamic (bs : ByteArray) (baseOff : Nat) (maxCount : Nat) :
    Array DynEntry :=
  decodeDynamicLoop bs baseOff maxCount 0 #[]

theorem decodeDynamicLoop_size_le (bs : ByteArray) (baseOff maxCount i : Nat)
    (acc : Array DynEntry) :
    (decodeDynamicLoop bs baseOff maxCount i acc).size ≤ acc.size + (maxCount - i) := by
  unfold decodeDynamicLoop
  by_cases hGe : i ≥ maxCount
  · simp [hGe]
  · have hI : i < maxCount := Nat.lt_of_not_le hGe
    simp only [hGe, ↓reduceDIte]
    cases h : (decodeDynEntry bs (baseOff + i * dynEntrySize)).tag with
    | null =>
      simp only [h]
      simp only [Array.size_push]
      have : maxCount - i ≥ 1 := by omega
      omega
    | _ =>
      all_goals (
        simp only [h]
        have hRec := decodeDynamicLoop_size_le bs baseOff maxCount (i + 1)
          ((acc.push (decodeDynEntry bs (baseOff + i * dynEntrySize)))))
      all_goals (simp [Array.size_push] at hRec; omega)
  termination_by maxCount - i

theorem decodeDynamic_size_le (bs : ByteArray) (baseOff maxCount : Nat) :
    (decodeDynamic bs baseOff maxCount).size ≤ maxCount := by
  unfold decodeDynamic
  have := decodeDynamicLoop_size_le bs baseOff maxCount 0 #[]
  simpa using this


/-! ## Verneed / Vernaux chain decoders (variable-size, linked-list shape) -/

/-- Decode the Vernaux chain starting at `startOff`. -/
def decodeVernauxChain (bs : ByteArray) (startOff : Nat) (maxAux : Nat) :
    Array Vernaux :=
  decodeChain (decodeVernaux bs) (·.vna_next) startOff maxAux

/-- Decode one Verneed (header + chained Vernauxes) at `bs[off..]`. -/
def decodeVerneed (bs : ByteArray) (off : Nat) : Verneed :=
  let vn_version := Reader.readU16 bs (off + VerneedField.vn_version.byteOffset)
  let vn_cnt     := Reader.readU16 bs (off + VerneedField.vn_cnt.byteOffset)
  let vn_file    := Reader.readU32 bs (off + VerneedField.vn_file.byteOffset)
  let vn_aux     := Reader.readU32 bs (off + VerneedField.vn_aux.byteOffset)
  let vn_next    := Reader.readU32 bs (off + VerneedField.vn_next.byteOffset)
  let aux := decodeVernauxChain bs (off + vn_aux.toNat) vn_cnt.toNat
  { vn_version := vn_version, vn_cnt := vn_cnt, vn_file := vn_file,
    vn_aux := vn_aux, vn_next := vn_next, aux := aux }

/-- Decode the `.gnu.version_r` section starting at `baseOff`. -/
def decodeVerneedChain (bs : ByteArray) (baseOff : Nat) (maxNeed : Nat) :
    Array Verneed :=
  decodeChain (decodeVerneed bs) (·.vn_next) baseOff maxNeed

theorem decodeVerneedChain_size_le (bs : ByteArray) (baseOff maxNeed : Nat) :
    (decodeVerneedChain bs baseOff maxNeed).size ≤ maxNeed := by
  unfold decodeVerneedChain
  exact decodeChain_size_le _ _ baseOff maxNeed

theorem decodeVernauxChain_size_le (bs : ByteArray) (startOff maxAux : Nat) :
    (decodeVernauxChain bs startOff maxAux).size ≤ maxAux := by
  unfold decodeVernauxChain
  exact decodeChain_size_le _ _ startOff maxAux

end Decode

/-! ## ElfHeader (64 bytes: embed ElfIdent + 13 primitive/wrapped)

    The first 16 bytes are the `ElfIdent` sub-struct, delegated to its
    own DSL-generated write / decode / roundtrip via the `embed` field
    kind. Because `ElfIdent`'s decoder takes a precondition (due to
    `raw_bytes … with_size_field`), we use the `embed … with_prec`
    variant; ElfHeader's decoder therefore also takes
    `(h : off + 64 ≤ bs.size)` and `skip_bytewidth`. -/

elf_schema ElfHeader := 64
  decode_as decodeHeader
  roundtrip_as ElfHeader_write_decodeHeader_extract
  skip_bytewidth
  ident     : embed ElfIdent bytes 16 with_prec
              write_as ElfIdent.write
              decode_as Decode.decodeElfIdent
              roundtrip_as ElfIdent_write_decodeElfIdent_extract
              forward_as ElfIdent_decode_write
              append_left_as decodeElfIdent_append_left @ 0
  objType   : u16 @ 16
  machine   : u16 @ 18
  version   : u32 @ 20
  entry     : u64 @ 24 wrap_nat VirtualAddr val
  phoff     : u64 @ 32 wrap_nat FileOffset val
  shoff     : u64 @ 40 wrap_nat FileOffset val
  flags     : u32 @ 48
  ehsize    : u16 @ 52
  phentsize : u16 @ 54
  phnum     : u16 @ 56
  shentsize : u16 @ 58
  shnum     : u16 @ 60
  shstrndx  : u16 @ 62

-- `ElfHeader_decode_write` is DSL-emitted from the `elf_schema`
-- declaration above (prec-with-embed-at-0 branch).  The proof
-- shape: cases destruct + hSz : (ElfIdent.write ident).size = 16
-- + simp + refine 14 underscores + per-leg tactics.  The embed
-- leg uses 13 iterations of `decodeElfIdent_append_left` then
-- closes via `ElfIdent_decode_write`; each primitive/wrapped leg
-- uses the standard chain-peel template with `[ByteArray.size_append,
-- hSz]` as size simp hints.

/-! ### Slice-based decoder

    The DSL-emitted `Decode.decodeHeader bs off h` reads bytes at
    `(off + k)` for k ∈ [0, 64).  Its result depends only on the
    64-byte window `bs.extract off (off+64)`, but the type signature
    exposes the full `bs`.  This abstraction leak forces the kernel
    to do per-field unification when proving equality of decoder
    outputs on different (but window-equal) buffers — costing
    enough heartbeats to time out for `parse_encode_roundtrip`.

    `Decode.decodeHeaderSlice` exposes a window-only signature.
    `decodeHeader_eq_slice` shows the existing decoder is just a
    wrapper around it.  Equality of decoder outputs on equal
    windows then follows from `congrArg`, single rewrite,
    eliminating the 14-field cascade. -/

namespace Decode

/-- Window-form of `decodeHeader`: takes a 64-byte buffer and reads
    fields at fixed offsets `[0, 64)`.  The result depends ONLY on
    these 64 bytes, by definition. -/
def decodeHeaderSlice (bs : ByteArray) (h : 64 ≤ bs.size) : ElfHeader :=
  decodeHeader bs 0 (by omega)

end Decode

set_option maxHeartbeats 8000000 in
/-- The existing offset-form decoder equals the slice decoder applied
    to the extracted window.  Proves the abstraction leak is just a
    notational wrapper. -/
theorem decodeHeader_eq_slice (bs : ByteArray) (off : Nat) (h : off + 64 ≤ bs.size) :
    Decode.decodeHeader bs off h
      = Decode.decodeHeaderSlice (bs.extract off (off + 64)) (by
          rw [ByteArray.size_extract]; omega) := by
  show Decode.decodeHeader bs off h = Decode.decodeHeader _ 0 _
  -- The 14-field decoder agrees on the two buffers (one reads at
  -- (off + k); the other at (extract bs off (off+64))[0 + k]).  Use
  -- `simp only` to unfold the decoder, then `ElfHeader.mk.injEq` to
  -- decompose into per-field equalities.
  simp only [Decode.decodeHeader, ElfHeader.mk.injEq,
             FileOffset.mk.injEq, VirtualAddr.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- ident: decodeElfIdent agrees on the two extracted views.
    -- Reduce via per-byte equality on the inner extracts.
    simp only [Decode.decodeElfIdent, ElfIdent.mk.injEq, Reader.readBytes]
    refine ⟨?_, ?_, ?_⟩
    · -- head: bs.extract (off+0) (off+0+7) = (extract bs off (off+64)).extract (0+0) (0+0+7)
      apply ByteArray.ext_getElem
      · rw [ByteArray.size_extract, ByteArray.size_extract, ByteArray.size_extract]
        omega
      · intros i _ _
        rw [ByteArray.getElem_extract, ByteArray.getElem_extract,
            ByteArray.getElem_extract]
        congr 1; omega
    · -- osAbi
      show OsAbi.ofByte (Reader.readU8 bs _) = OsAbi.ofByte (Reader.readU8 _ _)
      rw [readU8_extract_eq bs off 64 7 (by omega) h]
    · -- tail
      apply ByteArray.ext_getElem
      · rw [ByteArray.size_extract, ByteArray.size_extract, ByteArray.size_extract]
        omega
      · intros i _ _
        rw [ByteArray.getElem_extract, ByteArray.getElem_extract,
            ByteArray.getElem_extract]
        congr 1; omega
  · exact readU16_extract_eq bs off 64 16 (by omega) h
  · exact readU16_extract_eq bs off 64 18 (by omega) h
  · exact readU32_extract_eq bs off 64 20 (by omega) h
  -- entry / phoff / shoff are wrap_nat now: goals are (.toNat = .toNat).
  · simp only [Nat.zero_add]; exact congrArg UInt64.toNat (readU64_extract_eq bs off 64 24 (by omega) h)
  · simp only [Nat.zero_add]; exact congrArg UInt64.toNat (readU64_extract_eq bs off 64 32 (by omega) h)
  · simp only [Nat.zero_add]; exact congrArg UInt64.toNat (readU64_extract_eq bs off 64 40 (by omega) h)
  · exact readU32_extract_eq bs off 64 48 (by omega) h
  · exact readU16_extract_eq bs off 64 52 (by omega) h
  · exact readU16_extract_eq bs off 64 54 (by omega) h
  · exact readU16_extract_eq bs off 64 56 (by omega) h
  · exact readU16_extract_eq bs off 64 58 (by omega) h
  · exact readU16_extract_eq bs off 64 60 (by omega) h
  · exact readU16_extract_eq bs off 64 62 (by omega) h

/-- `decodePhdr` depends only on bytes in `[off, off+56)`.  The decoder
    on `bs` at offset `off` agrees with the decoder on the extracted
    window at offset 0. -/
theorem decodePhdr_eq_slice (bs : ByteArray) (off : Nat) (h : off + 56 ≤ bs.size) :
    Decode.decodePhdr bs off
      = Decode.decodePhdr (bs.extract off (off + 56)) 0 := by
  simp only [Decode.decodePhdr, ProgramHeader.mk.injEq,
             FileOffset.mk.injEq, VirtualAddr.mk.injEq, PhysicalAddr.mk.injEq,
             ByteSize.mk.injEq, Alignment.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine congrArg _ ?_; exact readU32_extract_eq bs off 56 0 (by omega) h
  · exact readU32_extract_eq bs off 56 4 (by omega) h
  -- offset (wrap_nat): goal is (readU64 ..).toNat = (readU64 ..).toNat.
  · simp only [Nat.zero_add]; exact congrArg UInt64.toNat (readU64_extract_eq bs off 56 8 (by omega) h)
  · simp only [Nat.zero_add]; exact congrArg UInt64.toNat (readU64_extract_eq bs off 56 16 (by omega) h)
  · simp only [Nat.zero_add]; exact congrArg UInt64.toNat (readU64_extract_eq bs off 56 24 (by omega) h)
  · simp only [Nat.zero_add]; exact congrArg UInt64.toNat (readU64_extract_eq bs off 56 32 (by omega) h)
  · simp only [Nat.zero_add]; exact congrArg UInt64.toNat (readU64_extract_eq bs off 56 40 (by omega) h)
  · simp only [Nat.zero_add]; exact congrArg UInt64.toNat (readU64_extract_eq bs off 56 48 (by omega) h)

/-- `decodeDynEntry` depends only on bytes in `[off, off+16)`. -/
theorem decodeDynEntry_eq_slice (bs : ByteArray) (off : Nat) (h : off + 16 ≤ bs.size) :
    Decode.decodeDynEntry bs off
      = Decode.decodeDynEntry (bs.extract off (off + 16)) 0 := by
  simp only [Decode.decodeDynEntry, DynEntry.mk.injEq]
  refine ⟨?_, ?_⟩
  · -- tag: codec on a u64 read.
    show DynTag.decodeU64 (Reader.readU64 bs (off + 0))
       = DynTag.decodeU64 (Reader.readU64 ((bs.extract off (off + 16))) (0 + 0))
    rw [readU64_extract_eq bs off 16 0 (by omega) h]
  · exact readU64_extract_eq bs off 16 8 (by omega) h

/-- `decodeSym` depends only on bytes in `[off, off+24)`. -/
theorem decodeSym_eq_slice (bs : ByteArray) (off : Nat) (h : off + 24 ≤ bs.size) :
    Decode.decodeSym bs off
      = Decode.decodeSym (bs.extract off (off + 24)) 0 := by
  simp only [Decode.decodeSym, Symbol.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact readU32_extract_eq bs off 24 0 (by omega) h
  · exact readU8_extract_eq bs off 24 4 (by omega) h
  · exact readU8_extract_eq bs off 24 5 (by omega) h
  · exact readU16_extract_eq bs off 24 6 (by omega) h
  · exact readU64_extract_eq bs off 24 8 (by omega) h
  · exact readU64_extract_eq bs off 24 16 (by omega) h

/-- `decodeShdr` depends only on bytes in `[off, off+64)`. -/
theorem decodeShdr_eq_slice (bs : ByteArray) (off : Nat) (h : off + 64 ≤ bs.size) :
    Decode.decodeShdr bs off
      = Decode.decodeShdr (bs.extract off (off + 64)) 0 := by
  simp only [Decode.decodeShdr, SectionHeader.mk.injEq,
             FileOffset.mk.injEq, VirtualAddr.mk.injEq, ByteSize.mk.injEq,
             Alignment.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact readU32_extract_eq bs off 64 0 (by omega) h
  · refine congrArg _ ?_; exact readU32_extract_eq bs off 64 4 (by omega) h
  · exact readU64_extract_eq bs off 64 8 (by omega) h
  -- addr / offset / size / addralign / entsize are wrap_nat now.
  · simp only [Nat.zero_add]; exact congrArg UInt64.toNat (readU64_extract_eq bs off 64 16 (by omega) h)
  · simp only [Nat.zero_add]; exact congrArg UInt64.toNat (readU64_extract_eq bs off 64 24 (by omega) h)
  · simp only [Nat.zero_add]; exact congrArg UInt64.toNat (readU64_extract_eq bs off 64 32 (by omega) h)
  · exact readU32_extract_eq bs off 64 40 (by omega) h
  · exact readU32_extract_eq bs off 64 44 (by omega) h
  · simp only [Nat.zero_add]; exact congrArg UInt64.toNat (readU64_extract_eq bs off 64 48 (by omega) h)
  · simp only [Nat.zero_add]; exact congrArg UInt64.toNat (readU64_extract_eq bs off 64 56 (by omega) h)

/-! ## Verneed / SysV-hash / GNU-hash writers (variable-size) -/

/-- Write one Verneed header (16 bytes). Does NOT include the auxiliary
    chain — callers must emit it separately after the header. -/
def Verneed.writeHeader (v : Verneed) : ByteArray :=
  Writer.writeU16 v.vn_version
  ++ Writer.writeU16 v.vn_cnt
  ++ Writer.writeU32 v.vn_file
  ++ Writer.writeU32 v.vn_aux
  ++ Writer.writeU32 v.vn_next

/-- Write one Verneed plus its Vernaux chain. -/
def Verneed.write (v : Verneed) : ByteArray :=
  v.writeHeader ++ writeArray Vernaux.write v.aux

/-- Write a SysV `.hash` section: 8-byte header + buckets + chain.
    `numBuckets` and `numChain` are derived from array sizes. -/
def SysVHashTable.write (h : SysVHashTable) : ByteArray :=
  Writer.writeU32 h.buckets.size.toUInt32
  ++ Writer.writeU32 h.chain.size.toUInt32
  ++ writeArray Writer.writeU32 h.buckets
  ++ writeArray Writer.writeU32 h.chain

/-- Write a GNU `.gnu.hash` section: 16-byte header + bloom + buckets + chain.
    `numBuckets` and `maskwords` are derived from array sizes. -/
def GnuHashTable.write (h : GnuHashTable) : ByteArray :=
  Writer.writeU32 h.buckets.size.toUInt32
  ++ Writer.writeU32 h.symndx
  ++ Writer.writeU32 h.bloom.size.toUInt32
  ++ Writer.writeU32 h.shift2
  ++ writeArray Writer.writeU64 h.bloom
  ++ writeArray Writer.writeU32 h.buckets
  ++ writeArray Writer.writeU32 h.chain


end Patchelf.Elf
