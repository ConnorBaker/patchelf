/-
  Byte-layer encoder: `ElfFile → ByteArray`.

  Three-phase encode:

    1. `syncDtStrszInFile e`: rewrite DT_STRSZ entries in
       `.dynamic` to match `.dynstr.bytes.size`.  No-op if either
       section is absent.
    2. Conditional `layoutForEncoding`: if `layoutAlreadyValid e`
       returns false (section offsets overlap, or shdr table
       overlaps a section slot), repack sections contiguously
       after `max(ehdrSize, phdrTableEnd)` honoring addralign,
       update `header.shoff`, and retarget PT_INTERP/PT_DYNAMIC
       phdrs to their sections' new offsets + encodedSize.
       Skipped when the existing layout is already valid,
       preserving byte-for-byte stability on no-growth ops.
    3. Splice pipeline: allocate a zero buffer of size
       `encodedFileSize e`, splice header at 0, phdr table at
       `phoff`, shdr table at `shoff`, then each non-NOBITS
       non-NULL section at its offset.

  `encode_size_eq` in `ByteRoundtrip.lean` gives the output size
  unconditionally.  `parse_encode_roundtrip` (same file) closes
  the Tier D byte-roundtrip conditional on a
  `DecodeRoundtripWitness` bundle — see that file.
-/
module

public import Patchelf.Elf.ElfFile
public import Patchelf.Elf.Layout
public import Patchelf.Elf.Writer
public import Patchelf.Elf.Splice
public import Patchelf.Elf.Serialize
public import Patchelf.Elf.Schemas
public import Patchelf.Elf.DynamicLemmas
public import Patchelf.Elf.SectionOps
public import Patchelf.Elf.LayoutEngine

@[expose] public section

namespace Patchelf.Elf

open Layout
open Patchelf.Elf (ElfHeader DynEntry Symbol Verneed SysVHashTable GnuHashTable
                     StringTable SectionHeader ProgramHeader)
open Patchelf.Elf.Writer
open Patchelf.Elf.Encoder

/-- Serialize one Section's content back to bytes.  For `.nobits`,
    the output is empty (NOBITS sections occupy zero file bytes).  -/
def Section.writeContent (s : Section) : ByteArray :=
  match s.content with
  | .raw bs      => bs
  | .strtab st   => st.bytes
  | .dynamic ds  => writeArray Patchelf.Elf.DynEntry.write ds
  | .dynsym syms => writeArray Patchelf.Elf.Symbol.write syms
  | .versym vs   => writeArray writeU16 vs
  | .nobits      => ByteArray.empty

/-- Project a byte-layer Section to a SectionHeader for the encoded shdr
    table (content is dropped; size is derived from encodedSize). -/
def toShdr (s : Section) : SectionHeader :=
  { name := s.name, type := s.type, flags := s.flags, addr := s.addr,
    offset := s.offset, size := ⟨s.encodedSize⟩,
    link := s.link, info := s.info,
    addralign := s.addralign, entsize := s.entsize }

/-- Total encoded file size = max(shoff + shdr table, max(section end)). -/
def encodedFileSize (e : ElfFile) : Nat :=
  let ehdrEnd := Layout.ehdrSize
  let phdrEnd := e.header.phoff.val + e.phdrs.size * Layout.phdrSize
  let shdrEnd := e.header.shoff.val + e.sections.size * Layout.shdrSize
  let sectionEnd := e.sections.foldl (init := 0) fun acc s =>
    if s.type = ShType.SHT_NOBITS ∨ s.type = ShType.SHT_NULL then acc
    else max acc (s.offset.val + s.encodedSize)
  max (max ehdrEnd phdrEnd) (max shdrEnd sectionEnd)

/-- Allocate a zero-initialized ByteArray of the given size.
    Straightforward — backed by `ByteArray.mkEmpty` + iterated `push`. -/
def zeroBytes (n : Nat) : ByteArray :=
  (List.range n).foldl (fun acc _ => acc.push 0) ByteArray.empty

@[simp] theorem zeroBytes_size (n : Nat) : (zeroBytes n).size = n := by
  unfold zeroBytes
  induction n with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append]
    simp [ih]

/-- Sync DT_STRSZ entries in `.dynamic` to match the current
    `.dynstr.bytes.size`.  Mirrors C++ patchelf's rewriteSections pass.
    No-op when `.dynamic` or `.dynstr` is absent. -/
def syncDtStrszInFile (e : ElfFile) : ElfFile :=
  match e.dynstr, e.dynamic, e.dynamicIdx with
  | some ds, some dyn, some iDyn =>
      if _h : iDyn < e.sections.size then
        let newDyn := Patchelf.Elf.syncDtStrsz dyn ds.bytes.size.toUInt64
        e.updateSectionContent iDyn (.dynamic newDyn)
      else e
  | _, _, _ => e

/-- The per-section step the encoder folds.  Extracted to a named def
    so foldl-induction proofs can match the function shape. -/
def sectionFoldStep (buf : ByteArray) (s : Section) : ByteArray :=
  if s.type = ShType.SHT_NOBITS ∨ s.type = ShType.SHT_NULL then buf
  else splice buf s.offset.val s.writeContent

/-- Encoder body: splice cascade with no pre-passes.  Factored from
    `encode` so verification proofs can target it directly.

    Marked `@[irreducible]` so the kernel doesn't unfold it during
    `whnf`/`isDefEq` — every consumer reasons via `encodeBody_eq`
    propositionally instead.  Without this, per-byte-access proofs
    re-elaborate the entire splice cascade at every use site,
    compounding kernel cost. -/
@[irreducible] def encodeBody (e : ElfFile) : ByteArray :=
  let total := encodedFileSize e
  let buf0 := zeroBytes total
  let buf1 := splice buf0 0 (Patchelf.Elf.ElfHeader.write e.header)
  let buf2 := splice buf1 e.header.phoff.val
    (writeArray Patchelf.Elf.ProgramHeader.write e.phdrs)
  let buf3 := splice buf2 e.header.shoff.val
    (writeArray Patchelf.Elf.SectionHeader.write (e.sections.map toShdr))
  e.sections.foldl (init := buf3) sectionFoldStep

/-- Unfolding equation for `encodeBody`.  The propositional interface
    to its body — use `simp only [encodeBody_eq]` or `rw [encodeBody_eq]`
    instead of `unfold encodeBody`. -/
theorem encodeBody_eq (e : ElfFile) :
    encodeBody e =
      let total := encodedFileSize e
      let buf0 := zeroBytes total
      let buf1 := splice buf0 0 (Patchelf.Elf.ElfHeader.write e.header)
      let buf2 := splice buf1 e.header.phoff.val
        (writeArray Patchelf.Elf.ProgramHeader.write e.phdrs)
      let buf3 := splice buf2 e.header.shoff.val
        (writeArray Patchelf.Elf.SectionHeader.write (e.sections.map toShdr))
      e.sections.foldl (init := buf3) sectionFoldStep := by
  unfold encodeBody; rfl

/-- Encode a pure-IR ElfFile to bytes.

    Pipeline:
      0. Sync DT_STRSZ entries to match `.dynstr.bytes.size`.
      1. Conditional `layoutForEncoding` if current layout has overlaps.
      2. `encodeBody` — the splice cascade.

    Marked `@[irreducible]`; use `encode_eq` for propositional
    unfolding. -/
@[irreducible] def encode (e : ElfFile) : ByteArray :=
  let e := syncDtStrszInFile e
  let e := if layoutAlreadyValid e then e else layoutForEncoding e
  encodeBody e

theorem encode_eq (e : ElfFile) :
    encode e =
      encodeBody (let e' := syncDtStrszInFile e
                  if layoutAlreadyValid e' then e' else layoutForEncoding e') := by
  unfold encode; rfl

/-! ## Sizes match: writeContent.size = encodedSize.

    The encoder's per-section splice writes `s.writeContent` at offset
    `s.offset`.  The `IsValid` and `spliceRegionsDisjoint` predicates
    bound regions by `s.offset + s.encodedSize`.  These two have to be
    equal for the splice region to actually fit. -/

/-- The encoder's per-section payload size equals `encodedSize`.  This
    bridges the splice's actual byte count with the structural size
    used in disjointness predicates. -/
theorem Section_writeContent_size_eq (s : Section) :
    s.writeContent.size = s.encodedSize := by
  unfold Section.writeContent Section.encodedSize
  match s.content with
  | .raw _ => simp
  | .strtab _ => simp
  | .dynamic ds =>
    exact writeArray_size_of_uniform DynEntry.write Layout.dynEntrySize
            DynEntry.write_size ds
  | .dynsym syms =>
    exact writeArray_size_of_uniform Symbol.write Layout.symEntrySize
            Symbol.write_size syms
  | .versym vs =>
    exact writeArray_size_of_uniform Writer.writeU16 2 (fun _ => writeU16_size _) vs
  | .nobits => simp

/-! ## Section-fold splice preservation

    When all sections have offsets ≥ k, reads at any offset < k are
    preserved through the entire fold.  This is used by the Tier D
    bridge: after the section pass, bytes in regions occupied by
    header / phdr table / shdr table are unchanged from before the
    section pass. -/

/-- `readU8` at offset `r ∈ [lo, hi)` is preserved through a section-
    splice fold when every section's region is interval-disjoint from
    `[lo, hi)` and fits in `init`.

    The precondition uses `IntervalDisjoint`: each section is either
    NOBITS / NULL (skipped by the fold), or its region `[s.offset,
    s.offset + s.encodedSize)` is interval-disjoint from `[lo, hi)`.
    The OR form composes directly with `headerSectionDisjoint` (lo=0),
    `phdrSectionDisjoint` (lo=phoff), `shdrSectionDisjoint` (lo=shoff)
    from `spliceRegionsDisjoint`. -/
theorem readU8_foldl_section_splice_preserved
    (sections : Array Section) (lo hi : Nat) (init : ByteArray)
    (hKAll : ∀ (i : Nat) (hiB : i < sections.size),
      let s := sections[i]'hiB
      s.type = ShType.SHT_NOBITS ∨ s.type = ShType.SHT_NULL ∨
      (IntervalDisjoint lo hi s.offset.val
          (s.offset.val + s.encodedSize) ∧
       s.offset.val + s.encodedSize ≤ init.size))
    (r : Nat) (hrLo : lo ≤ r) (hrHi : r + 1 ≤ hi) (hrFit : r < init.size) :
    Reader.readU8 (sections.foldl (init := init) sectionFoldStep) r
      = Reader.readU8 init r := by
  have h := @Array.foldl_induction Section ByteArray sections
    (motive := fun _ (buf : ByteArray) =>
      buf.size = init.size ∧ Reader.readU8 buf r = Reader.readU8 init r)
    (init := init) (h0 := ⟨rfl, rfl⟩)
    (f := sectionFoldStep)
    (hf := by
      intros i buf ih
      obtain ⟨hSz, hRd⟩ := ih
      unfold sectionFoldStep
      split
      · exact ⟨hSz, hRd⟩
      · rename_i hSec
        have hSec' : sections[i].type ≠ ShType.SHT_NOBITS
                  ∧ sections[i].type ≠ ShType.SHT_NULL :=
          ⟨fun h => hSec (Or.inl h), fun h => hSec (Or.inr h)⟩
        have hk := hKAll i i.isLt
        rcases hk with hNB | hNULL | hOK
        · exact absurd hNB hSec'.1
        · exact absurd hNULL hSec'.2
        obtain ⟨hIDisj, hSizeFit⟩ := hOK
        have hWcSz : (sections[i]'i.isLt).writeContent.size
                    = (sections[i]'i.isLt).encodedSize :=
          Section_writeContent_size_eq _
        have hSpliceFit : (sections[i]'i.isLt).offset.val
                          + (sections[i]'i.isLt).writeContent.size ≤ buf.size := by
          rw [hSz, hWcSz]; exact hSizeFit
        -- IntervalDisjoint lo hi gives: hi ≤ s.offset  ∨  s.end ≤ lo.
        -- For the splice-disjoint precondition we need:
        --   r + 1 ≤ s.offset   ∨   s.end ≤ r.
        -- Branch (a): hi ≤ s.offset combined with r + 1 ≤ hi gives r + 1 ≤ s.offset.
        -- Branch (b): s.end ≤ lo combined with lo ≤ r gives s.end ≤ r.
        have hSecEq : sections[i] = sections[i.val]'i.isLt := rfl
        have hDisj : r + 1 ≤ (sections[i]'i.isLt).offset.val
                  ∨ (sections[i]'i.isLt).offset.val
                    + (sections[i]'i.isLt).writeContent.size ≤ r := by
          rw [hSecEq]
          rcases hIDisj with hLeft | hRight
          · left; omega
          · right
            rw [show (sections[i.val]'i.isLt).writeContent.size
                  = (sections[i.val]'i.isLt).encodedSize from
                  Section_writeContent_size_eq _]
            omega
        refine ⟨?_, ?_⟩
        · rw [splice_size]; exact hSz
        · rw [Reader.readU8_splice_disjoint buf (sections[i]'i.isLt).offset.val
              (sections[i]'i.isLt).writeContent hSpliceFit r (by rw [hSz]; exact hrFit) hDisj]
          exact hRd)
  exact h.2

/-- `readU16` analog of `readU8_foldl_section_splice_preserved`. -/
theorem readU16_foldl_section_splice_preserved
    (sections : Array Section) (lo hi : Nat) (init : ByteArray)
    (hKAll : ∀ (i : Nat) (hiB : i < sections.size),
      let s := sections[i]'hiB
      s.type = ShType.SHT_NOBITS ∨ s.type = ShType.SHT_NULL ∨
      (IntervalDisjoint lo hi s.offset.val
          (s.offset.val + s.encodedSize) ∧
       s.offset.val + s.encodedSize ≤ init.size))
    (r : Nat) (hrLo : lo ≤ r) (hrHi : r + 2 ≤ hi) (hrFit : r + 2 ≤ init.size) :
    Reader.readU16 (sections.foldl (init := init) sectionFoldStep) r
      = Reader.readU16 init r := by
  unfold Reader.readU16
  rw [readU8_foldl_section_splice_preserved sections lo hi init hKAll r
      hrLo (by omega) (by omega)]
  rw [readU8_foldl_section_splice_preserved sections lo hi init hKAll (r + 1)
      (by omega) (by omega) (by omega)]

/-- `readU32` analog. -/
theorem readU32_foldl_section_splice_preserved
    (sections : Array Section) (lo hi : Nat) (init : ByteArray)
    (hKAll : ∀ (i : Nat) (hiB : i < sections.size),
      let s := sections[i]'hiB
      s.type = ShType.SHT_NOBITS ∨ s.type = ShType.SHT_NULL ∨
      (IntervalDisjoint lo hi s.offset.val
          (s.offset.val + s.encodedSize) ∧
       s.offset.val + s.encodedSize ≤ init.size))
    (r : Nat) (hrLo : lo ≤ r) (hrHi : r + 4 ≤ hi) (hrFit : r + 4 ≤ init.size) :
    Reader.readU32 (sections.foldl (init := init) sectionFoldStep) r
      = Reader.readU32 init r := by
  unfold Reader.readU32
  rw [readU8_foldl_section_splice_preserved sections lo hi init hKAll r
      hrLo (by omega) (by omega)]
  rw [readU8_foldl_section_splice_preserved sections lo hi init hKAll (r + 1)
      (by omega) (by omega) (by omega)]
  rw [readU8_foldl_section_splice_preserved sections lo hi init hKAll (r + 2)
      (by omega) (by omega) (by omega)]
  rw [readU8_foldl_section_splice_preserved sections lo hi init hKAll (r + 3)
      (by omega) (by omega) (by omega)]

/-- `readU64` analog. -/
theorem readU64_foldl_section_splice_preserved
    (sections : Array Section) (lo hi : Nat) (init : ByteArray)
    (hKAll : ∀ (i : Nat) (hiB : i < sections.size),
      let s := sections[i]'hiB
      s.type = ShType.SHT_NOBITS ∨ s.type = ShType.SHT_NULL ∨
      (IntervalDisjoint lo hi s.offset.val
          (s.offset.val + s.encodedSize) ∧
       s.offset.val + s.encodedSize ≤ init.size))
    (r : Nat) (hrLo : lo ≤ r) (hrHi : r + 8 ≤ hi) (hrFit : r + 8 ≤ init.size) :
    Reader.readU64 (sections.foldl (init := init) sectionFoldStep) r
      = Reader.readU64 init r := by
  unfold Reader.readU64
  rw [readU32_foldl_section_splice_preserved sections lo hi init hKAll r
      hrLo (by omega) (by omega)]
  rw [readU32_foldl_section_splice_preserved sections lo hi init hKAll (r + 4)
      (by omega) (by omega) (by omega)]

/-! ## Per-section foldl recovery

    For section `i` (non-NOBITS, non-NULL) at offset `s_i.offset` with
    payload `s_i.writeContent`, the section foldl writes that payload
    into the buffer at `s_i.offset`.  Reading at any offset
    `r ∈ [s_i.offset, s_i.offset + s_i.encodedSize)` of the foldl's
    output recovers the corresponding byte of `s_i.writeContent`.

    The proof carries a two-state invariant through `foldl_induction`:
    after processing array index k,
      (a) if `k ≤ i`: byte at `r` is unchanged from `init` (sections
          0..k-1 are all disjoint from section i's region, by
          `sectionsNonOverlapping`).
      (b) if `k > i`: byte at `r` equals `s_i.writeContent[r - s_i.offset]`
          (section i was processed, splicing the payload; subsequent
          sections k > i don't touch the region by disjointness).

    This combines disjointness preservation with splice-inside; it's
    different from `readU{N}_foldl_section_splice_preserved` which only
    handles the disjoint case (no section is the read region's owner). -/

theorem readU8_foldl_section_recovers
    (sections : Array Section) (init : ByteArray)
    (i : Nat) (hi : i < sections.size)
    (hType_NB : (sections[i]'hi).type ≠ ShType.SHT_NOBITS)
    (hType_NL : (sections[i]'hi).type ≠ ShType.SHT_NULL)
    (hSizeFit : (sections[i]'hi).offset.val
                + (sections[i]'hi).encodedSize ≤ init.size)
    (hOverlap : ∀ (j : Nat) (hj : j < sections.size), i ≠ j →
      (sections[j]'hj).type = ShType.SHT_NOBITS ∨
      (sections[j]'hj).type = ShType.SHT_NULL ∨
      IntervalDisjoint
        (sections[j]'hj).offset.val
        ((sections[j]'hj).offset.val + (sections[j]'hj).encodedSize)
        (sections[i]'hi).offset.val
        ((sections[i]'hi).offset.val + (sections[i]'hi).encodedSize))
    (hSizesFit : ∀ (j : Nat) (hj : j < sections.size),
      (sections[j]'hj).type = ShType.SHT_NOBITS ∨
      (sections[j]'hj).type = ShType.SHT_NULL ∨
      (sections[j]'hj).offset.val
        + (sections[j]'hj).encodedSize ≤ init.size)
    (k : Nat) (hk : k < (sections[i]'hi).encodedSize) :
    Reader.readU8
      (sections.foldl (init := init) sectionFoldStep)
      ((sections[i]'hi).offset.val + k)
      = Reader.readU8 (sections[i]'hi).writeContent k := by
  -- Convenience aliases for the read offset.
  let off_i := (sections[i]'hi).offset.val
  let r := off_i + k
  -- We need to track the foldl through the section array, with the
  -- two-state invariant.  After processing array index `m`:
  --   (a) m ≤ i: byte at r is unchanged from init.
  --   (b) m > i: byte at r equals writeContent[k] (splice already happened).
  have h := @Array.foldl_induction Section ByteArray sections
    (motive := fun (m : Nat) (buf : ByteArray) =>
      buf.size = init.size ∧
      ((m ≤ i ∧ Reader.readU8 buf r = Reader.readU8 init r) ∨
       (m > i ∧ Reader.readU8 buf r
          = Reader.readU8 (sections[i]'hi).writeContent k)))
    (init := init)
    (h0 := ⟨rfl, Or.inl ⟨Nat.zero_le _, rfl⟩⟩)
    (f := sectionFoldStep)
    (hf := by
      intros m buf ih
      obtain ⟨hSz, hAB⟩ := ih
      unfold sectionFoldStep
      split
      · -- Skipped section (NOBITS/NULL).  buf unchanged.
        refine ⟨hSz, ?_⟩
        rcases hAB with ⟨hLe, hRd⟩ | ⟨hGt, hRd⟩
        · -- Was case (a).  Need to know whether m+1 ≤ i or m+1 > i.
          by_cases hSucc : m.val + 1 ≤ i
          · exact Or.inl ⟨hSucc, hRd⟩
          · -- m + 1 > i, so m ≥ i; combined with m ≤ i, m = i.  But
            -- this iteration skipped (NOBITS/NULL) and section i is
            -- NOT NOBITS/NULL.  Contradiction.
            have hMI : m.val = i := by omega
            rename_i hSec
            have hSecAtI : (sections[i]'hi).type = ShType.SHT_NOBITS ∨
                           (sections[i]'hi).type = ShType.SHT_NULL := by
              rw [show sections[i]'hi = sections[m] from by
                  show sections[i]'hi = sections[m.val]'m.isLt
                  congr 1; exact hMI.symm]
              exact hSec
            rcases hSecAtI with hN | hN
            · exact absurd hN hType_NB
            · exact absurd hN hType_NL
        · -- Already in case (b).  m+1 > i too (since m > i).
          exact Or.inr ⟨by omega, hRd⟩
      · -- Splicing case.
        rename_i hSec
        have hSec' : sections[m].type ≠ ShType.SHT_NOBITS
                  ∧ sections[m].type ≠ ShType.SHT_NULL :=
          ⟨fun h => hSec (Or.inl h), fun h => hSec (Or.inr h)⟩
        have hWcSz : (sections[m]'m.isLt).writeContent.size
                    = (sections[m]'m.isLt).encodedSize :=
          Section_writeContent_size_eq _
        -- Splice fits.
        have hMSizeFit := hSizesFit m.val m.isLt
        rcases hMSizeFit with hN | hN | hMSize
        · exact absurd hN hSec'.1
        · exact absurd hN hSec'.2
        have hSpliceFit : (sections[m]'m.isLt).offset.val
                        + (sections[m]'m.isLt).writeContent.size ≤ buf.size := by
          rw [hSz, hWcSz]; exact hMSize
        refine ⟨by rw [splice_size]; exact hSz, ?_⟩
        rcases hAB with ⟨hLe, hRd⟩ | ⟨hGt, hRd⟩
        · -- Case (a) → split on whether m = i or m < i.
          by_cases hMEq : m.val = i
          · -- m = i: this is THE splice for section i.
            -- sections[m] = sections[i] under hMEq.
            have hMI : sections[m] = sections[i]'hi := by
              show sections[m.val]'m.isLt = sections[i]'hi
              congr 1
            have hOI : (sections[m]'m.isLt).offset.val = off_i := by
              rw [hMI]
            have hRdNew : Reader.readU8 (splice buf
                              (sections[m]'m.isLt).offset.val
                              (sections[m]'m.isLt).writeContent) r
                        = Reader.readU8 (sections[m]'m.isLt).writeContent
                            (r - (sections[m]'m.isLt).offset.val) := by
              apply Reader.readU8_splice_at_off_inside buf _
                (sections[m]'m.isLt).writeContent hSpliceFit r
              · rw [hOI]; show off_i ≤ off_i + k; omega
              · rw [hOI, hWcSz, hMI]; show off_i + k < off_i + (sections[i]'hi).encodedSize; omega
            rw [hRdNew]
            rw [hMI, show r - off_i = k from by show off_i + k - off_i = k; omega]
            exact Or.inr ⟨by omega, rfl⟩
          · -- m ≠ i.  Use disjointness (sectionsNonOverlapping).
            have hINeM : i ≠ m.val := fun h => hMEq h.symm
            have hMOverlap := hOverlap m.val m.isLt hINeM
            rcases hMOverlap with hN | hN | hDisj
            · exact absurd hN hSec'.1
            · exact absurd hN hSec'.2
            -- Disjoint: r is preserved through this splice.
            have hOffMEq : (sections[m]'m.isLt).offset.val
                           = sections[m.val].offset.val := rfl
            have hSzMEq : (sections[m]'m.isLt).encodedSize
                          = sections[m.val].encodedSize := rfl
            have hRdNew : Reader.readU8 (splice buf
                              (sections[m]'m.isLt).offset.val
                              (sections[m]'m.isLt).writeContent) r
                        = Reader.readU8 buf r := by
              apply Reader.readU8_splice_disjoint buf _
                (sections[m]'m.isLt).writeContent hSpliceFit r
              · rw [hSz]
                -- r < init.size from hSizeFit.
                show off_i + k < init.size; omega
              unfold IntervalDisjoint at hDisj
              rw [hWcSz, hOffMEq, hSzMEq]
              rcases hDisj with hL | hR
              · right; omega
              · left; omega
            rw [hRdNew, hRd]
            -- Need to update the case label: (a) m+1 ≤ i?
            by_cases hSucc : m.val + 1 ≤ i
            · exact Or.inl ⟨hSucc, rfl⟩
            · -- m+1 > i with m ≠ i implies m > i, but m ≤ i.  Contradiction.
              omega
        · -- Case (b): m > i, so m ≠ i (and section i was processed
          -- earlier, leaving writeContent at r).  Disjointness preserves.
          have hMNeI : i ≠ m.val := by omega
          have hMOverlap := hOverlap m.val m.isLt hMNeI
          rcases hMOverlap with hN | hN | hDisj
          · exact absurd hN hSec'.1
          · exact absurd hN hSec'.2
          -- hDisj has sections[↑m] but the splice-disjoint goal has sections[m] —
          -- bridge them by adding a definitional aliases.
          have hOffMEq : (sections[m]'m.isLt).offset.val
                         = sections[m.val].offset.val := rfl
          have hSzMEq : (sections[m]'m.isLt).encodedSize
                        = sections[m.val].encodedSize := rfl
          have hRdNew : Reader.readU8 (splice buf
                            (sections[m]'m.isLt).offset.val
                            (sections[m]'m.isLt).writeContent) r
                      = Reader.readU8 buf r := by
            apply Reader.readU8_splice_disjoint buf _
              (sections[m]'m.isLt).writeContent hSpliceFit r
            · rw [hSz]; show off_i + k < init.size; omega
            unfold IntervalDisjoint at hDisj
            rw [hWcSz, hOffMEq, hSzMEq]
            rcases hDisj with hL | hR
            · right; omega
            · left; omega
          rw [hRdNew, hRd]
          exact Or.inr ⟨by omega, rfl⟩)
  -- The motive at array end (m = sections.size > i): we're in case (b).
  obtain ⟨_, hAB⟩ := h
  rcases hAB with ⟨hLe, _⟩ | ⟨_, hRd⟩
  · -- Case (a) at end: sections.size ≤ i, but i < sections.size.  Contradiction.
    omega
  · exact hRd

/-- The encoder body's output has size exactly `encodedFileSize`.
    This is `encode_size_eq` specialized to `encodeBody` (i.e. without
    the pre-passes). -/
theorem encodeBody_size_eq (e : ElfFile) :
    (encodeBody e).size = encodedFileSize e := by
  unfold encodeBody
  simp only []
  have hFold : ∀ (buf : ByteArray) (ss : Array Section),
      (ss.foldl (init := buf) sectionFoldStep).size = buf.size := by
    intro buf ss
    have := @Array.foldl_induction Section ByteArray ss
      (motive := fun (_ : Nat) (b : ByteArray) => b.size = buf.size)
      (init := buf) rfl (f := sectionFoldStep)
      (by intro i b hb; unfold sectionFoldStep; split
          · exact hb
          · rw [splice_size]; exact hb)
    exact this
  rw [hFold, splice_size, splice_size, splice_size, zeroBytes_size]

/-- `encodedFileSize` always accommodates the ELF header at offset 0. -/
theorem encodedFileSize_ge_ehdr (e : ElfFile) :
    Layout.ehdrSize ≤ encodedFileSize e := by
  unfold encodedFileSize
  simp only []
  exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)

/-- The encoder body's output is at least 64 bytes long. -/
theorem encodeBody_size_ge_ehdr (e : ElfFile) :
    Layout.ehdrSize ≤ (encodeBody e).size := by
  rw [encodeBody_size_eq]; exact encodedFileSize_ge_ehdr e

/-! ## Bound-fitting lemmas

    Each region the encoder splices into the output buffer must fit
    within `encodedFileSize`.  These four lemmas discharge that for
    each region kind:

      * `phdr_end_le_encodedFileSize` — the program header table
        ends at `phoff + phnum * phdrSize ≤ encodedFileSize`.
      * `shdr_end_le_encodedFileSize` — the section header table
        ends at `shoff + shnum * shdrSize ≤ encodedFileSize`.
      * `section_end_le_encodedFileSize` — each non-NOBITS, non-NULL
        section ends at `s.offset + s.encodedSize ≤ encodedFileSize`.

    `encodedFileSize_ge_ehdr` (above) covers the ELF header itself.

    Used to discharge `parseHeader_ok` and the per-section decode
    obligations in the unconditional Tier D bridge: knowing each
    region fits inside the encoded buffer is exactly the
    precondition required by the splice/disjoint preservation
    lemmas. -/

/-- The phdr table fits inside the encoded buffer.  Direct max-of-max:
    `phdrEnd ≤ max ehdrEnd phdrEnd ≤ max (max ehdrEnd phdrEnd) (...)`. -/
theorem phdr_end_le_encodedFileSize (e : ElfFile) :
    e.header.phoff.val + e.phdrs.size * Layout.phdrSize ≤ encodedFileSize e := by
  unfold encodedFileSize
  exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)

/-- The shdr table fits inside the encoded buffer.  Same pattern as
    `phdr_end_le_encodedFileSize`. -/
theorem shdr_end_le_encodedFileSize (e : ElfFile) :
    e.header.shoff.val + e.sections.size * Layout.shdrSize ≤ encodedFileSize e := by
  unfold encodedFileSize
  exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

/-- For any non-NOBITS/non-NULL section, its byte range fits inside
    the encoded buffer.  Foldl-max-monotonic: each non-NOBITS/non-NULL
    section's end-offset gets folded into the running max via
    `max acc (s.offset + s.encodedSize)`. -/
theorem section_end_le_encodedFileSize (e : ElfFile)
    (i : Nat) (hi : i < e.sections.size)
    (hType : (e.sections[i]'hi).type ≠ ShType.SHT_NOBITS)
    (hType' : (e.sections[i]'hi).type ≠ ShType.SHT_NULL) :
    (e.sections[i]'hi).offset.val + (e.sections[i]'hi).encodedSize
      ≤ encodedFileSize e := by
  unfold encodedFileSize
  -- Goal: section_i_end ≤ max (max ehdrEnd phdrEnd) (max shdrEnd sectionEnd)
  -- Reduces to: section_i_end ≤ sectionEnd.
  refine Nat.le_trans ?_ (Nat.le_max_right _ _)
  refine Nat.le_trans ?_ (Nat.le_max_right _ _)
  -- Goal: section_i_end ≤ sectionEnd, where sectionEnd is the foldl-max.
  -- Foldl-induction: invariant motive(k, acc) = if any of the first
  -- k sections is non-NOBITS/non-NULL with the target as section_i,
  -- then acc ≥ section_i_end.  Since section_i is by index `i < k`
  -- when k = e.sections.size, the invariant gives the bound.
  have h := @Array.foldl_induction Section Nat e.sections
    (motive := fun (k : Nat) (acc : Nat) =>
      ∀ (j : Nat) (hj : j < k) (hjBound : j < e.sections.size),
        (e.sections[j]'hjBound).type ≠ ShType.SHT_NOBITS →
        (e.sections[j]'hjBound).type ≠ ShType.SHT_NULL →
        (e.sections[j]'hjBound).offset.val
          + (e.sections[j]'hjBound).encodedSize ≤ acc)
    (init := 0)
    (h0 := by
      intros j hj _ _ _
      exact absurd hj (Nat.not_lt_zero j))
    (f := fun acc s =>
      if s.type = ShType.SHT_NOBITS ∨ s.type = ShType.SHT_NULL then acc
      else max acc (s.offset.val + s.encodedSize))
    (hf := by
      intros k acc hMot j hj hjBound hjType hjType'
      -- Beta-reduce the step function.
      simp only []
      -- j < k+1 split: j < k (use IH) or j = k (current step).
      by_cases hjLt : j < k
      · -- Recursive case.
        have hRec := hMot j hjLt hjBound hjType hjType'
        split <;> first
          | exact hRec
          | exact Nat.le_trans hRec (Nat.le_max_left _ _)
      · -- j = k: current section.
        have hjEq : j = k.val := by omega
        subst hjEq
        split
        next hOr =>
          exfalso
          rcases hOr with hN | hN
          · exact hjType hN
          · exact hjType' hN
        next _ =>
          exact Nat.le_max_right _ _)
  exact h i hi hi hType hType'

end Patchelf.Elf
