/-
  growEOF: append-at-end layout strategy.

  When ops grow section content beyond its original slot, the C++
  `rewriteSectionsLibrary` strategy is to append the moved sections
  to a new region at file end and either extend the last PT_LOAD or
  add a new one.  This module implements the simpler "extend last
  PT_LOAD" form.

  The strategy:
    1. Identify the last PT_LOAD phdr.  Its `p_offset + p_memsz` is
       the end of the loaded image; rounded up to `p_align`, this is
       the start of the appended region.
    2. Sections whose `[offset, offset + encodedSize)` overlaps any
       other section's range or the shdr table are "stale" — their
       on-disk layout is broken, so they need to move.
    3. Append every stale section to the appended region.  Each
       moved section gets a fresh `(offset, addr)` such that the
       new offset and addr differ by the same constant — this
       preserves segment congruence (`p_offset ≡ p_vaddr (mod p_align)`).
    4. Extend the last PT_LOAD's `p_filesz`/`p_memsz` to cover the
       new region.
    5. Place the shdr table at the end of the appended region; update
       `e.header.shoff`.
    6. Update PT_INTERP / PT_DYNAMIC offsets to track the moved
       `.interp` / `.dynamic` sections (if they moved).

  Sections that don't overflow keep their original `(offset, addr)`.
  This avoids the byte-shifting bug in the previous `layoutForEncoding`
  (which pulled every section forward to `phdrTableEnd ≈ 0x70`).

  Address-tag sync (DT_STRTAB → new dynstr.addr, etc.) is delegated
  to `syncDtAddrTagsInFile`; this module only handles the offset/addr
  layout itself.
-/
module

public import Patchelf.Elf.ElfFile
public import Patchelf.Elf.SectionOps
public import Patchelf.Elf.LayoutEngine

@[expose] public section

namespace Patchelf.Elf

open Layout

/-! ## Page-aligned end-of-file derivation

    Every PT_LOAD segment ends at `p_offset + p_memsz`; the tail of the
    loaded image is `max` over all such segments.  Round that up to
    the largest `p_align` (typically the page size) to find the start
    of the new region.

    For non-PT_LOAD phdrs (PHDR, INTERP, DYNAMIC, NOTE, ...), the
    end-of-file contribution is bounded by enclosing PT_LOADs, so
    we only walk PT_LOAD entries here. -/

/-- Largest `p_align` over PT_LOAD phdrs, or 1 if no PT_LOAD has
    `align ≥ 1`.  The result is at least 1 so it's safe to mod by. -/
def maxPtLoadAlign (phdrs : Array Patchelf.Elf.ProgramHeader) : Nat :=
  phdrs.foldl (init := 1) fun acc ph =>
    if ph.type = PhType.PT_LOAD ∧ acc < ph.align.val then ph.align.val else acc

/-- File-end offset of the loaded image: max `p_offset + p_filesz`
    over PT_LOAD phdrs.  Sections that don't sit inside a PT_LOAD
    don't contribute. -/
def maxPtLoadFileEnd (phdrs : Array Patchelf.Elf.ProgramHeader) : Nat :=
  phdrs.foldl (init := 0) fun acc ph =>
    if ph.type = PhType.PT_LOAD then max acc (ph.offset.val + ph.filesz.val) else acc

/-- Vaddr-end of the loaded image: max `p_vaddr + p_memsz` over PT_LOAD
    phdrs.  This is the next free virtual address. -/
def maxPtLoadVaddrEnd (phdrs : Array Patchelf.Elf.ProgramHeader) : Nat :=
  phdrs.foldl (init := 0) fun acc ph =>
    if ph.type = PhType.PT_LOAD then max acc (ph.vaddr.val + ph.memsz.val) else acc

/-- Index of the last PT_LOAD phdr, or `none` if none exists.
    Used to decide whether to extend the last PT_LOAD or add a new one
    (we always extend in this implementation; no PT_LOAD → no growth). -/
def lastPtLoadIdx (phdrs : Array Patchelf.Elf.ProgramHeader) : Option Nat :=
  Nat.fold phdrs.size (init := (none : Option Nat)) fun i hi acc =>
    if (phdrs[i]'hi).type = PhType.PT_LOAD then some i else acc

/-- Current "file end" for layout purposes: the maximum of section ends,
    shdr-table end, ehdr end, and phdr-table end.  This is where we'd
    place the appended region if no rounding were needed. -/
def currentFileEnd (e : ElfFile) : Nat :=
  let ehdrEnd := Layout.ehdrSize
  let phdrEnd := e.header.phoff.val + e.phdrs.size * Layout.phdrSize
  let shdrEnd := e.header.shoff.val + e.sections.size * Layout.shdrSize
  let secEnd := e.sections.foldl (init := 0) fun acc s =>
    if s.type = ShType.SHT_NOBITS ∨ s.type = ShType.SHT_NULL then acc
    else max acc (s.offset.val + s.encodedSize)
  max (max ehdrEnd phdrEnd) (max shdrEnd secEnd)

/-! ## Stale-section detection

    A section is "stale" when its current `[offset, offset + encodedSize)`
    overlaps another section's range or the shdr table — i.e. when
    `layoutAlreadyValid` would reject the file.  Stale sections must
    move; non-stale sections stay at their original offset. -/

/-- Does the byte range `[lo, hi)` overlap section `j`'s file range?
    NOBITS / NULL sections occupy zero file bytes, so they don't overlap. -/
def rangeOverlapsSection (lo hi : Nat) (s : Section) : Bool :=
  if s.type = ShType.SHT_NOBITS ∨ s.type = ShType.SHT_NULL then false
  else !decide (hi ≤ s.offset.val ∨ s.offset.val + s.encodedSize ≤ lo)

/-- Does section `i` overlap any *other* section in `e.sections`?
    Walks `e.sections` linearly. -/
def sectionOverlapsAny (e : ElfFile) (i : Nat) (h : i < e.sections.size) : Bool :=
  let s := e.sections[i]'h
  let sEnd := s.offset.val + s.encodedSize
  Nat.fold e.sections.size (init := false) fun j hj acc =>
    if j = i then acc
    else acc || rangeOverlapsSection s.offset.val sEnd (e.sections[j]'hj)

/-- Does section `i` (at `e.sections[i]`) overlap any other non-NOBITS,
    non-NULL section, or the shdr table?  This identifies sections
    whose current slot can't accommodate their encoded content. -/
def sectionStale (e : ElfFile) (i : Nat) (h : i < e.sections.size) : Bool :=
  let s := e.sections[i]'h
  if s.type = ShType.SHT_NOBITS ∨ s.type = ShType.SHT_NULL then false
  else
    let sEnd := s.offset.val + s.encodedSize
    let shdrLo := e.header.shoff.val
    let shdrHi := e.header.shoff.val + e.sections.size * Layout.shdrSize
    let overlapShdr := !decide (sEnd ≤ shdrLo ∨ shdrHi ≤ s.offset.val)
    overlapShdr || sectionOverlapsAny e i h

/-! ## Append-at-end placement

    Walk the section array; for each stale section, assign a new
    offset = startOffset + cumulativeBytes (where cumulativeBytes
    accumulates aligned section sizes), and a new addr = startPage +
    cumulativeBytes.  Equal deltas guarantee `p_offset ≡ p_vaddr
    (mod align)` is preserved. -/

/-- One step of the append-at-end fold.  Threads
    `(acc, cursor) : (Array Section × Nat)` where `cursor` is the
    cumulative offset *within* the appended region (so the new file
    offset is `startOffset + cursor`).

    For non-stale sections, push the section verbatim (no offset change).
    For stale sections, place at `startOffset + roundUp cursor addralign`,
    new addr = `startPage + roundUp cursor addralign`, and advance
    cursor by `roundUp cursor align + encodedSize`.

    The "cursor" reflects bytes in the appended region — it lets us
    compute next-section placement without revisiting prior state. -/
def appendStep (startOffset startPage : Nat)
    (acc : Array Section × Nat)
    (idxAndStaleAndSec : Nat × Bool × Section) : Array Section × Nat :=
  let (_, isStale, s) := idxAndStaleAndSec
  let (sectionsAcc, cursor) := acc
  if isStale then
    let off := roundUp cursor s.addralign.val
    let newOffset := startOffset + off
    let newAddr := startPage + off
    let s' : Section :=
      { s with offset := ⟨newOffset⟩, addr := ⟨newAddr⟩ }
    (sectionsAcc.push s', off + s.encodedSize)
  else
    (sectionsAcc.push s, cursor)

/-- Stale-aware section placement.  Walks `sections`, threading
    `(acc, cursor)`; non-stale sections are kept at their original
    offset, stale sections are placed in the appended region. -/
def appendStaleSections (sections : Array Section) (stale : Array Bool)
    (startOffset startPage : Nat) : Array Section × Nat :=
  let indexed := sections.mapIdx (fun i s =>
    (i, (stale[i]?.getD false), s))
  indexed.foldl (init := (Array.emptyWithCapacity sections.size, 0))
    (appendStep startOffset startPage)

/-! ## PT_LOAD update

    The last PT_LOAD's `p_filesz`/`p_memsz` get extended to cover the
    appended region.  Specifically, after move, the segment runs from
    `p_offset` to `startOffset + appendedBytes`.  -/

/-- Update the i-th phdr to be the extended last PT_LOAD if `i = lastIdx`,
    or to retarget PT_INTERP / PT_DYNAMIC if the corresponding section
    moved.

    For the last PT_LOAD, the segment must cover both:
      * the file region `[p_offset, fileEnd)` where `fileEnd` is one
        past the last appended byte → `filesz = fileEnd - p_offset`;
      * the vaddr region `[p_vaddr, vaddrEnd)` where `vaddrEnd` is one
        past the last moved section's vaddr → `memsz = vaddrEnd - p_vaddr`.

    These differ when the original segment had BSS (memsz > filesz). -/
def updatePhdrsAfterMove (phdrs : Array Patchelf.Elf.ProgramHeader)
    (lastIdx? : Option Nat) (newLastFilesz newLastMemsz : Nat)
    (interpIdx? dynamicIdx? : Option Nat)
    (newSections : Array Section) : Array Patchelf.Elf.ProgramHeader :=
  phdrs.mapIdx fun i ph =>
    let phLast :=
      match lastIdx? with
      | some lastIdx =>
          if i = lastIdx then
            { ph with filesz := ⟨newLastFilesz⟩
                    , memsz := ⟨max ph.memsz.val newLastMemsz⟩ }
          else ph
      | none => ph
    if phLast.type = PhType.PT_INTERP then
      match interpIdx? with
      | some iS =>
          if h : iS < newSections.size then
            let s := newSections[iS]'h
            { phLast with offset := s.offset
                        , vaddr := s.addr
                        , paddr := ⟨s.addr.val⟩
                        , filesz := ⟨s.encodedSize⟩
                        , memsz := ⟨s.encodedSize⟩ }
          else phLast
      | none => phLast
    else if phLast.type = PhType.PT_DYNAMIC then
      match dynamicIdx? with
      | some iS =>
          if h : iS < newSections.size then
            let s := newSections[iS]'h
            { phLast with offset := s.offset
                        , vaddr := s.addr
                        , paddr := ⟨s.addr.val⟩
                        , filesz := ⟨s.encodedSize⟩
                        , memsz := ⟨s.encodedSize⟩ }
          else phLast
      | none => phLast
    else phLast

/-! ## Main entry point -/

/-- Is it safe to extend the last PT_LOAD to cover a new region starting at
    file offset `startOffset` and vaddr `startPage`?

    Safe iff `roundUp(p_offset + p_memsz, alignStartPage) == startOffset`
    AND `roundUp(p_vaddr + p_memsz, alignStartPage) == startPage`.  The
    first ensures that extending filesz brings the new region's vaddr
    range to start exactly at the BSS-end (no overlap with existing BSS
    or sections).  The second is the analogue for vaddr.

    For binaries where the last PT_LOAD has lots of BSS (e.g. coreutils
    `ls` with 0x97000 BSS), this check fails and we'd need to allocate
    a new PT_LOAD instead — out of scope for the minimal implementation. -/
def canExtendLastPtLoad (e : ElfFile) (startOffset startPage alignStartPage : Nat)
    (lastIdx : Nat) : Bool :=
  if h : lastIdx < e.phdrs.size then
    let ph := e.phdrs[lastIdx]'h
    decide (ph.type = PhType.PT_LOAD) &&
    decide (roundUp (ph.offset.val + ph.memsz.val) alignStartPage = startOffset) &&
    decide (roundUp (ph.vaddr.val + ph.memsz.val) alignStartPage = startPage)
  else false

/-- Append-at-end layout strategy: when sections overflow their original
    slots, move them to a new region at file end, extend the last PT_LOAD
    to cover it, and update PT_INTERP / PT_DYNAMIC / shoff to match.

    Idempotent on already-laid-out files (no section is stale → nothing
    moves → output equals input modulo a possible shoff adjustment).

    When extending the last PT_LOAD would clobber its BSS (because
    `p_memsz > p_filesz` significantly), this function returns `e`
    unchanged.  The validator will then reject the output, signaling that
    a more aggressive layout strategy is needed.  Allocating a new
    PT_LOAD (which would handle this case) requires growing the phdr
    table and is left for future work.

    The `pageSize?` parameter, when `some n`, raises the alignment used
    for the appended region to `max n (maxPtLoadAlign e.phdrs)` — never
    below the binary's existing PT_LOAD alignment (dropping below
    would break the `p_offset ≡ p_vaddr (mod p_align)` congruence).
    Use `some 0x10000` for AArch64 (64KB pages); `none` falls back to
    auto-detection from the binary's PT_LOAD entries. -/
def growEOFWith (pageSize? : Option Nat) (e : ElfFile) : ElfFile :=
  -- Fast path: layout is already valid → nothing to do.
  if layoutAlreadyValid e then e
  else
    let detectedAlign := maxPtLoadAlign e.phdrs
    let alignStartPage :=
      match pageSize? with
      | some n => max n detectedAlign
      | none   => detectedAlign
    let lastIdx? := lastPtLoadIdx e.phdrs
    -- Compute startPage from max vaddr-end (rounded up to align).
    let startPage := roundUp (maxPtLoadVaddrEnd e.phdrs) alignStartPage
    -- Compute startOffset from current file end (rounded up to align).
    let startOffset := roundUp (currentFileEnd e) alignStartPage
    -- Safety gate: only proceed if we can extend the last PT_LOAD without
    -- clobbering BSS.  When this fails, fall back to `layoutForEncoding`'s
    -- repack — it doesn't preserve PT_LOAD coverage but it produces
    -- byte-disjoint output (the validator will reject if the binary
    -- becomes non-loadable; but for synthetic ELFs without PT_LOAD,
    -- there's nothing to load anyway and the splice cascade just needs
    -- non-overlapping regions).
    match lastIdx? with
    | none => layoutForEncoding e
    | some lastIdx =>
      if !canExtendLastPtLoad e startOffset startPage alignStartPage lastIdx then
        -- Can't safely extend (huge BSS or wrong alignment).  Bail to a
        -- non-PT_LOAD-aware layout — produces non-loadable bytes that
        -- the validator will reject.
        layoutForEncoding e
      else
        -- Identify stale sections.
        let stale : Array Bool := Array.ofFn (n := e.sections.size) fun i =>
          sectionStale e i.val i.isLt
        -- Place sections (stale ones at startOffset + cumOff, non-stale at original).
        let placed := appendStaleSections e.sections stale startOffset startPage
        let newSections := placed.1
        let appendedBytes := placed.2
        -- Place shdr table just after the appended region (8-byte aligned).
        let newShoff := roundUp (startOffset + appendedBytes) 8
        -- Compute new last-PT_LOAD filesz / memsz.
        -- filesz spans `[p_offset, startOffset + appendedBytes)`.
        -- memsz spans `[p_vaddr, startPage + appendedBytes)`.
        let newLastFilesz : Nat :=
          if h : lastIdx < e.phdrs.size then
            let ph := e.phdrs[lastIdx]'h
            (startOffset + appendedBytes) - ph.offset.val
          else 0
        let newLastMemsz : Nat :=
          if h : lastIdx < e.phdrs.size then
            let ph := e.phdrs[lastIdx]'h
            (startPage + appendedBytes) - ph.vaddr.val
          else 0
        let newPhdrs := updatePhdrsAfterMove e.phdrs (some lastIdx)
                        newLastFilesz newLastMemsz
                        e.interpIdx e.dynamicIdx newSections
        let newHeader : Patchelf.Elf.ElfHeader :=
          { e.header with shoff := ⟨newShoff⟩ }
        { header := newHeader, phdrs := newPhdrs, sections := newSections }

/-- `growEOF` with auto-detected page size (no override).  Equivalent
    to `growEOFWith none`. -/
def growEOF (e : ElfFile) : ElfFile := growEOFWith none e

/-! ## DT_* address-tag synchronization

    When sections move (typical after `growEOF`), the `.dynamic` table's
    `DT_STRTAB`, `DT_SYMTAB`, `DT_HASH`, `DT_GNU_HASH`, `DT_VERNEED`,
    `DT_VERSYM`, `DT_JMPREL`, `DT_REL`, `DT_RELA` tags must be rewritten
    to point at the new section addresses.  This is the analogue of
    C++ `rewriteHeaders`'s DT_* update block (patchelf.cc:1244-1318).

    `Adapter.patchDynamicEntries` preserves these tags verbatim from the
    original byte-layer DT_* values; that's correct only when the
    target section didn't move.  This pass corrects the post-move
    case. -/

/-- Look up the `addr` of the section at index `i?`, or `none` if no
    such section. -/
def sectionAddr? (e : ElfFile) (i? : Option Nat) : Option Nat :=
  i?.bind fun i =>
    if h : i < e.sections.size then some (e.sections[i]'h).addr.val else none

/-- Find a section index by name (used for DT_JMPREL → .rela.plt /
    .rel.plt / .rela.IA_64.pltoff lookup; DT_REL → .rel.dyn / .rel.got;
    DT_RELA → .rela.dyn). -/
def findSectionByName (e : ElfFile) (nm : String) : Option Nat :=
  e.findIdxByName nm.toUTF8

/-- Compute the new address-tag value for a DT_* entry, given the
    current section table.  Returns `none` if the section the tag
    points at doesn't exist (in which case we leave the entry alone). -/
def addrTagTarget (e : ElfFile) (tag : DynTag) : Option Nat :=
  match tag with
  | DynTag.strtab  => sectionAddr? e e.dynstrIdx
  | DynTag.symtab  => sectionAddr? e e.dynsymIdx
  | DynTag.hash    => sectionAddr? e e.sysvHashIdx
  | DynTag.gnuHash => sectionAddr? e e.gnuHashIdx
  | DynTag.verneed => sectionAddr? e e.verneedIdx
  | DynTag.versym  => sectionAddr? e e.versymIdx
  -- DT_JMPREL / DT_REL / DT_RELA: lookup by name (multiple candidate sections).
  | DynTag.jmprel =>
      match findSectionByName e ".rela.plt" with
      | some i => sectionAddr? e (some i)
      | none =>
        match findSectionByName e ".rel.plt" with
        | some i => sectionAddr? e (some i)
        | none   => none
  | DynTag.rel =>
      match findSectionByName e ".rel.dyn" with
      | some i => sectionAddr? e (some i)
      | none =>
        match findSectionByName e ".rel.got" with
        | some i => sectionAddr? e (some i)
        | none   => none
  | DynTag.rela =>
      match findSectionByName e ".rela.dyn" with
      | some i => sectionAddr? e (some i)
      | none   => none
  | _ => none

/-- Rewrite a single dynamic entry's `value` if its tag is an address tag
    and we know the target section's new address. -/
def syncDtAddrEntry (e : ElfFile) (d : DynEntry) : DynEntry :=
  if d.tag.isAddressTag then
    match addrTagTarget e d.tag with
    | some a => { d with value := a.toUInt64 }
    | none   => d
  else d

/-- Apply `syncDtAddrEntry` across all `.dynamic` entries.  No-op if
    the file has no `.dynamic` section. -/
def syncDtAddrTagsInFile (e : ElfFile) : ElfFile :=
  match e.dynamicIdx, e.dynamic with
  | some iDyn, some dyn =>
      if h : iDyn < e.sections.size then
        let newDyn := dyn.map (syncDtAddrEntry e)
        e.updateSectionContent iDyn (.dynamic newDyn)
      else e
  | _, _ => e

end Patchelf.Elf
