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

/-! ## `currentFileEnd` structural lemmas

    `currentFileEnd e` upper-bounds every non-NULL/NOBITS section's file
    range, plus the ehdr / phdr / shdr table ends.  These bounds feed
    the `growEOFWith` `VerbatimWitness` proof: a non-stale section's
    range falls under `currentFileEnd ≤ startOffset`, which is exactly
    the third disjunct of `PlaceFold.VerbatimWitness.bound`. -/

theorem currentFileEnd_ge_ehdr (e : ElfFile) :
    Layout.ehdrSize ≤ currentFileEnd e := by
  unfold currentFileEnd
  exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)

theorem currentFileEnd_ge_phdrEnd (e : ElfFile) :
    e.header.phoff.val + e.phdrs.size * Layout.phdrSize ≤ currentFileEnd e := by
  unfold currentFileEnd
  exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)

theorem currentFileEnd_ge_shdrEnd (e : ElfFile) :
    e.header.shoff.val + e.sections.size * Layout.shdrSize ≤ currentFileEnd e := by
  unfold currentFileEnd
  exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

/-- For any non-NOBITS, non-NULL section, the section's file range
    `[offset, offset + encodedSize)` ends at or before `currentFileEnd`.

    Foldl induction on the `secEnd` accumulator: at each step the
    accumulator is the running max, and each new section either
    contributes its file range or skips (NOBITS/NULL). -/
theorem currentFileEnd_ge_section_end (e : ElfFile) (j : Nat) (hj : j < e.sections.size) :
    (e.sections[j]'hj).type = ShType.SHT_NOBITS ∨
    (e.sections[j]'hj).type = ShType.SHT_NULL ∨
    (e.sections[j]'hj).offset.val + (e.sections[j]'hj).encodedSize ≤ currentFileEnd e := by
  -- Foldl-induction motive: every j' < k satisfies the disjunction relative
  -- to the running secEnd accumulator.
  have hAux := @Array.foldl_induction Section Nat e.sections
    (motive := fun k acc =>
      ∀ j' (hj' : j' < e.sections.size), j' < k →
        (e.sections[j']'hj').type = ShType.SHT_NOBITS ∨
        (e.sections[j']'hj').type = ShType.SHT_NULL ∨
        (e.sections[j']'hj').offset.val + (e.sections[j']'hj').encodedSize ≤ acc)
    (init := 0)
    (h0 := by intros j' _ hjLt; exact absurd hjLt (Nat.not_lt_zero _))
    (f := fun acc s =>
      if s.type = ShType.SHT_NOBITS ∨ s.type = ShType.SHT_NULL then acc
      else max acc (s.offset.val + s.encodedSize))
    (hf := by
      intros i acc ih j' hj' hjLtSucc
      by_cases hjLtI : j' < i.val
      · -- Old j': use ih, then monotonicity through the step.
        rcases ih j' hj' hjLtI with hN | hNB | hLe
        · exact Or.inl hN
        · exact Or.inr (Or.inl hNB)
        · refine Or.inr (Or.inr ?_)
          by_cases hAlt : (e.sections[i.val]'i.isLt).type = ShType.SHT_NOBITS ∨
                          (e.sections[i.val]'i.isLt).type = ShType.SHT_NULL
          · simp [hAlt]; exact hLe
          · simp [hAlt]; exact Nat.le_trans hLe (Nat.le_max_left _ _)
      · -- New j' = i.val.
        have hjEq : j' = i.val := by omega
        subst hjEq
        by_cases hAlt : (e.sections[i.val]'hj').type = ShType.SHT_NOBITS ∨
                        (e.sections[i.val]'hj').type = ShType.SHT_NULL
        · rcases hAlt with hNB | hN
          · exact Or.inl hNB
          · exact Or.inr (Or.inl hN)
        · simp [hAlt]
          refine Or.inr (Or.inr ?_)
          exact Nat.le_max_right _ _)
  -- Apply at j = j, hj = hj, and j < e.sections.size.
  rcases hAux j hj hj with hN | hNB | hLe
  · exact Or.inl hN
  · exact Or.inr (Or.inl hNB)
  · refine Or.inr (Or.inr ?_)
    unfold currentFileEnd
    show _ ≤ max (max _ _) (max _ _)
    exact Nat.le_trans hLe (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))

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
    acc || (if j = i then false
            else rangeOverlapsSection s.offset.val sEnd (e.sections[j]'hj))

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
    (mod align)` is preserved.

    Implemented as a specialization of `PlaceFold.placeStep` /
    `PlaceFold.placeFold` (defined in `LayoutEngine.lean`), with
    verbatim = `¬ stale[i]` and transform shifting `offset` by
    `startOffset` and `addr` by `startPage`.  This lets us reuse the
    `Placement` / `PairDisjoint` / `placeFold_inv` machinery. -/

/-- Verbatim predicate for `growEOFWith`'s placement: an entry passes
    through unchanged when its index is not in the `stale` array. -/
def appendVerbatim (stale : Array Bool) (i : Nat) (_s : Section) : Bool :=
  !(stale[i]?.getD false)

/-- Per-section transform for `growEOFWith`: shifts `offset` by
    `startOffset` and `addr` by `startPage` (so the offset/addr delta
    is constant — preserving `p_offset ≡ p_vaddr (mod align)`). -/
def appendTransform (startOffset startPage : Nat) (s : Section) (off : Nat) : Section :=
  { s with offset := ⟨startOffset + off⟩, addr := ⟨startPage + off⟩ }

/-- Stale-aware section placement.  Walks `sections`, threading
    `(acc, cursor)`; non-stale sections are kept at their original
    offset, stale sections are placed in the appended region. -/
def appendStaleSections (sections : Array Section) (stale : Array Bool)
    (startOffset startPage : Nat) : Array Section × Nat :=
  placeFold (appendVerbatim stale) (appendTransform startOffset startPage)
    sections 0

/-- `appendTransform startOffset startPage` is a `TransformSpec` with
    `baseOffset = startOffset`. -/
theorem appendTransform_transformSpec (startOffset startPage : Nat) :
    PlaceFold.TransformSpec (appendTransform startOffset startPage) startOffset :=
  { type_eq := fun s o => by show ({s with offset := _, addr := _ }).type = s.type; rfl
    encodedSize_eq := fun s o => by
      unfold appendTransform Section.encodedSize; rfl
    offset_eq := fun s o => by
      show (appendTransform startOffset startPage s o).offset.val = startOffset + o
      rfl }

/-! ## Stale ⇒ disjointness extraction

    Two structural facts on `sectionStale = false`:

    * Non-stale, non-NULL/NOBITS sections have file ranges disjoint from
      the shdr table.
    * Non-stale section `i`'s file range is disjoint from every other
      section's file range (or the other section is NULL/NOBITS).

    Both fall out of unfolding `sectionStale`. -/

/-- Unfolding helper: when `rangeOverlapsSection lo hi s = false`, either
    `s.type = NULL`, `s.type = NOBITS`, or the byte ranges are disjoint. -/
theorem rangeOverlapsSection_false_disjoint
    (lo hi : Nat) (s : Section) (h : rangeOverlapsSection lo hi s = false) :
    s.type = ShType.SHT_NULL ∨ s.type = ShType.SHT_NOBITS ∨
    IntervalDisjoint lo hi s.offset.val (s.offset.val + s.encodedSize) := by
  unfold rangeOverlapsSection at h
  by_cases hAlt : s.type = ShType.SHT_NOBITS ∨ s.type = ShType.SHT_NULL
  · rcases hAlt with hNB | hN
    · exact Or.inr (Or.inl hNB)
    · exact Or.inl hN
  · simp only [hAlt, ↓reduceIte] at h
    -- h : !decide (hi ≤ s.offset.val ∨ s.offset.val + s.encodedSize ≤ lo) = false
    refine Or.inr (Or.inr ?_)
    show IntervalDisjoint lo hi s.offset.val (s.offset.val + s.encodedSize)
    unfold IntervalDisjoint
    -- `!x = false ↔ x = true`; then `decide P = true ↔ P`.
    have h' : decide (hi ≤ s.offset.val ∨ s.offset.val + s.encodedSize ≤ lo) = true := by
      cases hd : decide (hi ≤ s.offset.val ∨ s.offset.val + s.encodedSize ≤ lo)
      · rw [hd] at h; simp at h
      · rfl
    exact decide_eq_true_iff.mp h'

/-- Helper: `Nat.fold` of a `||`-step is monotone — once true, the
    accumulator stays true.  Equivalently: if the final fold is false,
    then every iteration's "contribution" `g i hi` was false. -/
theorem nat_fold_or_false_iff
    (n : Nat) (g : (i : Nat) → i < n → Bool) :
    Nat.fold n (init := false)
      (fun i hi acc => acc || g i hi) = false ↔
    ∀ (i : Nat) (hi : i < n), g i hi = false := by
  induction n with
  | zero =>
    rw [Nat.fold_zero]
    constructor
    · intros _ i hi; exact absurd hi (Nat.not_lt_zero _)
    · intros _; rfl
  | succ k ih =>
    rw [Nat.fold_succ]
    -- Goal: (g k _ || (Nat.fold k ... false)) = false ↔ ∀ i < k+1, g i _ = false.
    -- Note: order of `||` is `acc || g`; `Nat.fold_succ` puts the new step
    -- on the outside.  Here it's `f k hk inner = inner || g k hk`.
    -- Wait, `f i hi acc = acc || g i hi`, so `f k hk inner = inner || g k hk`.
    show (Nat.fold k _ false || g k (Nat.lt_succ_self _)) = false ↔ _
    rw [Bool.or_eq_false_iff]
    constructor
    · rintro ⟨hInner, hG⟩
      intros i hi
      by_cases hiK : i < k
      · -- Sub-fold's contribution: use ih.
        have ihLeft := (ih (fun i hi => g i (Nat.lt_succ_of_lt hi))).mp hInner
        exact ihLeft i hiK
      · have hiEq : i = k := by omega
        subst hiEq
        exact hG
    · intros hAll
      refine ⟨?_, hAll k (Nat.lt_succ_self _)⟩
      apply (ih (fun i hi => g i (Nat.lt_succ_of_lt hi))).mpr
      intros i hi
      exact hAll i (Nat.lt_succ_of_lt hi)

/-- When `sectionOverlapsAny e i h = false`, every other section
    has a disjointness witness with section `i`. -/
theorem sectionOverlapsAny_false_pair_disjoint (e : ElfFile)
    (i : Nat) (hi : i < e.sections.size)
    (hOA : sectionOverlapsAny e i hi = false)
    (j : Nat) (hj : j < e.sections.size) (hNe : j ≠ i) :
    (e.sections[j]'hj).type = ShType.SHT_NULL ∨
    (e.sections[j]'hj).type = ShType.SHT_NOBITS ∨
    IntervalDisjoint
      (e.sections[i]'hi).offset.val
      ((e.sections[i]'hi).offset.val + (e.sections[i]'hi).encodedSize)
      (e.sections[j]'hj).offset.val
      ((e.sections[j]'hj).offset.val + (e.sections[j]'hj).encodedSize) := by
  -- Reshape the fold to the `acc || g i hi` form so we can apply
  -- nat_fold_or_false_iff.  The original fold has `if jIdx = i then acc
  -- else acc || R`; this equals `acc || (if jIdx = i then false else R)`.
  let s := e.sections[i]'hi
  let sEnd := s.offset.val + s.encodedSize
  let g : (jIdx : Nat) → jIdx < e.sections.size → Bool := fun jIdx hjIdx =>
    if jIdx = i then false
    else rangeOverlapsSection s.offset.val sEnd (e.sections[jIdx]'hjIdx)
  have hReshape : sectionOverlapsAny e i hi =
      Nat.fold e.sections.size (init := false) (fun jIdx hjIdx acc => acc || g jIdx hjIdx) :=
    rfl
  rw [hReshape] at hOA
  have hPer := (nat_fold_or_false_iff e.sections.size g).mp hOA
  -- hPer: ∀ jIdx hjIdx, g jIdx hjIdx = false.
  -- For j ≠ i: g j hj = rangeOverlapsSection ... = false.
  have hRange : rangeOverlapsSection s.offset.val sEnd (e.sections[j]'hj) = false := by
    have := hPer j hj
    simp [g, hNe] at this
    exact this
  exact rangeOverlapsSection_false_disjoint _ _ _ hRange

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
      if _h : iDyn < e.sections.size then
        let newDyn := dyn.map (syncDtAddrEntry e)
        e.updateSectionContent iDyn (.dynamic newDyn)
      else e
  | _, _ => e

/-! ## `syncDtAddrTagsInFile` field preservation

    `syncDtAddrTagsInFile` either returns `e` unchanged or replaces
    `e.sections[iDyn]`'s content with a `.dynamic`-mapped version.  In
    both cases, all fields except section content at index `iDyn` are
    preserved; `Array.map` preserves array `.size`, so even the
    modified section's `encodedSize` is unchanged.

    Strategy: case-split on whether `syncDtAddrTagsInFile e = e` (the
    "no-op" case — covers `e.dynamic = none`, `e.dynamicIdx = none`,
    or the bounds-check failure) or
    `e.updateSectionContent iDyn (.dynamic (dyn.map _))` (the active
    case — derive content equality from the active branch). -/

theorem syncDtAddrTagsInFile_cases (e : ElfFile) :
    syncDtAddrTagsInFile e = e ∨
    ∃ (iDyn : Nat) (h : iDyn < e.sections.size) (dyn : Array DynEntry),
      (e.sections[iDyn]'h).content = .dynamic dyn ∧
      syncDtAddrTagsInFile e =
        e.updateSectionContent iDyn (.dynamic (dyn.map (syncDtAddrEntry e))) := by
  unfold syncDtAddrTagsInFile
  cases hI : e.dynamicIdx with
  | none =>
    -- The match on (none, _) returns e.
    cases e.dynamic <;> exact Or.inl rfl
  | some iDyn =>
    cases hD : e.dynamic with
    | none => exact Or.inl rfl
    | some dyn =>
      by_cases hLt : iDyn < e.sections.size
      · refine Or.inr ⟨iDyn, hLt, dyn, ?_, ?_⟩
        · -- e.dynamic = some dyn ⇒ e.sections[iDyn].content = .dynamic dyn.
          unfold ElfFile.dynamic at hD
          rw [hI] at hD
          unfold ElfFile.contentAt at hD
          simp only [Option.bind_some] at hD
          rw [dif_pos hLt] at hD
          generalize hC : (e.sections[iDyn]'hLt).content = c at hD
          cases c with
          | dynamic dyn' => simp at hD; rw [hD]
          | raw _ => simp at hD
          | strtab _ => simp at hD
          | dynsym _ => simp at hD
          | versym _ => simp at hD
          | nobits _ => simp at hD
        · -- After cases, the goal is `match some iDyn, some dyn with ... = ...`.
          simp only [dif_pos hLt]
      · refine Or.inl ?_; simp only [dif_neg hLt]

@[simp] theorem syncDtAddrTagsInFile_header (e : ElfFile) :
    (syncDtAddrTagsInFile e).header = e.header := by
  rcases syncDtAddrTagsInFile_cases e with hEq | ⟨iDyn, hLt, dyn, hContent, hEq⟩
  · rw [hEq]
  · rw [hEq]; simp

@[simp] theorem syncDtAddrTagsInFile_phdrs (e : ElfFile) :
    (syncDtAddrTagsInFile e).phdrs = e.phdrs := by
  rcases syncDtAddrTagsInFile_cases e with hEq | ⟨iDyn, hLt, dyn, hContent, hEq⟩
  · rw [hEq]
  · rw [hEq]; simp

@[simp] theorem syncDtAddrTagsInFile_sections_size (e : ElfFile) :
    (syncDtAddrTagsInFile e).sections.size = e.sections.size := by
  rcases syncDtAddrTagsInFile_cases e with hEq | ⟨iDyn, hLt, dyn, hContent, hEq⟩
  · rw [hEq]
  · rw [hEq]; simp

/-- Field preservation under `e.updateSectionContent iDyn (.dynamic _)`
    when the original section had `.dynamic dyn` content with same size:
    `encodedSize` is preserved at every index. -/
theorem updateSectionContent_dynamic_map_encodedSize_eq
    (e : ElfFile) (iDyn : Nat) (hLt : iDyn < e.sections.size)
    (dyn : Array DynEntry)
    (hContent : (e.sections[iDyn]'hLt).content = .dynamic dyn)
    (f : DynEntry → DynEntry)
    (j : Nat) (hj : j < e.sections.size)
    (hj' : j < (e.updateSectionContent iDyn (.dynamic (dyn.map f))).sections.size) :
    ((e.updateSectionContent iDyn (.dynamic (dyn.map f))).sections[j]'hj').encodedSize
      = (e.sections[j]'hj).encodedSize := by
  by_cases hje : j = iDyn
  · subst hje
    rw [ElfFile.updateSectionContent_getElem_self e j _ hLt hj']
    unfold Section.encodedSize
    rw [hContent]
    simp [Array.size_map]
  · rw [ElfFile.updateSectionContent_getElem_ne _ _ _ _ hj hje hj']

/-! ## `syncDtAddrTagsInFile` preserves `spliceRegionsDisjoint`

    `syncDtAddrTagsInFile` either is a no-op (returning `e` unchanged) or
    applies `updateSectionContent` at the `.dynamic` section's index with
    a same-size content.  All 7 `spliceRegionsDisjoint` clauses depend
    only on `header.{phoff, shoff}`, `phdrs.size`, `sections.size`, and
    per-section `(type, offset, encodedSize)`.  The first three are
    preserved by `updateSectionContent`; per-section fields are preserved
    everywhere except possibly the modified index, where `(type, offset)`
    are preserved by the `{ s with content := ... }` pattern and
    `encodedSize` is preserved by `Array.size_map`. -/
theorem syncDtAddrTagsInFile_preserves_spliceRegionsDisjoint
    (e : ElfFile) (h : e.spliceRegionsDisjoint) :
    (syncDtAddrTagsInFile e).spliceRegionsDisjoint := by
  rcases syncDtAddrTagsInFile_cases e with hEq | ⟨iDyn, hLt, dyn, hContent, hEq⟩
  · -- No-op case: result is e, inherit invariants directly.
    rw [hEq]; exact h
  · -- Active case: result = e.updateSectionContent iDyn (.dynamic (dyn.map _)).
    rw [hEq]
    -- Local abbreviations for readability.
    let e' := e.updateSectionContent iDyn (.dynamic (dyn.map (syncDtAddrEntry e)))
    show e'.spliceRegionsDisjoint
    have hSizeEq : e'.sections.size = e.sections.size :=
      ElfFile.updateSectionContent_sections_size _ _ _
    have hHdrEq : e'.header = e.header :=
      ElfFile.updateSectionContent_header _ _ _
    have hPhdrsEq : e'.phdrs = e.phdrs :=
      ElfFile.updateSectionContent_phdrs _ _ _
    have hPhoffEq : e'.header.phoff = e.header.phoff := by rw [hHdrEq]
    have hShoffEq : e'.header.shoff = e.header.shoff := by rw [hHdrEq]
    have hPhdrSizeEq : e'.phdrs.size = e.phdrs.size := by rw [hPhdrsEq]
    -- Per-section: type, offset, encodedSize preserved at every j.
    -- At j = iDyn: original had .dynamic dyn (type SHT_DYNAMIC); update also
    -- .dynamic (dyn.map f) (type SHT_DYNAMIC). Type unchanged.
    -- At j ≠ iDyn: content unchanged, type unchanged.
    have hType : ∀ (j : Nat) (hj : j < e.sections.size)
        (hj' : j < e'.sections.size),
        (e'.sections[j]'hj').type = (e.sections[j]'hj).type := by
      intros j hj hj'
      by_cases hji : j = iDyn
      · subst hji
        rw [ElfFile.updateSectionContent_type_self _ _ _ hj hj']
        -- c = .dynamic (dyn.map f) → c.type = SHT_DYNAMIC
        -- original = .dynamic dyn → original.type = SHT_DYNAMIC
        simp only [SectionContent.type, Section.type, hContent]
      · exact ElfFile.updateSectionContent_type _ _ _ _ hj hji hj'
    have hOffset : ∀ (j : Nat) (hj : j < e.sections.size)
        (hj' : j < e'.sections.size),
        (e'.sections[j]'hj').offset = (e.sections[j]'hj).offset := by
      intros j hj hj'
      exact ElfFile.updateSectionContent_offset _ _ _ _ hj hj'
    have hSize : ∀ (j : Nat) (hj : j < e.sections.size)
        (hj' : j < e'.sections.size),
        (e'.sections[j]'hj').encodedSize = (e.sections[j]'hj).encodedSize := by
      intros j hj hj'
      exact updateSectionContent_dynamic_map_encodedSize_eq e iDyn hLt dyn hContent _ j hj hj'
    -- Build the 7 clauses.
    refine
      { sections_disjoint := ?_
        hdr_phdr_disjoint := ?_
        hdr_shdr_disjoint := ?_
        phdr_shdr_disjoint := ?_
        hdr_sec_disjoint := ?_
        phdr_sec_disjoint := ?_
        shdr_sec_disjoint := ?_ }
    · -- sections_disjoint
      intros j hj j' hj' hNe
      have hjE : j < e.sections.size := hSizeEq ▸ hj
      have hj'E : j' < e.sections.size := hSizeEq ▸ hj'
      have hSectionsOrig := h.sections_disjoint j hjE j' hj'E hNe
      show (e'.sections[j]'hj).type = _ ∨ (e'.sections[j']'hj').type = _ ∨
           (e'.sections[j]'hj).type = _ ∨ (e'.sections[j']'hj').type = _ ∨
           IntervalDisjoint _ _ _ _
      rw [hType _ hjE hj, hType _ hj'E hj', hOffset _ hjE hj, hOffset _ hj'E hj',
          hSize _ hjE hj, hSize _ hj'E hj']
      exact hSectionsOrig
    · -- hdr_phdr_disjoint
      show IntervalDisjoint 0 _ e'.header.phoff.val (_ + e'.phdrs.size * _)
      rw [hPhoffEq, hPhdrSizeEq]
      exact h.hdr_phdr_disjoint
    · -- hdr_shdr_disjoint
      show IntervalDisjoint 0 _ e'.header.shoff.val (_ + e'.sections.size * _)
      rw [hShoffEq, hSizeEq]
      exact h.hdr_shdr_disjoint
    · -- phdr_shdr_disjoint
      show IntervalDisjoint e'.header.phoff.val (_ + e'.phdrs.size * _) e'.header.shoff.val (_ + e'.sections.size * _)
      rw [hPhoffEq, hShoffEq, hPhdrSizeEq, hSizeEq]
      exact h.phdr_shdr_disjoint
    · -- hdr_sec_disjoint
      intros j hj
      have hjE : j < e.sections.size := hSizeEq ▸ hj
      have hOrig := h.hdr_sec_disjoint j hjE
      show (e'.sections[j]'hj).type = _ ∨ (e'.sections[j]'hj).type = _ ∨
           IntervalDisjoint _ _ _ _
      rw [hType _ hjE hj, hOffset _ hjE hj, hSize _ hjE hj]
      exact hOrig
    · -- phdr_sec_disjoint
      intros j hj
      have hjE : j < e.sections.size := hSizeEq ▸ hj
      have hOrig := h.phdr_sec_disjoint j hjE
      show ((e'.sections[j]'hj).type = _ ∨ _)
      rw [hPhoffEq, hPhdrSizeEq]
      rw [hType _ hjE hj, hOffset _ hjE hj, hSize _ hjE hj]
      exact hOrig
    · -- shdr_sec_disjoint
      intros j hj
      have hjE : j < e.sections.size := hSizeEq ▸ hj
      have hOrig := h.shdr_sec_disjoint j hjE
      show ((e'.sections[j]'hj).type = _ ∨ _)
      rw [hShoffEq, hSizeEq]
      rw [hType _ hjE hj, hOffset _ hjE hj, hSize _ hjE hj]
      exact hOrig

/-! ## `growEOFWith` produces `spliceRegionsDisjoint` -/

/-- Sanity lemma: the `stale` array built inside `growEOFWith` indexes
    correctly to `sectionStale e i hi` for every valid `i`.  Used by the
    `appendVerbatim_witness` invocation in the main theorem. -/
theorem stale_ofFn_eq_sectionStale (e : ElfFile) (i : Nat) (hi : i < e.sections.size) :
    (Array.ofFn (n := e.sections.size) (fun (i : Fin e.sections.size) =>
        sectionStale e i.val i.isLt))[i]?.getD false = sectionStale e i hi := by
  have hLt : i < (Array.ofFn (n := e.sections.size) (fun (i : Fin e.sections.size) =>
      sectionStale e i.val i.isLt)).size := by
    rw [Array.size_ofFn]; exact hi
  rw [Array.getElem?_eq_getElem hLt]
  simp only [Option.getD_some]
  rw [Array.getElem_ofFn]

theorem stale_ofFn_size (e : ElfFile) :
    (Array.ofFn (n := e.sections.size) (fun (i : Fin e.sections.size) =>
        sectionStale e i.val i.isLt)).size = e.sections.size := Array.size_ofFn

/-- Verbatim-witness for `growEOFWith`'s placement at `baseOffset = startOffset`.

    The two fields fall out directly from `sectionStale = false`:

    * `bound`: a non-stale section is either NULL/NOBITS, or its file
      range ≤ `currentFileEnd e ≤ startOffset` (provided we know
      `currentFileEnd e ≤ startOffset`, which holds when `startOffset =
      roundUp (currentFileEnd e) align`).
    * `pair_disj`: two non-stale sections are pairwise disjoint by
      `sectionOverlapsAny_false_pair_disjoint`.

    The hypothesis `hStartOffset` captures the file-end alignment relation. -/
theorem appendVerbatim_witness (e : ElfFile)
    (startOffset : Nat)
    (hStartOffset : currentFileEnd e ≤ startOffset)
    (stale : Array Bool)
    (hStaleEq : ∀ (i : Nat) (hi : i < e.sections.size),
      stale[i]?.getD false = sectionStale e i hi) :
    PlaceFold.VerbatimWitness (appendVerbatim stale) startOffset e.sections := by
  refine ⟨?_, ?_⟩
  · -- bound: verbatim entry ⇒ NULL ∨ NOBITS ∨ file-range ≤ startOffset.
    intros j hjS hVerb
    -- hVerb : appendVerbatim stale j (e.sections[j]) = true
    --       = !(stale[j]?.getD false) = true ⇔ stale[j]?.getD false = false
    have hStaleFalse : stale[j]?.getD false = false := by
      unfold appendVerbatim at hVerb
      cases h : stale[j]?.getD false
      · rfl
      · rw [h] at hVerb; simp at hVerb
    -- By hStaleEq, sectionStale e j hjS = false.
    have hStaleE : sectionStale e j hjS = false := by
      rw [← hStaleEq j hjS]; exact hStaleFalse
    -- sectionStale = false: section is NULL/NOBITS, or its range doesn't
    -- overlap shdr table or any other section.  We extract NULL/NOBITS
    -- from the if-branch, and the file-range bound from currentFileEnd.
    rcases currentFileEnd_ge_section_end e j hjS with hNB | hN | hLe
    · exact Or.inr (Or.inl hNB)
    · exact Or.inl hN
    · exact Or.inr (Or.inr (Nat.le_trans hLe hStartOffset))
  · -- pair_disj: two non-stale entries are pairwise disjoint.
    intros j j' hj hj' hNe hVerbJ hVerbJ'
    -- Get sectionStale e j hj = false from hVerbJ.
    have hStaleJ : sectionStale e j hj = false := by
      have : stale[j]?.getD false = false := by
        unfold appendVerbatim at hVerbJ
        cases h : stale[j]?.getD false
        · rfl
        · rw [h] at hVerbJ; simp at hVerbJ
      rw [← hStaleEq j hj]; exact this
    -- Unfold sectionStale to get sectionOverlapsAny e j hj = false (when
    -- not NULL/NOBITS).
    unfold sectionStale at hStaleJ
    by_cases hAlt : (e.sections[j]'hj).type = ShType.SHT_NOBITS ∨
                    (e.sections[j]'hj).type = ShType.SHT_NULL
    · -- j is NULL or NOBITS: short-circuit pair_disj.
      rcases hAlt with hNB | hN
      · exact Or.inl hNB
      · exact Or.inr (Or.inr (Or.inl hN))
    · simp only [hAlt, ↓reduceIte] at hStaleJ
      -- hStaleJ : (overlapShdr || sectionOverlapsAny ...) = false
      -- The right disjunct gives us sectionOverlapsAny = false.
      have hOA : sectionOverlapsAny e j hj = false := by
        rcases Bool.or_eq_false_iff.mp hStaleJ with ⟨_, h⟩
        exact h
      -- Apply sectionOverlapsAny_false_pair_disjoint at j' ≠ j.
      rcases sectionOverlapsAny_false_pair_disjoint e j hj hOA j' hj' hNe.symm with h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inl h)
      · -- IntervalDisjoint with arguments in (j, j') order.
        refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
        -- h : IntervalDisjoint sj.range sj'.range — same as goal.
        exact h

/-- `growEOFWith` main-body construction: explicitly named so we can prove
    its splice-disjointness independently of the surrounding branches.
    Equals the body of `growEOFWith` when the main path is taken (i.e.,
    when `layoutAlreadyValid e = false`, `lastPtLoadIdx e.phdrs = some
    lastIdx`, and `canExtendLastPtLoad ... = true`). -/
def growEOFWithMainBody (pageSize? : Option Nat) (e : ElfFile) (lastIdx : Nat) : ElfFile :=
  let detectedAlign := maxPtLoadAlign e.phdrs
  let alignStartPage :=
    match pageSize? with
    | some n => max n detectedAlign
    | none   => detectedAlign
  let startPage := roundUp (maxPtLoadVaddrEnd e.phdrs) alignStartPage
  let startOffset := roundUp (currentFileEnd e) alignStartPage
  let stale : Array Bool := Array.ofFn (n := e.sections.size) fun i =>
    sectionStale e i.val i.isLt
  let placed := appendStaleSections e.sections stale startOffset startPage
  let newSections := placed.1
  let appendedBytes := placed.2
  let newShoff := roundUp (startOffset + appendedBytes) 8
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

/-- The main-body construction satisfies `spliceRegionsDisjoint` provided
    the input file's header / phdr-table / per-section disjointness
    invariants hold.  Shdr-table preconditions aren't needed because the
    output's `shoff` is freshly computed (and bounded by `currentFileEnd`
    via `roundUp`); `hSection0Null` isn't needed because non-stale
    sections inherit NULL/NOBITS from the file-range bound through
    `currentFileEnd_ge_section_end`. -/
theorem growEOFWithMainBody_produces_spliceRegionsDisjoint
    (pageSize? : Option Nat) (e : ElfFile) (lastIdx : Nat)
    (hHeaderPhdr : e.headerPhdrDisjoint)
    (hHeaderSec  : e.headerSectionDisjoint)
    (hPhdrSec    : e.phdrSectionDisjoint) :
    (growEOFWithMainBody pageSize? e lastIdx).spliceRegionsDisjoint := by
  unfold growEOFWithMainBody
  let detectedAlign := maxPtLoadAlign e.phdrs
  let alignStartPage :=
    match pageSize? with
    | some n => max n detectedAlign
    | none   => detectedAlign
  let startPage := roundUp (maxPtLoadVaddrEnd e.phdrs) alignStartPage
  let startOffset := roundUp (currentFileEnd e) alignStartPage
  let stale : Array Bool := Array.ofFn (n := e.sections.size) fun i =>
    sectionStale e i.val i.isLt
  let placed := appendStaleSections e.sections stale startOffset startPage
  let newSections := placed.1
  let appendedBytes := placed.2
  let newShoff := roundUp (startOffset + appendedBytes) 8
  -- Witnesses.
  have hSpec : PlaceFold.TransformSpec (appendTransform startOffset startPage) startOffset :=
    appendTransform_transformSpec _ _
  have hCurrLeStart : currentFileEnd e ≤ startOffset := le_roundUp _ _
  have hStaleEq : ∀ (i : Nat) (hi : i < e.sections.size),
      stale[i]?.getD false = sectionStale e i hi :=
    fun i hi => stale_ofFn_eq_sectionStale e i hi
  have hVerb : PlaceFold.VerbatimWitness (appendVerbatim stale) startOffset e.sections :=
    appendVerbatim_witness e startOffset hCurrLeStart stale hStaleEq
  -- placeFold output facts.
  have hSizeEq : newSections.size = e.sections.size :=
    PlaceFold.size_eq _ _
  have hCursorFloor : (0 : Nat) ≤ appendedBytes := PlaceFold.cursor_floor _ _
  -- newShoff bounds.
  have hStartLeShoff : startOffset ≤ newShoff :=
    Nat.le_trans (Nat.le_add_right _ _) (le_roundUp _ _)
  have hEndLeShoff : startOffset + appendedBytes ≤ newShoff := le_roundUp _ _
  -- currentFileEnd bounds.
  have hEhdrLe : Layout.ehdrSize ≤ startOffset :=
    Nat.le_trans (currentFileEnd_ge_ehdr e) hCurrLeStart
  have hPhEndLe : e.header.phoff.val + e.phdrs.size * Layout.phdrSize ≤ startOffset :=
    Nat.le_trans (currentFileEnd_ge_phdrEnd e) hCurrLeStart
  -- per-entry placement.
  have hPlacement : ∀ (j : Nat) (hj : j < newSections.size),
      PlaceFold.Placement (appendVerbatim stale) startOffset e.sections 0 placed j := by
    intros j hj
    have hjS : j < e.sections.size := hSizeEq ▸ hj
    exact PlaceFold.placeFold_placement hSpec e.sections 0 hVerb j hjS
  -- pairwise non-overlap.
  have hPair : ∀ (j j' : Nat) (hj : j < newSections.size) (hj' : j' < newSections.size),
      j ≠ j' → PlaceFold.PairDisjoint placed j j' := by
    intros j j' hj hj' hNe
    have hjS : j < e.sections.size := hSizeEq ▸ hj
    have hj'S : j' < e.sections.size := hSizeEq ▸ hj'
    exact PlaceFold.placeFold_pairDisjoint hSpec e.sections 0 hVerb j j' hjS hj'S hNe
  -- The output's structural fields.
  -- (Note: the main-body's `phdrs` field is the result of `updatePhdrsAfterMove`,
  --  whose size equals `e.phdrs.size` via `Array.size_mapIdx`.)
  have hOutPhdrsSize : (updatePhdrsAfterMove e.phdrs (some lastIdx)
        ((if h : lastIdx < e.phdrs.size then
            (startOffset + appendedBytes) - (e.phdrs[lastIdx]'h).offset.val else 0))
        ((if h : lastIdx < e.phdrs.size then
            (startPage + appendedBytes) - (e.phdrs[lastIdx]'h).vaddr.val else 0))
        e.interpIdx e.dynamicIdx newSections).size = e.phdrs.size := by
    unfold updatePhdrsAfterMove
    exact Array.size_mapIdx
  -- For each verbatim entry: derive type-preservation and offset-preservation
  -- from the Placement; combined with input invariants, yields bounds.
  -- For each placed entry: hPlacement gives baseOffset + 0 ≤ offset ≤ baseOffset + placed.2,
  -- i.e. startOffset ≤ offset ≤ startOffset + appendedBytes.
  -- Build all 7 clauses.
  refine
    { sections_disjoint := ?_
      hdr_phdr_disjoint := ?_
      hdr_shdr_disjoint := ?_
      phdr_shdr_disjoint := ?_
      hdr_sec_disjoint := ?_
      phdr_sec_disjoint := ?_
      shdr_sec_disjoint := ?_ }
  · -- sections_disjoint: from hPair.
    intros j hj j' hj' hNe
    have hjN : j < newSections.size := hj
    have hj'N : j' < newSections.size := hj'
    exact hPair j j' hjN hj'N hNe hjN hj'N
  · -- hdr_phdr_disjoint: phoff and phdrs.size unchanged from input.
    show IntervalDisjoint 0 Layout.ehdrSize _ _
    -- Output's phoff = e.header.phoff (we don't change it); output's phdrs.size = e.phdrs.size.
    -- Reduce: (growEOFWithMainBody _).header.phoff = e.header.phoff (since we only set shoff).
    -- and updatePhdrsAfterMove preserves size.
    show IntervalDisjoint 0 Layout.ehdrSize e.header.phoff.val
      (e.header.phoff.val + _ * Layout.phdrSize)
    rw [hOutPhdrsSize]
    exact hHeaderPhdr
  · -- hdr_shdr_disjoint: newShoff ≥ Layout.ehdrSize (via currentFileEnd_ge_ehdr).
    show IntervalDisjoint 0 Layout.ehdrSize _ _
    refine Or.inl ?_
    show Layout.ehdrSize ≤ newShoff
    exact Nat.le_trans hEhdrLe hStartLeShoff
  · -- phdr_shdr_disjoint: newShoff ≥ phEnd.
    show IntervalDisjoint e.header.phoff.val _ _ _
    rw [hOutPhdrsSize]
    refine Or.inl ?_
    show e.header.phoff.val + e.phdrs.size * Layout.phdrSize ≤ newShoff
    exact Nat.le_trans hPhEndLe hStartLeShoff
  · -- hdr_sec_disjoint
    intros j hj
    have hjN : j < newSections.size := hj
    have hPl := hPlacement j hjN
    rcases hPl.offset_or with hVerbJ | hPlace
    · -- Verbatim: derive from input's hHeaderSec at e.sections[j].
      have hjS : j < e.sections.size := hSizeEq ▸ hjN
      rcases hHeaderSec j hjS with h | h | hID
      · -- e.sections[j] is NOBITS: state[j].type = NOBITS via hPl.type_eq.
        exact Or.inl (hPl.type_eq.trans h)
      · exact Or.inr (Or.inl (hPl.type_eq.trans h))
      · -- IntervalDisjoint 0 ehdrSize sj.range; state[j] preserves offset/encodedSize.
        refine Or.inr (Or.inr ?_)
        have hOffJ : (newSections[j]'hjN).offset.val = (e.sections[j]'hjS).offset.val := by
          rw [hVerbJ.2]
        have hSzJ : (newSections[j]'hjN).encodedSize = (e.sections[j]'hjS).encodedSize :=
          hPl.size_eq
        unfold IntervalDisjoint
        unfold IntervalDisjoint at hID
        rw [hOffJ, hSzJ]
        exact hID
    · -- Placed: state[j].offset ≥ baseOffset + 0 = startOffset ≥ ehdrSize.
      refine Or.inr (Or.inr (Or.inl ?_))
      show Layout.ehdrSize ≤ (newSections[j]'hjN).offset.val
      have : startOffset + 0 ≤ (newSections[j]'hjN).offset.val := hPlace.2.1
      omega
  · -- phdr_sec_disjoint
    intros j hj
    have hjN : j < newSections.size := hj
    have hPl := hPlacement j hjN
    show ((newSections[j]'hjN).type = _ ∨ _)
    rw [hOutPhdrsSize]
    rcases hPl.offset_or with hVerbJ | hPlace
    · have hjS : j < e.sections.size := hSizeEq ▸ hjN
      rcases hPhdrSec j hjS with h | h | hID
      · exact Or.inl (hPl.type_eq.trans h)
      · exact Or.inr (Or.inl (hPl.type_eq.trans h))
      · refine Or.inr (Or.inr ?_)
        have hOffJ : (newSections[j]'hjN).offset.val = (e.sections[j]'hjS).offset.val := by
          rw [hVerbJ.2]
        have hSzJ : (newSections[j]'hjN).encodedSize = (e.sections[j]'hjS).encodedSize :=
          hPl.size_eq
        unfold IntervalDisjoint
        unfold IntervalDisjoint at hID
        rw [hOffJ, hSzJ]
        exact hID
    · refine Or.inr (Or.inr (Or.inl ?_))
      show e.header.phoff.val + e.phdrs.size * Layout.phdrSize ≤ (newSections[j]'hjN).offset.val
      have : startOffset + 0 ≤ (newSections[j]'hjN).offset.val := hPlace.2.1
      omega
  · -- shdr_sec_disjoint
    intros j hj
    have hjN : j < newSections.size := hj
    have hPl := hPlacement j hjN
    rcases hPl.offset_or with hVerbJ | hPlace
    · -- Verbatim: section's range ≤ currentFileEnd ≤ startOffset ≤ newShoff.
      have hjS : j < e.sections.size := hSizeEq ▸ hjN
      rcases currentFileEnd_ge_section_end e j hjS with h | h | hLe
      · exact Or.inl (hPl.type_eq.trans h)
      · exact Or.inr (Or.inl (hPl.type_eq.trans h))
      · refine Or.inr (Or.inr (Or.inr ?_))
        show (newSections[j]'hjN).offset.val + (newSections[j]'hjN).encodedSize ≤ newShoff
        have hOffJ : (newSections[j]'hjN).offset.val = (e.sections[j]'hjS).offset.val := by
          rw [hVerbJ.2]
        have hSzJ : (newSections[j]'hjN).encodedSize = (e.sections[j]'hjS).encodedSize :=
          hPl.size_eq
        rw [hOffJ, hSzJ]
        exact Nat.le_trans hLe (Nat.le_trans hCurrLeStart hStartLeShoff)
    · -- Placed: state[j].range ≤ baseOffset + state.2 = startOffset + appendedBytes ≤ newShoff.
      refine Or.inr (Or.inr (Or.inr ?_))
      show (newSections[j]'hjN).offset.val + (newSections[j]'hjN).encodedSize ≤ newShoff
      have : (newSections[j]'hjN).offset.val + (newSections[j]'hjN).encodedSize
            ≤ startOffset + appendedBytes := hPlace.2.2
      omega

/-- `growEOFWith` produces a layout where all 7 splice regions are
    pairwise disjoint.  The output is suitable as the input to `encode`'s
    splice cascade.

    Preconditions (input-driven, all parser-derivable):
    * `hSection0Null`: shdr[0] is SHT_NULL (ELF spec invariant).
    * `hHeaderPhdr`/`hHeaderShdr`/`hPhdrShdr`/`hHeaderSec`/`hPhdrSec`:
      the input file's header / phdr-table / shdr-table / per-section
      disjointness invariants — all hold for any parser-produced ELF
      (they're part of the structural invariants real ELFs satisfy). -/
theorem growEOFWith_produces_spliceRegionsDisjoint (pageSize? : Option Nat) (e : ElfFile)
    (hSection0Null : ∀ (h : 0 < e.sections.size),
      (e.sections[0]'h).type = ShType.SHT_NULL)
    (hHeaderPhdr : e.headerPhdrDisjoint)
    (hHeaderShdr : e.headerShdrDisjoint)
    (hPhdrShdr   : e.phdrShdrDisjoint)
    (hHeaderSec  : e.headerSectionDisjoint)
    (hPhdrSec    : e.phdrSectionDisjoint) :
    (growEOFWith pageSize? e).spliceRegionsDisjoint := by
  unfold growEOFWith
  by_cases hLay : layoutAlreadyValid e = true
  · -- Fast path: output = e.
    simp only [hLay, ↓reduceIte]
    obtain ⟨hSec, hShdr⟩ := (layoutAlreadyValid_iff e).mp hLay
    exact
      { sections_disjoint := hSec
        hdr_phdr_disjoint := hHeaderPhdr
        hdr_shdr_disjoint := hHeaderShdr
        phdr_shdr_disjoint := hPhdrShdr
        hdr_sec_disjoint := hHeaderSec
        phdr_sec_disjoint := hPhdrSec
        shdr_sec_disjoint := hShdr }
  · simp only [hLay]
    -- Branch on lastPtLoadIdx.
    cases hLast : lastPtLoadIdx e.phdrs with
    | none =>
      simp
      exact layoutForEncoding_produces_spliceRegionsDisjoint e hSection0Null hHeaderPhdr
    | some lastIdx =>
      simp only []
      -- canExtendLastPtLoad branch.
      by_cases hExt : (canExtendLastPtLoad e
        (roundUp (currentFileEnd e)
          (match pageSize? with | some n => max n (maxPtLoadAlign e.phdrs) | none => maxPtLoadAlign e.phdrs))
        (roundUp (maxPtLoadVaddrEnd e.phdrs)
          (match pageSize? with | some n => max n (maxPtLoadAlign e.phdrs) | none => maxPtLoadAlign e.phdrs))
        (match pageSize? with | some n => max n (maxPtLoadAlign e.phdrs) | none => maxPtLoadAlign e.phdrs)
        lastIdx) = true
      · simp only [hExt, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        -- The output equals growEOFWithMainBody pageSize? e lastIdx.
        show (growEOFWithMainBody pageSize? e lastIdx).spliceRegionsDisjoint
        exact growEOFWithMainBody_produces_spliceRegionsDisjoint pageSize? e lastIdx
          hHeaderPhdr hHeaderSec hPhdrSec
      · simp only [hExt, Bool.not_false, ↓reduceIte]
        exact layoutForEncoding_produces_spliceRegionsDisjoint e hSection0Null hHeaderPhdr

end Patchelf.Elf
