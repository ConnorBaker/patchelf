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

    Implemented as a specialization of `placeStep` /
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

/-! ## `appendTransform` per-field preservation

    The transform only mutates `(offset, addr)`; every other field
    survives.  These rfl-lemmas feed the `_preserves_valid` proofs:
    they let us argue every `IsValid` clause at the placed index
    reduces to the same clause at the input index. -/

@[simp] theorem appendTransform_name (startOffset startPage : Nat)
    (s : Section) (o : Nat) :
    (appendTransform startOffset startPage s o).name = s.name := rfl

@[simp] theorem appendTransform_flags (startOffset startPage : Nat)
    (s : Section) (o : Nat) :
    (appendTransform startOffset startPage s o).flags = s.flags := rfl

@[simp] theorem appendTransform_link (startOffset startPage : Nat)
    (s : Section) (o : Nat) :
    (appendTransform startOffset startPage s o).link = s.link := rfl

@[simp] theorem appendTransform_info (startOffset startPage : Nat)
    (s : Section) (o : Nat) :
    (appendTransform startOffset startPage s o).info = s.info := rfl

@[simp] theorem appendTransform_addralign (startOffset startPage : Nat)
    (s : Section) (o : Nat) :
    (appendTransform startOffset startPage s o).addralign = s.addralign := rfl

@[simp] theorem appendTransform_entsize (startOffset startPage : Nat)
    (s : Section) (o : Nat) :
    (appendTransform startOffset startPage s o).entsize = s.entsize := rfl

@[simp] theorem appendTransform_content (startOffset startPage : Nat)
    (s : Section) (o : Nat) :
    (appendTransform startOffset startPage s o).content = s.content := rfl

/-! ## `appendStaleSections` per-field preservation

    Generic projection: any field that `appendTransform` preserves
    is preserved by `appendStaleSections` at every index.  Consumes
    `placeFold_value_witness` (the structural per-entry verbatim /
    `transform input off` disjunction).  Per-field corollaries below
    instantiate the projection for the seven non-(offset, addr)
    fields that `IsValid` clauses depend on. -/

theorem appendStaleSections_field_eq.{u}
    {α : Type u} (sections : Array Section) (stale : Array Bool)
    (startOffset startPage : Nat)
    (proj : Section → α)
    (hTransform : ∀ s o, proj (appendTransform startOffset startPage s o) = proj s)
    (j : Nat)
    (hj : j < (appendStaleSections sections stale startOffset startPage).1.size)
    (hjS : j < sections.size) :
    proj ((appendStaleSections sections stale startOffset startPage).1[j]'hj)
      = proj (sections[j]'hjS) := by
  unfold appendStaleSections
  rcases PlaceFold.placeFold_value_witness sections 0 j hjS hj with
    ⟨_, hVerb⟩ | ⟨_, off, hPlaced⟩
  · -- Verbatim: output[j] = sections[j].
    rw [hVerb]
  · -- Placed: output[j] = appendTransform sections[j] off; use hTransform.
    rw [hPlaced]; exact hTransform _ _

/-- `appendStaleSections` preserves `name` at every index. -/
theorem appendStaleSections_name (sections : Array Section) (stale : Array Bool)
    (startOffset startPage : Nat) (j : Nat)
    (hj : j < (appendStaleSections sections stale startOffset startPage).1.size)
    (hjS : j < sections.size) :
    ((appendStaleSections sections stale startOffset startPage).1[j]'hj).name
      = (sections[j]'hjS).name :=
  appendStaleSections_field_eq sections stale startOffset startPage
    (·.name) (fun _ _ => rfl) j hj hjS

/-- `appendStaleSections` preserves `flags`. -/
theorem appendStaleSections_flags (sections : Array Section) (stale : Array Bool)
    (startOffset startPage : Nat) (j : Nat)
    (hj : j < (appendStaleSections sections stale startOffset startPage).1.size)
    (hjS : j < sections.size) :
    ((appendStaleSections sections stale startOffset startPage).1[j]'hj).flags
      = (sections[j]'hjS).flags :=
  appendStaleSections_field_eq sections stale startOffset startPage
    (·.flags) (fun _ _ => rfl) j hj hjS

/-- `appendStaleSections` preserves `link`. -/
theorem appendStaleSections_link (sections : Array Section) (stale : Array Bool)
    (startOffset startPage : Nat) (j : Nat)
    (hj : j < (appendStaleSections sections stale startOffset startPage).1.size)
    (hjS : j < sections.size) :
    ((appendStaleSections sections stale startOffset startPage).1[j]'hj).link
      = (sections[j]'hjS).link :=
  appendStaleSections_field_eq sections stale startOffset startPage
    (·.link) (fun _ _ => rfl) j hj hjS

/-- `appendStaleSections` preserves `info`. -/
theorem appendStaleSections_info (sections : Array Section) (stale : Array Bool)
    (startOffset startPage : Nat) (j : Nat)
    (hj : j < (appendStaleSections sections stale startOffset startPage).1.size)
    (hjS : j < sections.size) :
    ((appendStaleSections sections stale startOffset startPage).1[j]'hj).info
      = (sections[j]'hjS).info :=
  appendStaleSections_field_eq sections stale startOffset startPage
    (·.info) (fun _ _ => rfl) j hj hjS

/-- `appendStaleSections` preserves `addralign`. -/
theorem appendStaleSections_addralign (sections : Array Section) (stale : Array Bool)
    (startOffset startPage : Nat) (j : Nat)
    (hj : j < (appendStaleSections sections stale startOffset startPage).1.size)
    (hjS : j < sections.size) :
    ((appendStaleSections sections stale startOffset startPage).1[j]'hj).addralign
      = (sections[j]'hjS).addralign :=
  appendStaleSections_field_eq sections stale startOffset startPage
    (·.addralign) (fun _ _ => rfl) j hj hjS

/-- `appendStaleSections` preserves `entsize`. -/
theorem appendStaleSections_entsize (sections : Array Section) (stale : Array Bool)
    (startOffset startPage : Nat) (j : Nat)
    (hj : j < (appendStaleSections sections stale startOffset startPage).1.size)
    (hjS : j < sections.size) :
    ((appendStaleSections sections stale startOffset startPage).1[j]'hj).entsize
      = (sections[j]'hjS).entsize :=
  appendStaleSections_field_eq sections stale startOffset startPage
    (·.entsize) (fun _ _ => rfl) j hj hjS

/-- `appendStaleSections` preserves `content`. -/
theorem appendStaleSections_content (sections : Array Section) (stale : Array Bool)
    (startOffset startPage : Nat) (j : Nat)
    (hj : j < (appendStaleSections sections stale startOffset startPage).1.size)
    (hjS : j < sections.size) :
    ((appendStaleSections sections stale startOffset startPage).1[j]'hj).content
      = (sections[j]'hjS).content :=
  appendStaleSections_field_eq sections stale startOffset startPage
    (·.content) (fun _ _ => rfl) j hj hjS

/-- `appendStaleSections` preserves `type` (already provable via
    `Placement.type_eq`, but we expose it here for uniform access
    alongside the other field corollaries). -/
theorem appendStaleSections_type (sections : Array Section) (stale : Array Bool)
    (startOffset startPage : Nat) (j : Nat)
    (hj : j < (appendStaleSections sections stale startOffset startPage).1.size)
    (hjS : j < sections.size) :
    ((appendStaleSections sections stale startOffset startPage).1[j]'hj).type
      = (sections[j]'hjS).type :=
  appendStaleSections_field_eq sections stale startOffset startPage
    (·.type) (fun s o => by show (appendTransform _ _ s o).content.type = _; rfl)
    j hj hjS

/-- `appendStaleSections` preserves `encodedSize` (consequence of
    content preservation; encodedSize is content-derived). -/
theorem appendStaleSections_encodedSize (sections : Array Section) (stale : Array Bool)
    (startOffset startPage : Nat) (j : Nat)
    (hj : j < (appendStaleSections sections stale startOffset startPage).1.size)
    (hjS : j < sections.size) :
    ((appendStaleSections sections stale startOffset startPage).1[j]'hj).encodedSize
      = (sections[j]'hjS).encodedSize := by
  unfold Section.encodedSize
  rw [appendStaleSections_content sections stale startOffset startPage j hj hjS]

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

/-- Retarget every PT_PHDR program header to a new (offset, vaddr,
    size) tuple.  Used by `growEOFWithFreshPtLoadReloc` to keep the
    PT_PHDR phdr in agreement with the new `e_phoff` after the phdr
    table is moved to the appended region.

    PT_PHDR is informational — the kernel reads `e_phoff` directly to
    find phdrs at exec — but glibc's `ld.so` consults PT_PHDR to
    derive the load base.  Without this update, dynamic loading
    miscomputes the base and segfaults at the first relocation. -/
def retargetPtPhdr (phdrs : Array Patchelf.Elf.ProgramHeader)
    (newOff newVaddr newSize : Nat) : Array Patchelf.Elf.ProgramHeader :=
  phdrs.map fun ph =>
    if ph.type = PhType.PT_PHDR then
      { ph with offset := ⟨newOff⟩
              , vaddr := ⟨newVaddr⟩
              , paddr := ⟨newVaddr⟩
              , filesz := ⟨newSize⟩
              , memsz := ⟨newSize⟩ }
    else ph

-- (Forward-looking: `updatePhdrsAfterMove`-specific per-phdr facts
--  for PT_LOAD / PT_INTERP / PT_DYNAMIC are needed for
--  `growEOFWithMainBody_preserves_loadable`.  Phase L1 (covering
--  `layoutForEncoding`) lands on the simpler `relocatePhdr` infrastructure
--  in `LayoutEngine.lean`; the analog for `updatePhdrsAfterMove` requires
--  more case-bash because the `if i = lastIdx` branch interacts with
--  the PT_INTERP / PT_DYNAMIC type tests.  Picking up under §1.2
--  follow-up.)

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

/-- In-place fresh-PT_LOAD precondition: there is room in the original
    phdr-bearing region for one more 56-byte phdr entry, and the
    extended region is disjoint from every non-NOBITS/NULL section.

    "Room" means: the extended phdr-table region
    `[phoff, phoff + (phnum + 1) * phdrSize)` ends within
    `currentFileEnd e` and stays past the ELF header.  Together with
    the per-section disjointness, that is enough to discharge the
    `hdr_phdr_disjoint` and `phdr_sec_disjoint` clauses of the output's
    `spliceRegionsDisjoint`.

    When this fails, callers should fall through to either the
    `relocatePht` sub-case (move the phdr table to the new region —
    not implemented) or `layoutForEncoding`'s unaware repack. -/
def canAddFreshPtLoad (e : ElfFile) : Bool :=
  let phoff := e.header.phoff.val
  let newPhEnd := phoff + (e.phdrs.size + 1) * Layout.phdrSize
  decide (Layout.ehdrSize ≤ phoff) &&
  decide (newPhEnd ≤ currentFileEnd e) &&
  Nat.fold e.sections.size (init := true) (fun i hi acc =>
    let s := e.sections[i]'hi
    let entryOk : Bool :=
      decide (s.type = ShType.SHT_NOBITS) ||
      decide (s.type = ShType.SHT_NULL) ||
      decide (newPhEnd ≤ s.offset.val) ||
      decide (s.offset.val + s.encodedSize ≤ phoff)
    acc && entryOk)

/-- Build a brand-new PT_LOAD entry covering the appended region
    `[startOffset, startOffset + appendedBytes)` in file space and
    `[startPage, startPage + appendedBytes)` in vaddr space.  Flags
    are `PF_R | PF_W` (readable + writable; conservative — moved
    sections may be data, and a too-permissive segment never breaks
    the loader, only a too-restrictive one does). -/
def freshPtLoad (startOffset startPage appendedBytes alignStartPage : Nat) :
    Patchelf.Elf.ProgramHeader :=
  { type   := PhType.PT_LOAD
    flags  := PF_RW
    offset := ⟨startOffset⟩
    vaddr  := ⟨startPage⟩
    paddr  := ⟨startPage⟩
    filesz := ⟨appendedBytes⟩
    memsz  := ⟨appendedBytes⟩
    align  := ⟨alignStartPage⟩ }

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
        -- Can't extend the last PT_LOAD (huge BSS or wrong alignment).
        -- Try the fresh-PT_LOAD-allocation path; if there's no room in
        -- the existing phdr slot, fall through to `relocatePht` (move
        -- the phdr table itself to the appended region).
        if canAddFreshPtLoad e then
          -- In-place sub-case: inline body of `growEOFWithFreshPtLoad pageSize? e`.
          let stale : Array Bool := Array.ofFn (n := e.sections.size) fun i =>
            sectionStale e i.val i.isLt
          let placed := appendStaleSections e.sections stale startOffset startPage
          let newSections := placed.1
          let appendedBytes := placed.2
          let newShoff := roundUp (startOffset + appendedBytes) 8
          let retargetedPhdrs := updatePhdrsAfterMove e.phdrs none 0 0
                                e.interpIdx e.dynamicIdx newSections
          let newPhdrs := retargetedPhdrs.push
            (freshPtLoad startOffset startPage appendedBytes alignStartPage)
          let newHeader : Patchelf.Elf.ElfHeader :=
            { e.header with shoff := ⟨newShoff⟩
                          , phnum := (e.phdrs.size + 1).toUInt16 }
          { header := newHeader, phdrs := newPhdrs, sections := newSections }
        else
          -- relocatePht sub-case: inline body of
          -- `growEOFWithFreshPtLoadReloc pageSize? e`.
          let phtSize := (e.phdrs.size + 1) * Layout.phdrSize
          let secStartOffset := startOffset + phtSize
          let secStartPage := startPage + phtSize
          let stale : Array Bool := Array.ofFn (n := e.sections.size) fun i =>
            sectionStale e i.val i.isLt
          let placed := appendStaleSections e.sections stale secStartOffset secStartPage
          let newSections := placed.1
          let appendedBytes := placed.2
          let totalAppendBytes := phtSize + appendedBytes
          let newShoff := roundUp (startOffset + totalAppendBytes) 8
          let retargetedPhdrs := updatePhdrsAfterMove e.phdrs none 0 0
                                e.interpIdx e.dynamicIdx newSections
          let phdrRetargeted := retargetPtPhdr retargetedPhdrs startOffset startPage phtSize
          let newPhdrs := phdrRetargeted.push
            (freshPtLoad startOffset startPage totalAppendBytes alignStartPage)
          let newHeader : Patchelf.Elf.ElfHeader :=
            { e.header with phoff := ⟨startOffset⟩
                          , shoff := ⟨newShoff⟩
                          , phnum := (e.phdrs.size + 1).toUInt16 }
          { header := newHeader, phdrs := newPhdrs, sections := newSections }
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

/-! ## `syncDtAddrEntry` invariants

    `syncDtAddrEntry` only ever rewrites `d.value` on entries whose
    `tag.isAddressTag = true`.  None of the four string-ref tags
    (`needed`, `soname`, `rpath`, `runpath`) are address tags, so
    `value` is unchanged on string-ref entries — this is the key
    fact that lets `syncDtAddrTagsInFile_preserves_valid` reuse the
    `dynsym_wf` argument from `syncDtStrszInFile`. -/

theorem syncDtAddrEntry_tag (e : ElfFile) (d : DynEntry) :
    (syncDtAddrEntry e d).tag = d.tag := by
  unfold syncDtAddrEntry
  by_cases hAT : d.tag.isAddressTag
  · rw [if_pos hAT]
    cases addrTagTarget e d.tag <;> rfl
  · rw [if_neg hAT]

theorem syncDtAddrEntry_isStringRef (e : ElfFile) (d : DynEntry) :
    (syncDtAddrEntry e d).isStringRef = d.isStringRef := by
  unfold DynEntry.isStringRef
  rw [syncDtAddrEntry_tag]

/-- On string-ref entries (DT_NEEDED / DT_SONAME / DT_RPATH /
    DT_RUNPATH — none of which are address tags), `syncDtAddrEntry`
    is the identity. -/
theorem syncDtAddrEntry_value_of_stringRef (e : ElfFile) (d : DynEntry)
    (hSR : d.isStringRef = true) :
    (syncDtAddrEntry e d).value = d.value := by
  unfold syncDtAddrEntry
  rw [DynEntry.isStringRef_iff] at hSR
  by_cases hAT : d.tag.isAddressTag = true
  · -- Address tag and string-ref are mutually exclusive — derive False.
    exfalso
    unfold DynTag.isAddressTag at hAT
    rcases hSR with h | h | h | h <;> rw [h] at hAT <;> cases hAT
  · simp only [Bool.not_eq_true] at hAT
    rw [if_neg]
    intro h; rw [h] at hAT; cases hAT

/-- `syncDtAddrEntry` preserves `back?`'s `.tag = DT_NULL` check. -/
theorem syncDtAddr_back_null (e : ElfFile) (dyn : Array DynEntry) :
    (dyn.map (syncDtAddrEntry e)).back?.any
        (fun e => decide (e.tag = DynTag.null)) =
      dyn.back?.any (fun e => decide (e.tag = DynTag.null)) := by
  rw [Array.back?_map]
  cases hb : dyn.back? with
  | none   => simp
  | some d => simp [syncDtAddrEntry_tag]

/-- `syncDtAddrEntry`-mapping preserves `SectionContent.dynamic _`'s
    WellFormed. -/
theorem syncDtAddr_content_wf (e : ElfFile) (dyn : Array DynEntry)
    (h : (SectionContent.dynamic dyn).WellFormed) :
    (SectionContent.dynamic (dyn.map (syncDtAddrEntry e))).WellFormed := by
  show Option.any _ (dyn.map (syncDtAddrEntry e)).back? = true
  rw [syncDtAddr_back_null]
  exact h

/-! ## `syncDtAddrTagsInFile` preserves byte-layer `IsValid`

    Mirrors `syncDtStrszInFile_aux_preserves_valid` in
    `Encoder.lean`.  The key facts:
      * `syncDtAddrEntry` preserves `.tag` (always).
      * Hence the `.dynamic` array's `back?` and DT_NULL position are
        preserved.
      * `.value` is unchanged on string-ref entries, so
        `dynamicStringRefsValid` survives.
      * Every other section's `Section` value is unchanged.

    Like `syncDtStrszInFile_aux_preserves_valid`, requires
    `e.dynstr = some ds`.  Concretely: we need to know
    `iDyn ≠ shstrndx` so `updateSectionContent_dynstr_eq` /
    `updateSectionContent_shstrtab` apply.  The dynstr witness gives
    that via `shstrndx_ne_of_content_dynamic_of_dynstr`.  Real
    callers (encoder pipeline post-`growEOFWith`) always supply
    dynstr; the outer wrapper handles the `dynstr = none`
    degenerate case via `syncDtAddrTagsInFile_cases`. -/

private theorem syncDtAddrTagsInFile_aux_preserves_valid (e : ElfFile)
    (hVal : e.IsValid) (ds : StringTable) (dyn : Array DynEntry) (iDyn : Nat)
    (hDs : e.dynstr = some ds)
    (hDyn : e.dynamic = some dyn) (hIdx : e.dynamicIdx = some iDyn)
    (hBound : iDyn < e.sections.size) :
    (e.updateSectionContent iDyn
      (SectionContent.dynamic (dyn.map (syncDtAddrEntry e)))).IsValid := by
  -- Recover the section's content from `e.dynamic = some dyn`.
  have hContent : (e.sections[iDyn]'hBound).content = .dynamic dyn := by
    have hCa : e.contentAt e.dynamicIdx = some (.dynamic dyn) := by
      unfold ElfFile.dynamic at hDyn
      split at hDyn <;> first | (cases hDyn; assumption) | cases hDyn
    rw [hIdx] at hCa
    unfold ElfFile.contentAt at hCa
    simp only [Option.bind_some, dif_pos hBound] at hCa
    exact Option.some.inj hCa
  let e' := e.updateSectionContent iDyn
    (SectionContent.dynamic (dyn.map (syncDtAddrEntry e)))
  show e'.IsValid
  have hHeader : e'.header = e.header := by simp [e']
  have hPhdrs : e'.phdrs = e.phdrs := by simp [e']
  have hSecSize : e'.sections.size = e.sections.size := by simp [e']
  have hBound' : iDyn < e'.sections.size := by simp [hSecSize, hBound]
  have hOther : ∀ (j : Nat) (hj : j < e.sections.size) (_ : j ≠ iDyn)
      (hj' : j < e'.sections.size),
      e'.sections[j]'hj' = e.sections[j]'hj :=
    fun j hj hne hj' =>
      ElfFile.updateSectionContent_getElem_ne e _ _ _ hj hne hj'
  have hSelf : ∀ (h' : iDyn < e'.sections.size),
      e'.sections[iDyn]'h' = { e.sections[iDyn]'hBound with
        content := .dynamic (dyn.map (syncDtAddrEntry e)) } :=
    fun h' => ElfFile.updateSectionContent_getElem_self e _ _ hBound h'
  have hType_iDyn : (e.sections[iDyn]'hBound).type = ShType.SHT_DYNAMIC := by
    obtain ⟨_, hT⟩ := ElfFile.findUniqueTypeIdx_section_type e _ _ hIdx
    exact hT
  have hType : ∀ (j : Nat) (hj : j < e.sections.size)
      (hj' : j < e'.sections.size),
      (e'.sections[j]'hj').type = (e.sections[j]'hj).type := by
    intro j hj hj'
    by_cases hji : j = iDyn
    · subst hji
      rw [ElfFile.updateSectionContent_type_self _ _ _ hj hj']
      simp only [SectionContent.type, Section.type, hContent]
    · exact ElfFile.updateSectionContent_type _ _ _ _ hj hji hj'
  have hName : ∀ (j : Nat) (hj : j < e.sections.size)
      (hj' : j < e'.sections.size),
      (e'.sections[j]'hj').name = (e.sections[j]'hj).name :=
    fun j hj hj' => ElfFile.updateSectionContent_name _ _ _ _ hj hj'
  -- shstrndx-disjointness from `e.dynstr = some ds` + iDyn's content.
  have hShstrNe : iDyn ≠ e.header.shstrndx.toNat :=
    ElfFile.shstrndx_ne_of_content_dynamic_of_dynstr e hBound hContent hDs
  -- Typed accessors at non-iDyn indices are preserved.
  have hDsEq' : e'.dynstr = e.dynstr := by
    apply ElfFile.updateSectionContent_dynstr_eq _ _ _ hShstrNe
    intro iStr hStr
    exact (ElfFile.dynstrIdx_target_ne_of_content_dynamic
      e hBound hContent hDs hStr).symm
  have hDsymEq' : e'.dynsym = e.dynsym := by
    apply ElfFile.updateSectionContent_dynsym_eq
    · simp [SectionContent.type]; decide
    · intro hi
      simp only [Section.type, hContent, SectionContent.type]; decide
    · intro iSym hSym hEq
      subst hEq
      obtain ⟨_, hT⟩ := ElfFile.findUniqueTypeIdx_section_type e _ _ hSym
      rw [hType_iDyn] at hT
      cases hT
  -- Pointwise equality of `Section.contentWellFormedB`.
  have hContentWFB : ∀ (j : Nat) (hj : j < e.sections.size)
      (hj' : j < e'.sections.size),
      ElfFile.Section.contentWellFormedB (e'.sections[j]'hj') =
        ElfFile.Section.contentWellFormedB (e.sections[j]'hj) := by
    intros j hj hj'
    by_cases hjEq : j = iDyn
    · subst hjEq; rw [hSelf hj']
      unfold ElfFile.Section.contentWellFormedB
      simp only [hContent]
      have hWF : (SectionContent.dynamic dyn).WellFormed ↔
          (SectionContent.dynamic (dyn.map (syncDtAddrEntry e))).WellFormed := by
        constructor
        · exact syncDtAddr_content_wf _ _
        · intro h
          show Option.any _ dyn.back? = true
          rw [← syncDtAddr_back_null e]; exact h
      simp [hWF]
    · rw [hOther j hj hjEq hj']
  have hStrtabWFB : ∀ (j : Nat) (hj : j < e.sections.size)
      (hj' : j < e'.sections.size),
      ElfFile.Section.strtabWellFormedB (e'.sections[j]'hj') =
        ElfFile.Section.strtabWellFormedB (e.sections[j]'hj) := by
    intros j hj hj'
    by_cases hjEq : j = iDyn
    · subst hjEq; rw [hSelf hj']
      unfold ElfFile.Section.strtabWellFormedB
      simp only [hContent]
    · rw [hOther j hj hjEq hj']
  -- The 8 IsValid clauses.
  refine
    { header_counts := ?_, sections_wf := ?_, strtabs_wf := ?_,
      dynamic_wf := ?_, dynsym_wf := ?_, content_wf := ?_,
      types_distinct := ?_, names_unique := ?_ }
  ----------------------------------------
  -- header_counts
  ----------------------------------------
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hVal.header_counts
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [hHeader, hPhdrs, hSecSize, h1, h2, h3, h4, h5]
  ----------------------------------------
  -- sections_wf
  ----------------------------------------
  · intro h0
    have h0' : 0 < e.sections.size := by simpa [hSecSize] using h0
    rw [hType 0 h0' h0]
    exact hVal.sections_wf h0'
  ----------------------------------------
  -- strtabs_wf
  ----------------------------------------
  · have hAll := hVal.strtabs_wf
    show e'.sections.all _ = true
    unfold ElfFile.strtabsWellFormed at hAll
    rw [Array.all_eq_true] at hAll ⊢
    intro j hj
    have hjE : j < e.sections.size := by simpa [hSecSize] using hj
    rw [hStrtabWFB j hjE hj]
    exact hAll j hjE
  ----------------------------------------
  -- dynamic_wf
  ----------------------------------------
  · have hIdx' : e'.dynamicIdx = some iDyn := by
      rw [ElfFile.updateSectionContent_dynamicIdx e iDyn _
        (fun _ => by simp [Section.type, hContent, SectionContent.type])]; exact hIdx
    have hDyn' : e'.dynamic = some (dyn.map (syncDtAddrEntry e)) := by
      unfold ElfFile.dynamic
      rw [hIdx']
      simp only [ElfFile.contentAt, Option.bind_some, dif_pos hBound']
      rw [hSelf hBound']
    refine ⟨?_, ?_⟩
    · -- dynamicTerminated.
      intro d hd
      rw [hDyn'] at hd
      cases hd
      have ⟨hSize, hBack, hUnique⟩ := hVal.dynamic_wf.1 dyn hDyn
      have hSizeEq : (dyn.map (syncDtAddrEntry e)).size = dyn.size := Array.size_map ..
      refine ⟨hSizeEq ▸ hSize, ?_, ?_⟩
      · -- (dyn.map _)[size - 1].tag = .null
        simp only [Array.size_map]
        rw [Array.getElem_map, syncDtAddrEntry_tag]
        exact hBack
      · -- uniqueness of DT_NULL position
        intros i hi hT
        rw [hSizeEq] at hi
        rw [Array.getElem_map, syncDtAddrEntry_tag] at hT
        rw [hSizeEq]
        exact hUnique i hi hT
    · -- dynamicStringRefsValid.
      intro d ds' hd hds'
      rw [hDyn'] at hd
      cases hd
      rw [hDsEq'] at hds'
      rw [hDs] at hds'
      cases hds'
      have hOrig := hVal.dynamic_wf.2 dyn ds hDyn hDs
      intros i hi hSR
      rw [show (dyn.map (syncDtAddrEntry e)).size = dyn.size from
            Array.size_map ..] at hi
      rw [Array.getElem_map]
      rw [Array.getElem_map] at hSR
      rw [syncDtAddrEntry_isStringRef] at hSR
      rw [syncDtAddrEntry_value_of_stringRef _ _ hSR]
      exact hOrig i hi hSR
  ----------------------------------------
  -- dynsym_wf
  ----------------------------------------
  · intros syms ds' hSyms hDs'
    have hOrigSyms : e.dynsym = some syms := hDsymEq' ▸ hSyms
    have hOrigDs   : e.dynstr = some ds'  := hDsEq'   ▸ hDs'
    exact hVal.dynsym_wf syms ds' hOrigSyms hOrigDs
  ----------------------------------------
  -- content_wf
  ----------------------------------------
  · have hAll := hVal.content_wf
    show e'.sections.all _ = true
    unfold ElfFile.sectionsContentWellFormed at hAll
    rw [Array.all_eq_true] at hAll ⊢
    intro j hj
    have hjE : j < e.sections.size := by simpa [hSecSize] using hj
    rw [hContentWFB j hjE hj]
    exact hAll j hjE
  ----------------------------------------
  -- types_distinct
  ----------------------------------------
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hVal.types_distinct
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> {
      intros i hi j hj hi_t hj_t
      have hiE : i < e.sections.size := by simpa [hSecSize] using hi
      have hjE : j < e.sections.size := by simpa [hSecSize] using hj
      rw [hType i hiE hi] at hi_t
      rw [hType j hjE hj] at hj_t
      first
      | exact h1 i hiE j hjE hi_t hj_t
      | exact h2 i hiE j hjE hi_t hj_t
      | exact h3 i hiE j hjE hi_t hj_t
      | exact h4 i hiE j hjE hi_t hj_t
      | exact h5 i hiE j hjE hi_t hj_t
      | exact h6 i hiE j hjE hi_t hj_t
    }
  ----------------------------------------
  -- names_unique
  ----------------------------------------
  · unfold ElfFile.namedSectionsUnique
    rw [ElfFile.updateSectionContent_shstrtab _ _ _ hShstrNe]
    cases hSt : e.shstrtab with
    | none => trivial
    | some st =>
        obtain ⟨h1, h2⟩ := by
          have := hVal.names_unique
          unfold ElfFile.namedSectionsUnique at this
          rw [hSt] at this; exact this
        constructor <;> {
          intros i hi j hj hi_n hj_n
          have hiE : i < e.sections.size := by simpa [hSecSize] using hi
          have hjE : j < e.sections.size := by simpa [hSecSize] using hj
          rw [hName i hiE hi] at hi_n
          rw [hName j hjE hj] at hj_n
          first
          | exact h1 i hiE j hjE hi_n hj_n
          | exact h2 i hiE j hjE hi_n hj_n
        }

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
    cases e.dynamic <;> exact Or.inl rfl
  | some iDyn =>
    cases hD : e.dynamic with
    | none => exact Or.inl rfl
    | some dyn =>
      by_cases hLt : iDyn < e.sections.size
      · refine Or.inr ⟨iDyn, hLt, dyn, ?_, ?_⟩
        · unfold ElfFile.dynamic at hD
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
        · simp only [dif_pos hLt]
      · refine Or.inl ?_; simp only [dif_neg hLt]

/-- `syncDtAddrTagsInFile` preserves the byte-layer `IsValid` invariant
    when the input has a `.dynstr` section.  Companion to
    `syncDtAddrTagsInFile_preserves_spliceRegionsDisjoint`; together
    they cover both invariant families.  Mirrors
    `syncDtStrszInFile_preserves_valid` (which has the same dynstr
    precondition for the same reason).

    The dynstr precondition is needed because `iDyn ≠ shstrndx` is
    only derivable from the dynstr witness — `IsValid` alone doesn't
    force shstrndx to point at a strtab, so the section at shstrndx
    could in principle be the SHT_DYNAMIC section we are mutating.
    Real ELFs always satisfy the precondition (any binary with
    `.dynamic` has `.dynstr`); the runtime-decidable validator
    catches the pathological case at write time. -/
theorem syncDtAddrTagsInFile_preserves_valid (e : ElfFile) (hVal : e.IsValid)
    {ds : StringTable} (hDs : e.dynstr = some ds) :
    (syncDtAddrTagsInFile e).IsValid := by
  rcases syncDtAddrTagsInFile_cases e with hEq | ⟨iDyn, hLt, dyn, hContent, hEq⟩
  · rw [hEq]; exact hVal
  · rw [hEq]
    have hType : (e.sections[iDyn]'hLt).type = ShType.SHT_DYNAMIC := by
      simp [Section.type, hContent, SectionContent.type]
    have hIdx : e.dynamicIdx = some iDyn := by
      unfold ElfFile.dynamicIdx
      rcases hVal.types_distinct with ⟨h1, _, _, _, _, _⟩
      exact ElfFile.findUniqueTypeIdx_eq_some e ShType.SHT_DYNAMIC
              iDyn hLt hType h1
    have hDyn : e.dynamic = some dyn := by
      unfold ElfFile.dynamic
      rw [hIdx]
      unfold ElfFile.contentAt
      simp only [Option.bind_some, dif_pos hLt]
      rw [hContent]
    exact syncDtAddrTagsInFile_aux_preserves_valid e hVal ds dyn iDyn hDs hDyn hIdx hLt

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

/-! ## `canAddFreshPtLoad` extraction lemmas -/

/-- `canAddFreshPtLoad` packages three facts; this extracts clause 1
    (header end ≤ phoff). -/
theorem canAddFreshPtLoad_ehdrSize_le_phoff (e : ElfFile)
    (h : canAddFreshPtLoad e = true) :
    Layout.ehdrSize ≤ e.header.phoff.val := by
  unfold canAddFreshPtLoad at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

/-- Clause 2: extended phdr table fits within `currentFileEnd`. -/
theorem canAddFreshPtLoad_newPhEnd_le_currentFileEnd (e : ElfFile)
    (h : canAddFreshPtLoad e = true) :
    e.header.phoff.val + (e.phdrs.size + 1) * Layout.phdrSize ≤ currentFileEnd e := by
  unfold canAddFreshPtLoad at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

/-- Helper: `Nat.fold ... && entryOk` is `true` iff every iteration's
    contribution is `true`. -/
theorem nat_fold_and_true_iff
    (n : Nat) (g : (i : Nat) → i < n → Bool) :
    Nat.fold n (init := true)
      (fun i hi acc => acc && g i hi) = true ↔
    ∀ (i : Nat) (hi : i < n), g i hi = true := by
  induction n with
  | zero =>
    rw [Nat.fold_zero]
    constructor
    · intros _ i hi; exact absurd hi (Nat.not_lt_zero _)
    · intros _; rfl
  | succ k ih =>
    rw [Nat.fold_succ]
    show (Nat.fold k _ true && g k (Nat.lt_succ_self _)) = true ↔ _
    rw [Bool.and_eq_true]
    constructor
    · rintro ⟨hInner, hG⟩
      intros i hi
      by_cases hiK : i < k
      · have ihLeft := (ih (fun i hi => g i (Nat.lt_succ_of_lt hi))).mp hInner
        exact ihLeft i hiK
      · have hiEq : i = k := by omega
        subst hiEq
        exact hG
    · intros hAll
      refine ⟨?_, hAll k (Nat.lt_succ_self _)⟩
      apply (ih (fun i hi => g i (Nat.lt_succ_of_lt hi))).mpr
      intros i hi
      exact hAll i (Nat.lt_succ_of_lt hi)

/-- Clause 3: every section is either NOBITS/NULL or its file range is
    disjoint from the extended phdr region. -/
theorem canAddFreshPtLoad_pair_disjoint (e : ElfFile)
    (h : canAddFreshPtLoad e = true)
    (i : Nat) (hi : i < e.sections.size) :
    (e.sections[i]'hi).type = ShType.SHT_NOBITS ∨
    (e.sections[i]'hi).type = ShType.SHT_NULL ∨
    IntervalDisjoint
      e.header.phoff.val
      (e.header.phoff.val + (e.phdrs.size + 1) * Layout.phdrSize)
      (e.sections[i]'hi).offset.val
      ((e.sections[i]'hi).offset.val + (e.sections[i]'hi).encodedSize) := by
  unfold canAddFreshPtLoad at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨_, hFold⟩ := h
  -- Apply nat_fold_and_true_iff.
  let g : (i : Nat) → i < e.sections.size → Bool := fun i hi =>
    let s := e.sections[i]'hi
    decide (s.type = ShType.SHT_NOBITS) ||
    decide (s.type = ShType.SHT_NULL) ||
    decide (e.header.phoff.val + (e.phdrs.size + 1) * Layout.phdrSize ≤ s.offset.val) ||
    decide (s.offset.val + s.encodedSize ≤ e.header.phoff.val)
  have hReshape : Nat.fold e.sections.size (init := true) (fun i hi acc =>
      let s := e.sections[i]'hi
      let entryOk : Bool :=
        decide (s.type = ShType.SHT_NOBITS) ||
        decide (s.type = ShType.SHT_NULL) ||
        decide (e.header.phoff.val + (e.phdrs.size + 1) * Layout.phdrSize ≤ s.offset.val) ||
        decide (s.offset.val + s.encodedSize ≤ e.header.phoff.val)
      acc && entryOk) =
      Nat.fold e.sections.size (init := true) (fun jIdx hjIdx acc => acc && g jIdx hjIdx) :=
    rfl
  rw [hReshape] at hFold
  have hPer := (nat_fold_and_true_iff e.sections.size g).mp hFold
  have hG := hPer i hi
  -- hG : decide (...) || decide (...) || decide (...) || decide (...) = true.
  simp only [g, Bool.or_eq_true, decide_eq_true_eq] at hG
  rcases hG with ((hNB | hN) | hLeRight) | hLeLeft
  · exact Or.inl hNB
  · exact Or.inr (Or.inl hN)
  · -- newPhEnd ≤ s.offset → IntervalDisjoint phoff newPhEnd s.offset (s.offset + ...).
    refine Or.inr (Or.inr (Or.inl hLeRight))
  · -- s.offset + s.encodedSize ≤ phoff → IntervalDisjoint phoff newPhEnd s.offset (s.offset + ...).
    refine Or.inr (Or.inr (Or.inr hLeLeft))

/-- `growEOFWith` fresh-PT_LOAD-allocation construction (in-place
    sub-case: phdr table stays at its original location).  Same
    overall shape as `growEOFWithMainBody`, but instead of extending
    the last existing PT_LOAD's `filesz`/`memsz` to cover the appended
    region, we append a brand-new PT_LOAD entry covering it and bump
    `e.header.phnum` by 1.  Used when `canExtendLastPtLoad` rejects
    (BSS-heavy binaries like coreutils `ls`) AND `canAddFreshPtLoad`
    accepts (room for one more phdr in the existing slot).

    For binaries with the phdr table packed tight against the first
    section (no in-place room), the `relocatePht` companion below
    moves the phdr table itself to the appended region. -/
def growEOFWithFreshPtLoad (pageSize? : Option Nat) (e : ElfFile) : ElfFile :=
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
  -- Retarget PT_INTERP / PT_DYNAMIC for moved sections, but DON'T
  -- extend any existing PT_LOAD (passing `none` for lastIdx?).
  let retargetedPhdrs := updatePhdrsAfterMove e.phdrs none 0 0
                        e.interpIdx e.dynamicIdx newSections
  -- Append the new PT_LOAD covering the appended region.
  let newPhdrs := retargetedPhdrs.push
    (freshPtLoad startOffset startPage appendedBytes alignStartPage)
  -- Bump phnum so `headerCountsConsistent` survives.
  let newHeader : Patchelf.Elf.ElfHeader :=
    { e.header with shoff := ⟨newShoff⟩
                  , phnum := (e.phdrs.size + 1).toUInt16 }
  { header := newHeader, phdrs := newPhdrs, sections := newSections }

/-- `growEOFWith` fresh-PT_LOAD-allocation construction
    (`relocatePht` sub-case: the phdr table itself moves to the
    appended region).  Used when the binary has no room for one
    more phdr at the original location — i.e., `canExtendLastPtLoad`
    rejects AND `canAddFreshPtLoad` rejects.  Mirrors the C++
    `rewriteSectionsLibrary` `relocatePht = true` branch
    (`patchelf.cc:848`).

    Layout in the appended region:
      `[startOffset, startOffset + phtSize)`              — relocated phdr table
      `[startOffset + phtSize, startOffset + phtSize + appendedBytes)` — moved sections

    The new PT_LOAD covers BOTH (`filesz = memsz = phtSize +
    appendedBytes`).  `header.phoff` is updated to `startOffset`;
    `header.phnum` becomes `phdrs.size + 1`.  This dispatches
    `appendStaleSections` with a base offset shifted by `phtSize`
    so the moved sections sit just past the relocated phdrs.

    Note: ELF spec doesn't constrain `e_phoff`'s location — kernel
    loaders read it directly to find the program headers.  Modern
    kernels (post-2022) accept arbitrary phoff; older kernels had
    a bug requiring phoff near the file start.  C++ patchelf accepts
    the older-kernel breakage as the price of generality. -/
def growEOFWithFreshPtLoadReloc (pageSize? : Option Nat) (e : ElfFile) : ElfFile :=
  let detectedAlign := maxPtLoadAlign e.phdrs
  let alignStartPage :=
    match pageSize? with
    | some n => max n detectedAlign
    | none   => detectedAlign
  let startPage := roundUp (maxPtLoadVaddrEnd e.phdrs) alignStartPage
  let startOffset := roundUp (currentFileEnd e) alignStartPage
  let phtSize := (e.phdrs.size + 1) * Layout.phdrSize
  -- Place stale sections starting AFTER the relocated phdr table.
  let secStartOffset := startOffset + phtSize
  let secStartPage := startPage + phtSize
  let stale : Array Bool := Array.ofFn (n := e.sections.size) fun i =>
    sectionStale e i.val i.isLt
  let placed := appendStaleSections e.sections stale secStartOffset secStartPage
  let newSections := placed.1
  let appendedBytes := placed.2
  let totalAppendBytes := phtSize + appendedBytes
  let newShoff := roundUp (startOffset + totalAppendBytes) 8
  -- Retarget PT_INTERP / PT_DYNAMIC for moved sections, then PT_PHDR
  -- to point at the relocated phdr table.
  let retargetedPhdrs := updatePhdrsAfterMove e.phdrs none 0 0
                        e.interpIdx e.dynamicIdx newSections
  let phdrRetargeted := retargetPtPhdr retargetedPhdrs startOffset startPage phtSize
  -- Append the new PT_LOAD covering both the relocated phdrs and the
  -- moved sections.
  let newPhdrs := phdrRetargeted.push
    (freshPtLoad startOffset startPage totalAppendBytes alignStartPage)
  let newHeader : Patchelf.Elf.ElfHeader :=
    { e.header with phoff := ⟨startOffset⟩
                  , shoff := ⟨newShoff⟩
                  , phnum := (e.phdrs.size + 1).toUInt16 }
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

/-! ## `growEOFWithMainBody` field projections

    Lift the `appendStaleSections_*` corollaries to the full
    `growEOFWithMainBody` output.  The output's `sections` field IS
    `appendStaleSections.1`; its `header.{phnum, shnum, shstrndx}`
    are unchanged from the input. -/

@[simp] theorem growEOFWithMainBody_sections_size
    (pageSize? : Option Nat) (e : ElfFile) (lastIdx : Nat) :
    (growEOFWithMainBody pageSize? e lastIdx).sections.size = e.sections.size := by
  unfold growEOFWithMainBody
  exact PlaceFold.size_eq _ _

@[simp] theorem growEOFWithMainBody_header_phnum
    (pageSize? : Option Nat) (e : ElfFile) (lastIdx : Nat) :
    (growEOFWithMainBody pageSize? e lastIdx).header.phnum = e.header.phnum := by
  unfold growEOFWithMainBody; rfl

@[simp] theorem growEOFWithMainBody_header_shnum
    (pageSize? : Option Nat) (e : ElfFile) (lastIdx : Nat) :
    (growEOFWithMainBody pageSize? e lastIdx).header.shnum = e.header.shnum := by
  unfold growEOFWithMainBody; rfl

@[simp] theorem growEOFWithMainBody_header_shstrndx
    (pageSize? : Option Nat) (e : ElfFile) (lastIdx : Nat) :
    (growEOFWithMainBody pageSize? e lastIdx).header.shstrndx = e.header.shstrndx := by
  unfold growEOFWithMainBody; rfl

@[simp] theorem growEOFWithMainBody_header_phentsize
    (pageSize? : Option Nat) (e : ElfFile) (lastIdx : Nat) :
    (growEOFWithMainBody pageSize? e lastIdx).header.phentsize = e.header.phentsize := by
  unfold growEOFWithMainBody; rfl

@[simp] theorem growEOFWithMainBody_header_shentsize
    (pageSize? : Option Nat) (e : ElfFile) (lastIdx : Nat) :
    (growEOFWithMainBody pageSize? e lastIdx).header.shentsize = e.header.shentsize := by
  unfold growEOFWithMainBody; rfl

@[simp] theorem growEOFWithMainBody_phdrs_size
    (pageSize? : Option Nat) (e : ElfFile) (lastIdx : Nat) :
    (growEOFWithMainBody pageSize? e lastIdx).phdrs.size = e.phdrs.size := by
  unfold growEOFWithMainBody updatePhdrsAfterMove
  exact Array.size_mapIdx

/-- Per-section name preservation lifted to `growEOFWithMainBody`. -/
theorem growEOFWithMainBody_sections_name
    (pageSize? : Option Nat) (e : ElfFile) (lastIdx : Nat) (j : Nat)
    (hj : j < (growEOFWithMainBody pageSize? e lastIdx).sections.size)
    (hjE : j < e.sections.size) :
    ((growEOFWithMainBody pageSize? e lastIdx).sections[j]'hj).name
      = (e.sections[j]'hjE).name := by
  unfold growEOFWithMainBody at hj ⊢
  exact appendStaleSections_name _ _ _ _ j hj hjE

/-- Per-section type preservation. -/
theorem growEOFWithMainBody_sections_type
    (pageSize? : Option Nat) (e : ElfFile) (lastIdx : Nat) (j : Nat)
    (hj : j < (growEOFWithMainBody pageSize? e lastIdx).sections.size)
    (hjE : j < e.sections.size) :
    ((growEOFWithMainBody pageSize? e lastIdx).sections[j]'hj).type
      = (e.sections[j]'hjE).type := by
  unfold growEOFWithMainBody at hj ⊢
  exact appendStaleSections_type _ _ _ _ j hj hjE

/-- Per-section content preservation. -/
theorem growEOFWithMainBody_sections_content
    (pageSize? : Option Nat) (e : ElfFile) (lastIdx : Nat) (j : Nat)
    (hj : j < (growEOFWithMainBody pageSize? e lastIdx).sections.size)
    (hjE : j < e.sections.size) :
    ((growEOFWithMainBody pageSize? e lastIdx).sections[j]'hj).content
      = (e.sections[j]'hjE).content := by
  unfold growEOFWithMainBody at hj ⊢
  exact appendStaleSections_content _ _ _ _ j hj hjE

/-- `growEOFWithMainBody` preserves `findUniqueTypeIdx` for every type
    (since per-section types are preserved + sections.size unchanged). -/
theorem growEOFWithMainBody_findUniqueTypeIdx
    (pageSize? : Option Nat) (e : ElfFile) (lastIdx : Nat) (ty : ShType) :
    (growEOFWithMainBody pageSize? e lastIdx).findUniqueTypeIdx ty
      = e.findUniqueTypeIdx ty := by
  apply ElfFile.firstIdxWhereIn_congr
  · exact growEOFWithMainBody_sections_size _ _ _
  · intros k hk hk'
    have := growEOFWithMainBody_sections_type pageSize? e lastIdx k hk hk'
    simp [this]

/-- `growEOFWithMainBody` preserves `dynamicIdx`. -/
@[simp] theorem growEOFWithMainBody_dynamicIdx
    (pageSize? : Option Nat) (e : ElfFile) (lastIdx : Nat) :
    (growEOFWithMainBody pageSize? e lastIdx).dynamicIdx = e.dynamicIdx :=
  growEOFWithMainBody_findUniqueTypeIdx pageSize? e lastIdx ShType.SHT_DYNAMIC

/-- `growEOFWithMainBody` preserves `dynsymIdx`. -/
@[simp] theorem growEOFWithMainBody_dynsymIdx
    (pageSize? : Option Nat) (e : ElfFile) (lastIdx : Nat) :
    (growEOFWithMainBody pageSize? e lastIdx).dynsymIdx = e.dynsymIdx :=
  growEOFWithMainBody_findUniqueTypeIdx pageSize? e lastIdx ShType.SHT_DYNSYM

/-- `growEOFWithMainBody` preserves `contentAt` for any optional index. -/
theorem growEOFWithMainBody_contentAt
    (pageSize? : Option Nat) (e : ElfFile) (lastIdx : Nat) (i? : Option Nat) :
    (growEOFWithMainBody pageSize? e lastIdx).contentAt i? = e.contentAt i? := by
  unfold ElfFile.contentAt
  cases i? with
  | none => rfl
  | some i =>
    simp only [Option.bind_some]
    by_cases hi : i < e.sections.size
    · have hi' : i < (growEOFWithMainBody pageSize? e lastIdx).sections.size :=
        (growEOFWithMainBody_sections_size pageSize? e lastIdx).symm ▸ hi
      rw [dif_pos hi', dif_pos hi]
      rw [growEOFWithMainBody_sections_content pageSize? e lastIdx i hi' hi]
    · have hi' : ¬ i < (growEOFWithMainBody pageSize? e lastIdx).sections.size := by
        intro h; exact hi ((growEOFWithMainBody_sections_size pageSize? e lastIdx).symm ▸ h)
      rw [dif_neg hi', dif_neg hi]

/-- `growEOFWithMainBody` preserves `dynamic`. -/
@[simp] theorem growEOFWithMainBody_dynamic
    (pageSize? : Option Nat) (e : ElfFile) (lastIdx : Nat) :
    (growEOFWithMainBody pageSize? e lastIdx).dynamic = e.dynamic := by
  unfold ElfFile.dynamic
  rw [growEOFWithMainBody_dynamicIdx, growEOFWithMainBody_contentAt]

/-- `growEOFWithMainBody` preserves `dynsym`. -/
@[simp] theorem growEOFWithMainBody_dynsym
    (pageSize? : Option Nat) (e : ElfFile) (lastIdx : Nat) :
    (growEOFWithMainBody pageSize? e lastIdx).dynsym = e.dynsym := by
  unfold ElfFile.dynsym
  rw [growEOFWithMainBody_dynsymIdx, growEOFWithMainBody_contentAt]

/-- `growEOFWithMainBody` preserves `shstrtab`. -/
@[simp] theorem growEOFWithMainBody_shstrtab
    (pageSize? : Option Nat) (e : ElfFile) (lastIdx : Nat) :
    (growEOFWithMainBody pageSize? e lastIdx).shstrtab = e.shstrtab := by
  unfold ElfFile.shstrtab
  rw [growEOFWithMainBody_header_shstrndx]
  by_cases hSh : e.header.shstrndx.toNat < e.sections.size
  · have hSh' : e.header.shstrndx.toNat
                  < (growEOFWithMainBody pageSize? e lastIdx).sections.size :=
      (growEOFWithMainBody_sections_size pageSize? e lastIdx).symm ▸ hSh
    rw [dif_pos hSh', dif_pos hSh]
    rw [growEOFWithMainBody_sections_content pageSize? e lastIdx _ hSh' hSh]
  · have hSh' : ¬ e.header.shstrndx.toNat
                   < (growEOFWithMainBody pageSize? e lastIdx).sections.size := by
      intro h; exact hSh ((growEOFWithMainBody_sections_size pageSize? e lastIdx).symm ▸ h)
    rw [dif_neg hSh', dif_neg hSh]

/-- `growEOFWithMainBody` preserves `findIdxByName` (since shstrtab and
    per-section names are both preserved). -/
theorem growEOFWithMainBody_findIdxByName
    (pageSize? : Option Nat) (e : ElfFile) (lastIdx : Nat) (name : ByteArray) :
    (growEOFWithMainBody pageSize? e lastIdx).findIdxByName name
      = e.findIdxByName name := by
  unfold ElfFile.findIdxByName
  rw [growEOFWithMainBody_shstrtab]
  cases e.shstrtab with
  | none => rfl
  | some st =>
    apply ElfFile.firstIdxWhereIn_congr
    · exact growEOFWithMainBody_sections_size _ _ _
    · intros k hk hk'
      have := growEOFWithMainBody_sections_name pageSize? e lastIdx k hk hk'
      simp [this]

/-- `growEOFWithMainBody` preserves `dynstrIdx`. -/
@[simp] theorem growEOFWithMainBody_dynstrIdx
    (pageSize? : Option Nat) (e : ElfFile) (lastIdx : Nat) :
    (growEOFWithMainBody pageSize? e lastIdx).dynstrIdx = e.dynstrIdx :=
  growEOFWithMainBody_findIdxByName pageSize? e lastIdx _

/-- `growEOFWithMainBody` preserves `dynstr`. -/
@[simp] theorem growEOFWithMainBody_dynstr
    (pageSize? : Option Nat) (e : ElfFile) (lastIdx : Nat) :
    (growEOFWithMainBody pageSize? e lastIdx).dynstr = e.dynstr := by
  unfold ElfFile.dynstr
  rw [growEOFWithMainBody_dynstrIdx, growEOFWithMainBody_contentAt]

/-- `growEOFWithMainBody` preserves byte-layer `IsValid`.

    All 8 IsValid clauses depend only on per-section (name, type,
    content) plus header counts (phnum, shnum, etc.) — none on
    `(offset, addr)`.  `growEOFWithMainBody` mutates `header.shoff`
    and per-section `(offset, addr)` only; phnum / shnum /
    sections.size / phdrs.size are all preserved.  The proof
    dispatches each clause via the `growEOFWithMainBody_*` accessor-
    preservation lemmas above. -/
theorem growEOFWithMainBody_preserves_valid
    (pageSize? : Option Nat) (e : ElfFile) (lastIdx : Nat)
    (hVal : e.IsValid) :
    (growEOFWithMainBody pageSize? e lastIdx).IsValid := by
  refine
    { header_counts := ?_, sections_wf := ?_, strtabs_wf := ?_,
      dynamic_wf := ?_, dynsym_wf := ?_, content_wf := ?_,
      types_distinct := ?_, names_unique := ?_ }
  ----------------------------------------
  -- header_counts: phnum/shnum/etc. unchanged.
  ----------------------------------------
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hVal.header_counts
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [growEOFWithMainBody_header_phnum, growEOFWithMainBody_phdrs_size]; exact h1
    · rw [growEOFWithMainBody_header_shnum, growEOFWithMainBody_sections_size]; exact h2
    · rw [growEOFWithMainBody_header_phentsize]; exact h3
    · rw [growEOFWithMainBody_header_shentsize]; exact h4
    · rw [growEOFWithMainBody_header_shstrndx, growEOFWithMainBody_sections_size]; exact h5
  ----------------------------------------
  -- sections_wf: section[0].type = SHT_NULL.  Type preserved at index 0.
  ----------------------------------------
  · intro h0
    have h0' : 0 < e.sections.size :=
      (growEOFWithMainBody_sections_size pageSize? e lastIdx) ▸ h0
    rw [growEOFWithMainBody_sections_type pageSize? e lastIdx 0 h0 h0']
    exact hVal.sections_wf h0'
  ----------------------------------------
  -- strtabs_wf: per-section strtab predicate; depends on content only.
  ----------------------------------------
  · have hAll := hVal.strtabs_wf
    show (growEOFWithMainBody pageSize? e lastIdx).sections.all _ = true
    unfold ElfFile.strtabsWellFormed at hAll
    rw [Array.all_eq_true] at hAll ⊢
    intro j hj
    have hjE : j < e.sections.size :=
      (growEOFWithMainBody_sections_size pageSize? e lastIdx) ▸ hj
    show ElfFile.Section.strtabWellFormedB
            ((growEOFWithMainBody pageSize? e lastIdx).sections[j]'hj) = true
    have : ElfFile.Section.strtabWellFormedB
              ((growEOFWithMainBody pageSize? e lastIdx).sections[j]'hj)
         = ElfFile.Section.strtabWellFormedB (e.sections[j]'hjE) := by
      unfold ElfFile.Section.strtabWellFormedB
      rw [growEOFWithMainBody_sections_content pageSize? e lastIdx j hj hjE]
    rw [this]
    exact hAll j hjE
  ----------------------------------------
  -- dynamic_wf: depends on .dynamic and .dynstr; both preserved.
  ----------------------------------------
  · refine ⟨?_, ?_⟩
    · intro dyn hd
      rw [growEOFWithMainBody_dynamic] at hd
      exact hVal.dynamic_wf.1 dyn hd
    · intros dyn ds hd hds
      rw [growEOFWithMainBody_dynamic] at hd
      rw [growEOFWithMainBody_dynstr] at hds
      exact hVal.dynamic_wf.2 dyn ds hd hds
  ----------------------------------------
  -- dynsym_wf: depends on .dynsym and .dynstr; both preserved.
  ----------------------------------------
  · intros syms ds hSyms hDs
    rw [growEOFWithMainBody_dynsym] at hSyms
    rw [growEOFWithMainBody_dynstr] at hDs
    exact hVal.dynsym_wf syms ds hSyms hDs
  ----------------------------------------
  -- content_wf: per-section content predicate.
  ----------------------------------------
  · have hAll := hVal.content_wf
    show (growEOFWithMainBody pageSize? e lastIdx).sections.all _ = true
    unfold ElfFile.sectionsContentWellFormed at hAll
    rw [Array.all_eq_true] at hAll ⊢
    intro j hj
    have hjE : j < e.sections.size :=
      (growEOFWithMainBody_sections_size pageSize? e lastIdx) ▸ hj
    show ElfFile.Section.contentWellFormedB
            ((growEOFWithMainBody pageSize? e lastIdx).sections[j]'hj) = true
    have : ElfFile.Section.contentWellFormedB
              ((growEOFWithMainBody pageSize? e lastIdx).sections[j]'hj)
         = ElfFile.Section.contentWellFormedB (e.sections[j]'hjE) := by
      unfold ElfFile.Section.contentWellFormedB
      rw [growEOFWithMainBody_sections_content pageSize? e lastIdx j hj hjE]
    rw [this]
    exact hAll j hjE
  ----------------------------------------
  -- types_distinct: per-type uniqueness; types preserved.
  ----------------------------------------
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hVal.types_distinct
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> {
      intros i hi j hj hi_t hj_t
      have hiE : i < e.sections.size :=
        (growEOFWithMainBody_sections_size pageSize? e lastIdx) ▸ hi
      have hjE : j < e.sections.size :=
        (growEOFWithMainBody_sections_size pageSize? e lastIdx) ▸ hj
      rw [growEOFWithMainBody_sections_type pageSize? e lastIdx i hi hiE] at hi_t
      rw [growEOFWithMainBody_sections_type pageSize? e lastIdx j hj hjE] at hj_t
      first
      | exact h1 i hiE j hjE hi_t hj_t
      | exact h2 i hiE j hjE hi_t hj_t
      | exact h3 i hiE j hjE hi_t hj_t
      | exact h4 i hiE j hjE hi_t hj_t
      | exact h5 i hiE j hjE hi_t hj_t
      | exact h6 i hiE j hjE hi_t hj_t
    }
  ----------------------------------------
  -- names_unique: shstrtab + per-section name; both preserved.
  ----------------------------------------
  · unfold ElfFile.namedSectionsUnique
    rw [growEOFWithMainBody_shstrtab]
    cases hSt : e.shstrtab with
    | none => trivial
    | some st =>
        obtain ⟨h1, h2⟩ := by
          have := hVal.names_unique
          unfold ElfFile.namedSectionsUnique at this
          rw [hSt] at this; exact this
        constructor <;> {
          intros i hi j hj hi_n hj_n
          have hiE : i < e.sections.size :=
            (growEOFWithMainBody_sections_size pageSize? e lastIdx) ▸ hi
          have hjE : j < e.sections.size :=
            (growEOFWithMainBody_sections_size pageSize? e lastIdx) ▸ hj
          rw [growEOFWithMainBody_sections_name pageSize? e lastIdx i hi hiE] at hi_n
          rw [growEOFWithMainBody_sections_name pageSize? e lastIdx j hj hjE] at hj_n
          first
          | exact h1 i hiE j hjE hi_n hj_n
          | exact h2 i hiE j hjE hi_n hj_n
        }

/-! ## `growEOFWithFreshPtLoad` field projections and preserves_valid -/

@[simp] theorem growEOFWithFreshPtLoad_sections_size
    (pageSize? : Option Nat) (e : ElfFile) :
    (growEOFWithFreshPtLoad pageSize? e).sections.size = e.sections.size := by
  unfold growEOFWithFreshPtLoad
  exact PlaceFold.size_eq _ _

@[simp] theorem growEOFWithFreshPtLoad_header_phnum
    (pageSize? : Option Nat) (e : ElfFile) :
    (growEOFWithFreshPtLoad pageSize? e).header.phnum
      = (e.phdrs.size + 1).toUInt16 := by
  unfold growEOFWithFreshPtLoad; rfl

@[simp] theorem growEOFWithFreshPtLoad_header_shnum
    (pageSize? : Option Nat) (e : ElfFile) :
    (growEOFWithFreshPtLoad pageSize? e).header.shnum = e.header.shnum := by
  unfold growEOFWithFreshPtLoad; rfl

@[simp] theorem growEOFWithFreshPtLoad_header_shstrndx
    (pageSize? : Option Nat) (e : ElfFile) :
    (growEOFWithFreshPtLoad pageSize? e).header.shstrndx = e.header.shstrndx := by
  unfold growEOFWithFreshPtLoad; rfl

@[simp] theorem growEOFWithFreshPtLoad_header_phentsize
    (pageSize? : Option Nat) (e : ElfFile) :
    (growEOFWithFreshPtLoad pageSize? e).header.phentsize = e.header.phentsize := by
  unfold growEOFWithFreshPtLoad; rfl

@[simp] theorem growEOFWithFreshPtLoad_header_shentsize
    (pageSize? : Option Nat) (e : ElfFile) :
    (growEOFWithFreshPtLoad pageSize? e).header.shentsize = e.header.shentsize := by
  unfold growEOFWithFreshPtLoad; rfl

@[simp] theorem growEOFWithFreshPtLoad_phdrs_size
    (pageSize? : Option Nat) (e : ElfFile) :
    (growEOFWithFreshPtLoad pageSize? e).phdrs.size = e.phdrs.size + 1 := by
  unfold growEOFWithFreshPtLoad updatePhdrsAfterMove
  rw [Array.size_push, Array.size_mapIdx]

theorem growEOFWithFreshPtLoad_sections_name
    (pageSize? : Option Nat) (e : ElfFile) (j : Nat)
    (hj : j < (growEOFWithFreshPtLoad pageSize? e).sections.size)
    (hjE : j < e.sections.size) :
    ((growEOFWithFreshPtLoad pageSize? e).sections[j]'hj).name
      = (e.sections[j]'hjE).name := by
  unfold growEOFWithFreshPtLoad at hj ⊢
  exact appendStaleSections_name _ _ _ _ j hj hjE

theorem growEOFWithFreshPtLoad_sections_type
    (pageSize? : Option Nat) (e : ElfFile) (j : Nat)
    (hj : j < (growEOFWithFreshPtLoad pageSize? e).sections.size)
    (hjE : j < e.sections.size) :
    ((growEOFWithFreshPtLoad pageSize? e).sections[j]'hj).type
      = (e.sections[j]'hjE).type := by
  unfold growEOFWithFreshPtLoad at hj ⊢
  exact appendStaleSections_type _ _ _ _ j hj hjE

theorem growEOFWithFreshPtLoad_sections_content
    (pageSize? : Option Nat) (e : ElfFile) (j : Nat)
    (hj : j < (growEOFWithFreshPtLoad pageSize? e).sections.size)
    (hjE : j < e.sections.size) :
    ((growEOFWithFreshPtLoad pageSize? e).sections[j]'hj).content
      = (e.sections[j]'hjE).content := by
  unfold growEOFWithFreshPtLoad at hj ⊢
  exact appendStaleSections_content _ _ _ _ j hj hjE

theorem growEOFWithFreshPtLoad_findUniqueTypeIdx
    (pageSize? : Option Nat) (e : ElfFile) (ty : ShType) :
    (growEOFWithFreshPtLoad pageSize? e).findUniqueTypeIdx ty
      = e.findUniqueTypeIdx ty := by
  apply ElfFile.firstIdxWhereIn_congr
  · exact growEOFWithFreshPtLoad_sections_size _ _
  · intros k hk hk'
    have := growEOFWithFreshPtLoad_sections_type pageSize? e k hk hk'
    simp [this]

@[simp] theorem growEOFWithFreshPtLoad_dynamicIdx
    (pageSize? : Option Nat) (e : ElfFile) :
    (growEOFWithFreshPtLoad pageSize? e).dynamicIdx = e.dynamicIdx :=
  growEOFWithFreshPtLoad_findUniqueTypeIdx pageSize? e ShType.SHT_DYNAMIC

@[simp] theorem growEOFWithFreshPtLoad_dynsymIdx
    (pageSize? : Option Nat) (e : ElfFile) :
    (growEOFWithFreshPtLoad pageSize? e).dynsymIdx = e.dynsymIdx :=
  growEOFWithFreshPtLoad_findUniqueTypeIdx pageSize? e ShType.SHT_DYNSYM

theorem growEOFWithFreshPtLoad_contentAt
    (pageSize? : Option Nat) (e : ElfFile) (i? : Option Nat) :
    (growEOFWithFreshPtLoad pageSize? e).contentAt i? = e.contentAt i? := by
  unfold ElfFile.contentAt
  cases i? with
  | none => rfl
  | some i =>
    simp only [Option.bind_some]
    by_cases hi : i < e.sections.size
    · have hi' : i < (growEOFWithFreshPtLoad pageSize? e).sections.size :=
        (growEOFWithFreshPtLoad_sections_size pageSize? e).symm ▸ hi
      rw [dif_pos hi', dif_pos hi]
      rw [growEOFWithFreshPtLoad_sections_content pageSize? e i hi' hi]
    · have hi' : ¬ i < (growEOFWithFreshPtLoad pageSize? e).sections.size := by
        intro h; exact hi ((growEOFWithFreshPtLoad_sections_size pageSize? e).symm ▸ h)
      rw [dif_neg hi', dif_neg hi]

@[simp] theorem growEOFWithFreshPtLoad_dynamic
    (pageSize? : Option Nat) (e : ElfFile) :
    (growEOFWithFreshPtLoad pageSize? e).dynamic = e.dynamic := by
  unfold ElfFile.dynamic
  rw [growEOFWithFreshPtLoad_dynamicIdx, growEOFWithFreshPtLoad_contentAt]

@[simp] theorem growEOFWithFreshPtLoad_dynsym
    (pageSize? : Option Nat) (e : ElfFile) :
    (growEOFWithFreshPtLoad pageSize? e).dynsym = e.dynsym := by
  unfold ElfFile.dynsym
  rw [growEOFWithFreshPtLoad_dynsymIdx, growEOFWithFreshPtLoad_contentAt]

@[simp] theorem growEOFWithFreshPtLoad_shstrtab
    (pageSize? : Option Nat) (e : ElfFile) :
    (growEOFWithFreshPtLoad pageSize? e).shstrtab = e.shstrtab := by
  unfold ElfFile.shstrtab
  rw [growEOFWithFreshPtLoad_header_shstrndx]
  by_cases hSh : e.header.shstrndx.toNat < e.sections.size
  · have hSh' : e.header.shstrndx.toNat
                  < (growEOFWithFreshPtLoad pageSize? e).sections.size :=
      (growEOFWithFreshPtLoad_sections_size pageSize? e).symm ▸ hSh
    rw [dif_pos hSh', dif_pos hSh]
    rw [growEOFWithFreshPtLoad_sections_content pageSize? e _ hSh' hSh]
  · have hSh' : ¬ e.header.shstrndx.toNat
                   < (growEOFWithFreshPtLoad pageSize? e).sections.size := by
      intro h; exact hSh ((growEOFWithFreshPtLoad_sections_size pageSize? e).symm ▸ h)
    rw [dif_neg hSh', dif_neg hSh]

theorem growEOFWithFreshPtLoad_findIdxByName
    (pageSize? : Option Nat) (e : ElfFile) (name : ByteArray) :
    (growEOFWithFreshPtLoad pageSize? e).findIdxByName name
      = e.findIdxByName name := by
  unfold ElfFile.findIdxByName
  rw [growEOFWithFreshPtLoad_shstrtab]
  cases e.shstrtab with
  | none => rfl
  | some st =>
    apply ElfFile.firstIdxWhereIn_congr
    · exact growEOFWithFreshPtLoad_sections_size _ _
    · intros k hk hk'
      have := growEOFWithFreshPtLoad_sections_name pageSize? e k hk hk'
      simp [this]

@[simp] theorem growEOFWithFreshPtLoad_dynstrIdx
    (pageSize? : Option Nat) (e : ElfFile) :
    (growEOFWithFreshPtLoad pageSize? e).dynstrIdx = e.dynstrIdx :=
  growEOFWithFreshPtLoad_findIdxByName pageSize? e _

@[simp] theorem growEOFWithFreshPtLoad_dynstr
    (pageSize? : Option Nat) (e : ElfFile) :
    (growEOFWithFreshPtLoad pageSize? e).dynstr = e.dynstr := by
  unfold ElfFile.dynstr
  rw [growEOFWithFreshPtLoad_dynstrIdx, growEOFWithFreshPtLoad_contentAt]

/-- `growEOFWithFreshPtLoad` preserves byte-layer `IsValid`, given a
    bound on `phdrs.size + 1` (so the bumped phnum survives the
    `UInt16` round-trip).  The bound `(e.phdrs.size + 1) < UInt16.size`
    is satisfied by every real ELF (phnum is at most a few dozen). -/
theorem growEOFWithFreshPtLoad_preserves_valid
    (pageSize? : Option Nat) (e : ElfFile)
    (hVal : e.IsValid)
    (hPhdrFit : (e.phdrs.size + 1) < UInt16.size) :
    (growEOFWithFreshPtLoad pageSize? e).IsValid := by
  refine
    { header_counts := ?_, sections_wf := ?_, strtabs_wf := ?_,
      dynamic_wf := ?_, dynsym_wf := ?_, content_wf := ?_,
      types_distinct := ?_, names_unique := ?_ }
  ----------------------------------------
  -- header_counts: phnum bumped, shnum/etc. unchanged.
  ----------------------------------------
  · obtain ⟨_, h2, h3, h4, h5⟩ := hVal.header_counts
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- phnum.toNat = phdrs.size = e.phdrs.size + 1.
      rw [growEOFWithFreshPtLoad_header_phnum, growEOFWithFreshPtLoad_phdrs_size]
      -- (e.phdrs.size + 1).toUInt16.toNat = e.phdrs.size + 1 (given hPhdrFit).
      show (e.phdrs.size + 1).toUInt16.toNat = e.phdrs.size + 1
      -- For n < 2^16, (n.toUInt16.toNat) = n.  Standard mod-reduction.
      unfold Nat.toUInt16 UInt16.toNat
      simp only [UInt16.ofNat]
      -- Goal reduces to (e.phdrs.size + 1) % 2^16 = e.phdrs.size + 1.
      exact Nat.mod_eq_of_lt hPhdrFit
    · rw [growEOFWithFreshPtLoad_header_shnum, growEOFWithFreshPtLoad_sections_size]; exact h2
    · rw [growEOFWithFreshPtLoad_header_phentsize]; exact h3
    · rw [growEOFWithFreshPtLoad_header_shentsize]; exact h4
    · rw [growEOFWithFreshPtLoad_header_shstrndx, growEOFWithFreshPtLoad_sections_size]; exact h5
  ----------------------------------------
  -- sections_wf, strtabs_wf, dynamic_wf, dynsym_wf, content_wf,
  -- types_distinct, names_unique: identical structure to main-body proof.
  ----------------------------------------
  · intro h0
    have h0' : 0 < e.sections.size :=
      (growEOFWithFreshPtLoad_sections_size pageSize? e) ▸ h0
    rw [growEOFWithFreshPtLoad_sections_type pageSize? e 0 h0 h0']
    exact hVal.sections_wf h0'
  · have hAll := hVal.strtabs_wf
    show (growEOFWithFreshPtLoad pageSize? e).sections.all _ = true
    unfold ElfFile.strtabsWellFormed at hAll
    rw [Array.all_eq_true] at hAll ⊢
    intro j hj
    have hjE : j < e.sections.size :=
      (growEOFWithFreshPtLoad_sections_size pageSize? e) ▸ hj
    show ElfFile.Section.strtabWellFormedB
            ((growEOFWithFreshPtLoad pageSize? e).sections[j]'hj) = true
    have : ElfFile.Section.strtabWellFormedB
              ((growEOFWithFreshPtLoad pageSize? e).sections[j]'hj)
         = ElfFile.Section.strtabWellFormedB (e.sections[j]'hjE) := by
      unfold ElfFile.Section.strtabWellFormedB
      rw [growEOFWithFreshPtLoad_sections_content pageSize? e j hj hjE]
    rw [this]; exact hAll j hjE
  · refine ⟨?_, ?_⟩
    · intro dyn hd
      rw [growEOFWithFreshPtLoad_dynamic] at hd
      exact hVal.dynamic_wf.1 dyn hd
    · intros dyn ds hd hds
      rw [growEOFWithFreshPtLoad_dynamic] at hd
      rw [growEOFWithFreshPtLoad_dynstr] at hds
      exact hVal.dynamic_wf.2 dyn ds hd hds
  · intros syms ds hSyms hDs
    rw [growEOFWithFreshPtLoad_dynsym] at hSyms
    rw [growEOFWithFreshPtLoad_dynstr] at hDs
    exact hVal.dynsym_wf syms ds hSyms hDs
  · have hAll := hVal.content_wf
    show (growEOFWithFreshPtLoad pageSize? e).sections.all _ = true
    unfold ElfFile.sectionsContentWellFormed at hAll
    rw [Array.all_eq_true] at hAll ⊢
    intro j hj
    have hjE : j < e.sections.size :=
      (growEOFWithFreshPtLoad_sections_size pageSize? e) ▸ hj
    show ElfFile.Section.contentWellFormedB
            ((growEOFWithFreshPtLoad pageSize? e).sections[j]'hj) = true
    have : ElfFile.Section.contentWellFormedB
              ((growEOFWithFreshPtLoad pageSize? e).sections[j]'hj)
         = ElfFile.Section.contentWellFormedB (e.sections[j]'hjE) := by
      unfold ElfFile.Section.contentWellFormedB
      rw [growEOFWithFreshPtLoad_sections_content pageSize? e j hj hjE]
    rw [this]; exact hAll j hjE
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hVal.types_distinct
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> {
      intros i hi j hj hi_t hj_t
      have hiE : i < e.sections.size :=
        (growEOFWithFreshPtLoad_sections_size pageSize? e) ▸ hi
      have hjE : j < e.sections.size :=
        (growEOFWithFreshPtLoad_sections_size pageSize? e) ▸ hj
      rw [growEOFWithFreshPtLoad_sections_type pageSize? e i hi hiE] at hi_t
      rw [growEOFWithFreshPtLoad_sections_type pageSize? e j hj hjE] at hj_t
      first
      | exact h1 i hiE j hjE hi_t hj_t
      | exact h2 i hiE j hjE hi_t hj_t
      | exact h3 i hiE j hjE hi_t hj_t
      | exact h4 i hiE j hjE hi_t hj_t
      | exact h5 i hiE j hjE hi_t hj_t
      | exact h6 i hiE j hjE hi_t hj_t
    }
  · unfold ElfFile.namedSectionsUnique
    rw [growEOFWithFreshPtLoad_shstrtab]
    cases hSt : e.shstrtab with
    | none => trivial
    | some st =>
        obtain ⟨h1, h2⟩ := by
          have := hVal.names_unique
          unfold ElfFile.namedSectionsUnique at this
          rw [hSt] at this; exact this
        constructor <;> {
          intros i hi j hj hi_n hj_n
          have hiE : i < e.sections.size :=
            (growEOFWithFreshPtLoad_sections_size pageSize? e) ▸ hi
          have hjE : j < e.sections.size :=
            (growEOFWithFreshPtLoad_sections_size pageSize? e) ▸ hj
          rw [growEOFWithFreshPtLoad_sections_name pageSize? e i hi hiE] at hi_n
          rw [growEOFWithFreshPtLoad_sections_name pageSize? e j hj hjE] at hj_n
          first
          | exact h1 i hiE j hjE hi_n hj_n
          | exact h2 i hiE j hjE hi_n hj_n
        }

/-- The fresh-PT_LOAD construction satisfies `spliceRegionsDisjoint`,
    given the input's structural input invariants AND
    `canAddFreshPtLoad` (which witnesses room for one more phdr in the
    in-place layout).  Mirror of
    `growEOFWithMainBody_produces_spliceRegionsDisjoint` with one
    extra precondition (`hCan : canAddFreshPtLoad e = true`); the
    difference shows up in `hdr_phdr_disjoint`, `phdr_shdr_disjoint`,
    and `phdr_sec_disjoint`, where the output's phdr-table region is
    `(e.phdrs.size + 1) * phdrSize` bytes (not `e.phdrs.size *
    phdrSize`). -/
theorem growEOFWithFreshPtLoad_produces_spliceRegionsDisjoint
    (pageSize? : Option Nat) (e : ElfFile)
    (hCan : canAddFreshPtLoad e = true)
    (hHeaderSec  : e.headerSectionDisjoint) :
    (growEOFWithFreshPtLoad pageSize? e).spliceRegionsDisjoint := by
  unfold growEOFWithFreshPtLoad
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
  -- Witnesses (same as main-body proof).
  have hSpec : PlaceFold.TransformSpec (appendTransform startOffset startPage) startOffset :=
    appendTransform_transformSpec _ _
  have hCurrLeStart : currentFileEnd e ≤ startOffset := le_roundUp _ _
  have hStaleEq : ∀ (i : Nat) (hi : i < e.sections.size),
      stale[i]?.getD false = sectionStale e i hi :=
    fun i hi => stale_ofFn_eq_sectionStale e i hi
  have hVerb : PlaceFold.VerbatimWitness (appendVerbatim stale) startOffset e.sections :=
    appendVerbatim_witness e startOffset hCurrLeStart stale hStaleEq
  have hSizeEq : newSections.size = e.sections.size :=
    PlaceFold.size_eq _ _
  have hCursorFloor : (0 : Nat) ≤ appendedBytes := PlaceFold.cursor_floor _ _
  have hStartLeShoff : startOffset ≤ newShoff :=
    Nat.le_trans (Nat.le_add_right _ _) (le_roundUp _ _)
  have hEndLeShoff : startOffset + appendedBytes ≤ newShoff := le_roundUp _ _
  have hEhdrLe : Layout.ehdrSize ≤ startOffset :=
    Nat.le_trans (currentFileEnd_ge_ehdr e) hCurrLeStart
  -- canAddFreshPtLoad extractions.
  have hEhdrLePh : Layout.ehdrSize ≤ e.header.phoff.val :=
    canAddFreshPtLoad_ehdrSize_le_phoff e hCan
  have hExtPhEndLe : e.header.phoff.val + (e.phdrs.size + 1) * Layout.phdrSize ≤ currentFileEnd e :=
    canAddFreshPtLoad_newPhEnd_le_currentFileEnd e hCan
  have hExtPhEndLeShoff :
      e.header.phoff.val + (e.phdrs.size + 1) * Layout.phdrSize ≤ newShoff :=
    Nat.le_trans hExtPhEndLe (Nat.le_trans hCurrLeStart hStartLeShoff)
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
  -- The output's phdr count: retargetedPhdrs.size = e.phdrs.size, then push adds 1.
  have hRetSize : (updatePhdrsAfterMove e.phdrs none 0 0
                  e.interpIdx e.dynamicIdx newSections).size = e.phdrs.size := by
    unfold updatePhdrsAfterMove
    exact Array.size_mapIdx
  have hOutPhdrsSize :
      ((updatePhdrsAfterMove e.phdrs none 0 0
        e.interpIdx e.dynamicIdx newSections).push
        (freshPtLoad startOffset startPage appendedBytes alignStartPage)).size
        = e.phdrs.size + 1 := by
    rw [Array.size_push]; rw [hRetSize]
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
  · -- hdr_phdr_disjoint: phoff unchanged; phdrs.size = e.phdrs.size + 1.
    show IntervalDisjoint 0 Layout.ehdrSize e.header.phoff.val
      (e.header.phoff.val + _ * Layout.phdrSize)
    rw [hOutPhdrsSize]
    -- phoff ≥ ehdrSize (from canAddFreshPtLoad).
    exact Or.inl hEhdrLePh
  · -- hdr_shdr_disjoint: newShoff ≥ ehdrSize.
    show IntervalDisjoint 0 Layout.ehdrSize _ _
    refine Or.inl ?_
    show Layout.ehdrSize ≤ newShoff
    exact Nat.le_trans hEhdrLe hStartLeShoff
  · -- phdr_shdr_disjoint: extended phdr table ends ≤ newShoff.
    show IntervalDisjoint e.header.phoff.val _ _ _
    rw [hOutPhdrsSize]
    refine Or.inl ?_
    show e.header.phoff.val + (e.phdrs.size + 1) * Layout.phdrSize ≤ newShoff
    exact hExtPhEndLeShoff
  · -- hdr_sec_disjoint: same as main-body.
    intros j hj
    have hjN : j < newSections.size := hj
    have hPl := hPlacement j hjN
    rcases hPl.offset_or with hVerbJ | hPlace
    · have hjS : j < e.sections.size := hSizeEq ▸ hjN
      rcases hHeaderSec j hjS with h | h | hID
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
      show Layout.ehdrSize ≤ (newSections[j]'hjN).offset.val
      have : startOffset + 0 ≤ (newSections[j]'hjN).offset.val := hPlace.2.1
      omega
  · -- phdr_sec_disjoint: extended phdr region disjoint from each section.
    -- Verbatim sections: combine canAddFreshPtLoad_pair_disjoint with placement.
    -- Placed sections: section.offset ≥ startOffset ≥ phdrEnd' (via canAddFreshPtLoad's
    --   extPhEnd ≤ currentFileEnd ≤ startOffset).
    intros j hj
    have hjN : j < newSections.size := hj
    have hPl := hPlacement j hjN
    show ((newSections[j]'hjN).type = _ ∨ _)
    rw [hOutPhdrsSize]
    rcases hPl.offset_or with hVerbJ | hPlace
    · have hjS : j < e.sections.size := hSizeEq ▸ hjN
      rcases canAddFreshPtLoad_pair_disjoint e hCan j hjS with h | h | hID
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
      show e.header.phoff.val + (e.phdrs.size + 1) * Layout.phdrSize ≤ (newSections[j]'hjN).offset.val
      have hOffGe : startOffset + 0 ≤ (newSections[j]'hjN).offset.val := hPlace.2.1
      have hExtLeStart : e.header.phoff.val + (e.phdrs.size + 1) * Layout.phdrSize ≤ startOffset :=
        Nat.le_trans hExtPhEndLe hCurrLeStart
      omega
  · -- shdr_sec_disjoint: same as main-body.
    intros j hj
    have hjN : j < newSections.size := hj
    have hPl := hPlacement j hjN
    rcases hPl.offset_or with hVerbJ | hPlace
    · have hjS : j < e.sections.size := hSizeEq ▸ hjN
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
    · refine Or.inr (Or.inr (Or.inr ?_))
      show (newSections[j]'hjN).offset.val + (newSections[j]'hjN).encodedSize ≤ newShoff
      have : (newSections[j]'hjN).offset.val + (newSections[j]'hjN).encodedSize
            ≤ startOffset + appendedBytes := hPlace.2.2
      omega

/-- The `relocatePht` construction satisfies `spliceRegionsDisjoint`.
    Crucially, this needs NO precondition beyond the standard structural
    input invariants — `canAddFreshPtLoad` is not required.  The reason:
    the relocated phdr table sits at `[startOffset, startOffset + phtSize)`,
    past `currentFileEnd`, so it's automatically disjoint from every
    verbatim section by `currentFileEnd_ge_section_end`.  By contrast,
    the in-place sub-case keeps the phdr table within the original file
    body and needs `canAddFreshPtLoad` to discharge phdr-vs-section
    disjointness.

    `hHeaderSec` is still needed for the `hdr_sec_disjoint` clause on
    verbatim sections (this is the standard parser-output invariant
    `headerSectionDisjoint`, independent of the layout strategy). -/
theorem growEOFWithFreshPtLoadReloc_produces_spliceRegionsDisjoint
    (pageSize? : Option Nat) (e : ElfFile)
    (hHeaderSec  : e.headerSectionDisjoint) :
    (growEOFWithFreshPtLoadReloc pageSize? e).spliceRegionsDisjoint := by
  unfold growEOFWithFreshPtLoadReloc
  let detectedAlign := maxPtLoadAlign e.phdrs
  let alignStartPage :=
    match pageSize? with
    | some n => max n detectedAlign
    | none   => detectedAlign
  let startPage := roundUp (maxPtLoadVaddrEnd e.phdrs) alignStartPage
  let startOffset := roundUp (currentFileEnd e) alignStartPage
  let phtSize := (e.phdrs.size + 1) * Layout.phdrSize
  let secStartOffset := startOffset + phtSize
  let secStartPage := startPage + phtSize
  let stale : Array Bool := Array.ofFn (n := e.sections.size) fun i =>
    sectionStale e i.val i.isLt
  let placed := appendStaleSections e.sections stale secStartOffset secStartPage
  let newSections := placed.1
  let appendedBytes := placed.2
  let totalAppendBytes := phtSize + appendedBytes
  let newShoff := roundUp (startOffset + totalAppendBytes) 8
  -- Witnesses: same shape as in-place, but with shifted base offset.
  have hSpec : PlaceFold.TransformSpec
      (appendTransform secStartOffset secStartPage) secStartOffset :=
    appendTransform_transformSpec _ _
  have hCurrLeStart : currentFileEnd e ≤ startOffset := le_roundUp _ _
  have hCurrLeSecStart : currentFileEnd e ≤ secStartOffset :=
    Nat.le_trans hCurrLeStart (Nat.le_add_right _ _)
  have hStaleEq : ∀ (i : Nat) (hi : i < e.sections.size),
      stale[i]?.getD false = sectionStale e i hi :=
    fun i hi => stale_ofFn_eq_sectionStale e i hi
  have hVerb : PlaceFold.VerbatimWitness (appendVerbatim stale) secStartOffset e.sections :=
    appendVerbatim_witness e secStartOffset hCurrLeSecStart stale hStaleEq
  have hSizeEq : newSections.size = e.sections.size :=
    PlaceFold.size_eq _ _
  have hCursorFloor : (0 : Nat) ≤ appendedBytes := PlaceFold.cursor_floor _ _
  -- newShoff bounds.
  have hStartLeShoff : startOffset ≤ newShoff :=
    Nat.le_trans (Nat.le_add_right _ _) (le_roundUp _ _)
  have hEhdrLeStart : Layout.ehdrSize ≤ startOffset :=
    Nat.le_trans (currentFileEnd_ge_ehdr e) hCurrLeStart
  -- per-entry placement.
  have hPlacement : ∀ (j : Nat) (hj : j < newSections.size),
      PlaceFold.Placement (appendVerbatim stale) secStartOffset e.sections 0 placed j := by
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
  -- Output's phdrs.size: retargetPtPhdr is `Array.map`, preserves size.
  have hRetSize : (updatePhdrsAfterMove e.phdrs none 0 0
                  e.interpIdx e.dynamicIdx newSections).size = e.phdrs.size := by
    unfold updatePhdrsAfterMove
    exact Array.size_mapIdx
  have hRetargetSize :
      (retargetPtPhdr (updatePhdrsAfterMove e.phdrs none 0 0
        e.interpIdx e.dynamicIdx newSections) startOffset startPage phtSize).size
        = e.phdrs.size := by
    unfold retargetPtPhdr
    rw [Array.size_map, hRetSize]
  have hOutPhdrsSize :
      ((retargetPtPhdr (updatePhdrsAfterMove e.phdrs none 0 0
        e.interpIdx e.dynamicIdx newSections) startOffset startPage phtSize).push
        (freshPtLoad startOffset startPage totalAppendBytes alignStartPage)).size
        = e.phdrs.size + 1 := by
    rw [Array.size_push]; rw [hRetargetSize]
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
  · -- hdr_phdr_disjoint: output's phoff = startOffset ≥ ehdrSize.
    show IntervalDisjoint 0 Layout.ehdrSize startOffset
      (startOffset + _ * Layout.phdrSize)
    rw [hOutPhdrsSize]
    -- ehdrSize ≤ startOffset (from currentFileEnd_ge_ehdr + currentFileEnd ≤ startOffset).
    exact Or.inl hEhdrLeStart
  · -- hdr_shdr_disjoint: newShoff ≥ ehdrSize.
    show IntervalDisjoint 0 Layout.ehdrSize _ _
    refine Or.inl ?_
    show Layout.ehdrSize ≤ newShoff
    exact Nat.le_trans hEhdrLeStart hStartLeShoff
  · -- phdr_shdr_disjoint: phdr table at [startOffset, startOffset + phtSize),
    -- shdr table at newShoff = roundUp(startOffset + phtSize + appendedBytes, 8).
    -- phdr table end = startOffset + (phdrs.size+1)*phdrSize = startOffset + phtSize.
    -- newShoff ≥ startOffset + phtSize + appendedBytes ≥ startOffset + phtSize.
    show IntervalDisjoint startOffset _ _ _
    rw [hOutPhdrsSize]
    refine Or.inl ?_
    show startOffset + (e.phdrs.size + 1) * Layout.phdrSize ≤ newShoff
    -- newShoff = roundUp(startOffset + totalAppendBytes, 8); totalAppendBytes = phtSize + appendedBytes.
    have hTotalLeShoff : startOffset + totalAppendBytes ≤ newShoff := le_roundUp _ _
    -- phtSize unfolds to (phdrs.size + 1) * phdrSize; totalAppendBytes = phtSize + appendedBytes.
    show startOffset + (e.phdrs.size + 1) * Layout.phdrSize ≤ newShoff
    have hPhtLe : startOffset + phtSize ≤ startOffset + totalAppendBytes := by
      show startOffset + phtSize ≤ startOffset + (phtSize + appendedBytes)
      omega
    exact Nat.le_trans hPhtLe hTotalLeShoff
  · -- hdr_sec_disjoint: same shape as in-place; needs hHeaderSec for verbatim.
    intros j hj
    have hjN : j < newSections.size := hj
    have hPl := hPlacement j hjN
    rcases hPl.offset_or with hVerbJ | hPlace
    · have hjS : j < e.sections.size := hSizeEq ▸ hjN
      rcases hHeaderSec j hjS with h | h | hID
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
    · -- Placed: section.offset ≥ secStartOffset = startOffset + phtSize ≥ ehdrSize.
      refine Or.inr (Or.inr (Or.inl ?_))
      show Layout.ehdrSize ≤ (newSections[j]'hjN).offset.val
      have h1 : secStartOffset + 0 ≤ (newSections[j]'hjN).offset.val := hPlace.2.1
      omega
  · -- phdr_sec_disjoint: extended phdr region is [startOffset, startOffset + phtSize).
    -- Verbatim sections: their range ≤ currentFileEnd ≤ startOffset (NO need for
    --   canAddFreshPtLoad — that's the whole point of relocate).
    -- Placed sections: range starts at secStartOffset = startOffset + phtSize, past
    --   the new phdr table.
    intros j hj
    have hjN : j < newSections.size := hj
    have hPl := hPlacement j hjN
    show ((newSections[j]'hjN).type = _ ∨ _)
    rw [hOutPhdrsSize]
    rcases hPl.offset_or with hVerbJ | hPlace
    · have hjS : j < e.sections.size := hSizeEq ▸ hjN
      rcases currentFileEnd_ge_section_end e j hjS with h | h | hLe
      · exact Or.inl (hPl.type_eq.trans h)
      · exact Or.inr (Or.inl (hPl.type_eq.trans h))
      · -- file range ≤ currentFileEnd ≤ startOffset = phdr-region start.
        refine Or.inr (Or.inr ?_)
        have hOffJ : (newSections[j]'hjN).offset.val = (e.sections[j]'hjS).offset.val := by
          rw [hVerbJ.2]
        have hSzJ : (newSections[j]'hjN).encodedSize = (e.sections[j]'hjS).encodedSize :=
          hPl.size_eq
        rw [hOffJ, hSzJ]
        -- IntervalDisjoint startOffset _ s.offset (s.offset + s.encodedSize).
        -- Goal: s.offset + s.encodedSize ≤ startOffset (right disjunct).
        refine Or.inr ?_
        exact Nat.le_trans hLe hCurrLeStart
    · -- Placed: section.offset ≥ secStartOffset = startOffset + phtSize, so
      --   startOffset + phtSize ≤ section.offset → phdr region ends at-or-before
      --   section start.
      refine Or.inr (Or.inr (Or.inl ?_))
      show startOffset + (e.phdrs.size + 1) * Layout.phdrSize ≤ (newSections[j]'hjN).offset.val
      have h1 : secStartOffset + 0 ≤ (newSections[j]'hjN).offset.val := hPlace.2.1
      -- secStartOffset = startOffset + phtSize = startOffset + (phdrs.size + 1) * phdrSize.
      omega
  · -- shdr_sec_disjoint: section ranges ≤ either currentFileEnd (verbatim) or
    --   secStartOffset + appendedBytes = startOffset + phtSize + appendedBytes
    --   ≤ newShoff (placed).
    intros j hj
    have hjN : j < newSections.size := hj
    have hPl := hPlacement j hjN
    rcases hPl.offset_or with hVerbJ | hPlace
    · have hjS : j < e.sections.size := hSizeEq ▸ hjN
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
    · -- Placed: range ≤ secStartOffset + appendedBytes = startOffset + phtSize + appendedBytes ≤ newShoff.
      refine Or.inr (Or.inr (Or.inr ?_))
      show (newSections[j]'hjN).offset.val + (newSections[j]'hjN).encodedSize ≤ newShoff
      have hRange : (newSections[j]'hjN).offset.val + (newSections[j]'hjN).encodedSize
            ≤ secStartOffset + appendedBytes := hPlace.2.2
      -- newShoff = roundUp(startOffset + totalAppendBytes, 8) ≥ startOffset + totalAppendBytes
      --         = startOffset + phtSize + appendedBytes = secStartOffset + appendedBytes.
      have hTotalLeShoff : startOffset + totalAppendBytes ≤ newShoff := le_roundUp _ _
      -- secStartOffset = startOffset + phtSize, totalAppendBytes = phtSize + appendedBytes.
      show (newSections[j]'hjN).offset.val + (newSections[j]'hjN).encodedSize ≤ newShoff
      have : secStartOffset + appendedBytes ≤ startOffset + totalAppendBytes := by
        show startOffset + phtSize + appendedBytes ≤ startOffset + (phtSize + appendedBytes)
        omega
      exact Nat.le_trans hRange (Nat.le_trans this hTotalLeShoff)

/-! ## `growEOFWithFreshPtLoadReloc` field projections and preserves_valid -/

@[simp] theorem growEOFWithFreshPtLoadReloc_sections_size
    (pageSize? : Option Nat) (e : ElfFile) :
    (growEOFWithFreshPtLoadReloc pageSize? e).sections.size = e.sections.size := by
  unfold growEOFWithFreshPtLoadReloc
  exact PlaceFold.size_eq _ _

@[simp] theorem growEOFWithFreshPtLoadReloc_header_phnum
    (pageSize? : Option Nat) (e : ElfFile) :
    (growEOFWithFreshPtLoadReloc pageSize? e).header.phnum
      = (e.phdrs.size + 1).toUInt16 := by
  unfold growEOFWithFreshPtLoadReloc; rfl

@[simp] theorem growEOFWithFreshPtLoadReloc_header_shnum
    (pageSize? : Option Nat) (e : ElfFile) :
    (growEOFWithFreshPtLoadReloc pageSize? e).header.shnum = e.header.shnum := by
  unfold growEOFWithFreshPtLoadReloc; rfl

@[simp] theorem growEOFWithFreshPtLoadReloc_header_shstrndx
    (pageSize? : Option Nat) (e : ElfFile) :
    (growEOFWithFreshPtLoadReloc pageSize? e).header.shstrndx = e.header.shstrndx := by
  unfold growEOFWithFreshPtLoadReloc; rfl

@[simp] theorem growEOFWithFreshPtLoadReloc_header_phentsize
    (pageSize? : Option Nat) (e : ElfFile) :
    (growEOFWithFreshPtLoadReloc pageSize? e).header.phentsize = e.header.phentsize := by
  unfold growEOFWithFreshPtLoadReloc; rfl

@[simp] theorem growEOFWithFreshPtLoadReloc_header_shentsize
    (pageSize? : Option Nat) (e : ElfFile) :
    (growEOFWithFreshPtLoadReloc pageSize? e).header.shentsize = e.header.shentsize := by
  unfold growEOFWithFreshPtLoadReloc; rfl

@[simp] theorem growEOFWithFreshPtLoadReloc_phdrs_size
    (pageSize? : Option Nat) (e : ElfFile) :
    (growEOFWithFreshPtLoadReloc pageSize? e).phdrs.size = e.phdrs.size + 1 := by
  unfold growEOFWithFreshPtLoadReloc updatePhdrsAfterMove retargetPtPhdr
  rw [Array.size_push, Array.size_map, Array.size_mapIdx]

theorem growEOFWithFreshPtLoadReloc_sections_name
    (pageSize? : Option Nat) (e : ElfFile) (j : Nat)
    (hj : j < (growEOFWithFreshPtLoadReloc pageSize? e).sections.size)
    (hjE : j < e.sections.size) :
    ((growEOFWithFreshPtLoadReloc pageSize? e).sections[j]'hj).name
      = (e.sections[j]'hjE).name := by
  unfold growEOFWithFreshPtLoadReloc at hj ⊢
  exact appendStaleSections_name _ _ _ _ j hj hjE

theorem growEOFWithFreshPtLoadReloc_sections_type
    (pageSize? : Option Nat) (e : ElfFile) (j : Nat)
    (hj : j < (growEOFWithFreshPtLoadReloc pageSize? e).sections.size)
    (hjE : j < e.sections.size) :
    ((growEOFWithFreshPtLoadReloc pageSize? e).sections[j]'hj).type
      = (e.sections[j]'hjE).type := by
  unfold growEOFWithFreshPtLoadReloc at hj ⊢
  exact appendStaleSections_type _ _ _ _ j hj hjE

theorem growEOFWithFreshPtLoadReloc_sections_content
    (pageSize? : Option Nat) (e : ElfFile) (j : Nat)
    (hj : j < (growEOFWithFreshPtLoadReloc pageSize? e).sections.size)
    (hjE : j < e.sections.size) :
    ((growEOFWithFreshPtLoadReloc pageSize? e).sections[j]'hj).content
      = (e.sections[j]'hjE).content := by
  unfold growEOFWithFreshPtLoadReloc at hj ⊢
  exact appendStaleSections_content _ _ _ _ j hj hjE

theorem growEOFWithFreshPtLoadReloc_findUniqueTypeIdx
    (pageSize? : Option Nat) (e : ElfFile) (ty : ShType) :
    (growEOFWithFreshPtLoadReloc pageSize? e).findUniqueTypeIdx ty
      = e.findUniqueTypeIdx ty := by
  apply ElfFile.firstIdxWhereIn_congr
  · exact growEOFWithFreshPtLoadReloc_sections_size _ _
  · intros k hk hk'
    have := growEOFWithFreshPtLoadReloc_sections_type pageSize? e k hk hk'
    simp [this]

@[simp] theorem growEOFWithFreshPtLoadReloc_dynamicIdx
    (pageSize? : Option Nat) (e : ElfFile) :
    (growEOFWithFreshPtLoadReloc pageSize? e).dynamicIdx = e.dynamicIdx :=
  growEOFWithFreshPtLoadReloc_findUniqueTypeIdx pageSize? e ShType.SHT_DYNAMIC

@[simp] theorem growEOFWithFreshPtLoadReloc_dynsymIdx
    (pageSize? : Option Nat) (e : ElfFile) :
    (growEOFWithFreshPtLoadReloc pageSize? e).dynsymIdx = e.dynsymIdx :=
  growEOFWithFreshPtLoadReloc_findUniqueTypeIdx pageSize? e ShType.SHT_DYNSYM

theorem growEOFWithFreshPtLoadReloc_contentAt
    (pageSize? : Option Nat) (e : ElfFile) (i? : Option Nat) :
    (growEOFWithFreshPtLoadReloc pageSize? e).contentAt i? = e.contentAt i? := by
  unfold ElfFile.contentAt
  cases i? with
  | none => rfl
  | some i =>
    simp only [Option.bind_some]
    by_cases hi : i < e.sections.size
    · have hi' : i < (growEOFWithFreshPtLoadReloc pageSize? e).sections.size :=
        (growEOFWithFreshPtLoadReloc_sections_size pageSize? e).symm ▸ hi
      rw [dif_pos hi', dif_pos hi]
      rw [growEOFWithFreshPtLoadReloc_sections_content pageSize? e i hi' hi]
    · have hi' : ¬ i < (growEOFWithFreshPtLoadReloc pageSize? e).sections.size := by
        intro h; exact hi ((growEOFWithFreshPtLoadReloc_sections_size pageSize? e).symm ▸ h)
      rw [dif_neg hi', dif_neg hi]

@[simp] theorem growEOFWithFreshPtLoadReloc_dynamic
    (pageSize? : Option Nat) (e : ElfFile) :
    (growEOFWithFreshPtLoadReloc pageSize? e).dynamic = e.dynamic := by
  unfold ElfFile.dynamic
  rw [growEOFWithFreshPtLoadReloc_dynamicIdx, growEOFWithFreshPtLoadReloc_contentAt]

@[simp] theorem growEOFWithFreshPtLoadReloc_dynsym
    (pageSize? : Option Nat) (e : ElfFile) :
    (growEOFWithFreshPtLoadReloc pageSize? e).dynsym = e.dynsym := by
  unfold ElfFile.dynsym
  rw [growEOFWithFreshPtLoadReloc_dynsymIdx, growEOFWithFreshPtLoadReloc_contentAt]

@[simp] theorem growEOFWithFreshPtLoadReloc_shstrtab
    (pageSize? : Option Nat) (e : ElfFile) :
    (growEOFWithFreshPtLoadReloc pageSize? e).shstrtab = e.shstrtab := by
  unfold ElfFile.shstrtab
  rw [growEOFWithFreshPtLoadReloc_header_shstrndx]
  by_cases hSh : e.header.shstrndx.toNat < e.sections.size
  · have hSh' : e.header.shstrndx.toNat
                  < (growEOFWithFreshPtLoadReloc pageSize? e).sections.size :=
      (growEOFWithFreshPtLoadReloc_sections_size pageSize? e).symm ▸ hSh
    rw [dif_pos hSh', dif_pos hSh]
    rw [growEOFWithFreshPtLoadReloc_sections_content pageSize? e _ hSh' hSh]
  · have hSh' : ¬ e.header.shstrndx.toNat
                   < (growEOFWithFreshPtLoadReloc pageSize? e).sections.size := by
      intro h; exact hSh ((growEOFWithFreshPtLoadReloc_sections_size pageSize? e).symm ▸ h)
    rw [dif_neg hSh', dif_neg hSh]

theorem growEOFWithFreshPtLoadReloc_findIdxByName
    (pageSize? : Option Nat) (e : ElfFile) (name : ByteArray) :
    (growEOFWithFreshPtLoadReloc pageSize? e).findIdxByName name
      = e.findIdxByName name := by
  unfold ElfFile.findIdxByName
  rw [growEOFWithFreshPtLoadReloc_shstrtab]
  cases e.shstrtab with
  | none => rfl
  | some st =>
    apply ElfFile.firstIdxWhereIn_congr
    · exact growEOFWithFreshPtLoadReloc_sections_size _ _
    · intros k hk hk'
      have := growEOFWithFreshPtLoadReloc_sections_name pageSize? e k hk hk'
      simp [this]

@[simp] theorem growEOFWithFreshPtLoadReloc_dynstrIdx
    (pageSize? : Option Nat) (e : ElfFile) :
    (growEOFWithFreshPtLoadReloc pageSize? e).dynstrIdx = e.dynstrIdx :=
  growEOFWithFreshPtLoadReloc_findIdxByName pageSize? e _

@[simp] theorem growEOFWithFreshPtLoadReloc_dynstr
    (pageSize? : Option Nat) (e : ElfFile) :
    (growEOFWithFreshPtLoadReloc pageSize? e).dynstr = e.dynstr := by
  unfold ElfFile.dynstr
  rw [growEOFWithFreshPtLoadReloc_dynstrIdx, growEOFWithFreshPtLoadReloc_contentAt]

/-- `growEOFWithFreshPtLoadReloc` preserves byte-layer `IsValid`,
    given the same `phdrs.size + 1 < UInt16.size` bound as the
    fresh-PT_LOAD in-place case. -/
theorem growEOFWithFreshPtLoadReloc_preserves_valid
    (pageSize? : Option Nat) (e : ElfFile)
    (hVal : e.IsValid)
    (hPhdrFit : (e.phdrs.size + 1) < UInt16.size) :
    (growEOFWithFreshPtLoadReloc pageSize? e).IsValid := by
  refine
    { header_counts := ?_, sections_wf := ?_, strtabs_wf := ?_,
      dynamic_wf := ?_, dynsym_wf := ?_, content_wf := ?_,
      types_distinct := ?_, names_unique := ?_ }
  ----------------------------------------
  -- header_counts: phnum bumped, phoff changed (irrelevant), shnum/etc. unchanged.
  ----------------------------------------
  · obtain ⟨_, h2, h3, h4, h5⟩ := hVal.header_counts
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [growEOFWithFreshPtLoadReloc_header_phnum, growEOFWithFreshPtLoadReloc_phdrs_size]
      show (e.phdrs.size + 1).toUInt16.toNat = e.phdrs.size + 1
      unfold Nat.toUInt16 UInt16.toNat
      simp only [UInt16.ofNat]
      exact Nat.mod_eq_of_lt hPhdrFit
    · rw [growEOFWithFreshPtLoadReloc_header_shnum,
          growEOFWithFreshPtLoadReloc_sections_size]; exact h2
    · rw [growEOFWithFreshPtLoadReloc_header_phentsize]; exact h3
    · rw [growEOFWithFreshPtLoadReloc_header_shentsize]; exact h4
    · rw [growEOFWithFreshPtLoadReloc_header_shstrndx,
          growEOFWithFreshPtLoadReloc_sections_size]; exact h5
  ----------------------------------------
  -- Remaining clauses: identical structure to fresh-PT_LOAD in-place.
  ----------------------------------------
  · intro h0
    have h0' : 0 < e.sections.size :=
      (growEOFWithFreshPtLoadReloc_sections_size pageSize? e) ▸ h0
    rw [growEOFWithFreshPtLoadReloc_sections_type pageSize? e 0 h0 h0']
    exact hVal.sections_wf h0'
  · have hAll := hVal.strtabs_wf
    show (growEOFWithFreshPtLoadReloc pageSize? e).sections.all _ = true
    unfold ElfFile.strtabsWellFormed at hAll
    rw [Array.all_eq_true] at hAll ⊢
    intro j hj
    have hjE : j < e.sections.size :=
      (growEOFWithFreshPtLoadReloc_sections_size pageSize? e) ▸ hj
    show ElfFile.Section.strtabWellFormedB
            ((growEOFWithFreshPtLoadReloc pageSize? e).sections[j]'hj) = true
    have : ElfFile.Section.strtabWellFormedB
              ((growEOFWithFreshPtLoadReloc pageSize? e).sections[j]'hj)
         = ElfFile.Section.strtabWellFormedB (e.sections[j]'hjE) := by
      unfold ElfFile.Section.strtabWellFormedB
      rw [growEOFWithFreshPtLoadReloc_sections_content pageSize? e j hj hjE]
    rw [this]; exact hAll j hjE
  · refine ⟨?_, ?_⟩
    · intro dyn hd
      rw [growEOFWithFreshPtLoadReloc_dynamic] at hd
      exact hVal.dynamic_wf.1 dyn hd
    · intros dyn ds hd hds
      rw [growEOFWithFreshPtLoadReloc_dynamic] at hd
      rw [growEOFWithFreshPtLoadReloc_dynstr] at hds
      exact hVal.dynamic_wf.2 dyn ds hd hds
  · intros syms ds hSyms hDs
    rw [growEOFWithFreshPtLoadReloc_dynsym] at hSyms
    rw [growEOFWithFreshPtLoadReloc_dynstr] at hDs
    exact hVal.dynsym_wf syms ds hSyms hDs
  · have hAll := hVal.content_wf
    show (growEOFWithFreshPtLoadReloc pageSize? e).sections.all _ = true
    unfold ElfFile.sectionsContentWellFormed at hAll
    rw [Array.all_eq_true] at hAll ⊢
    intro j hj
    have hjE : j < e.sections.size :=
      (growEOFWithFreshPtLoadReloc_sections_size pageSize? e) ▸ hj
    show ElfFile.Section.contentWellFormedB
            ((growEOFWithFreshPtLoadReloc pageSize? e).sections[j]'hj) = true
    have : ElfFile.Section.contentWellFormedB
              ((growEOFWithFreshPtLoadReloc pageSize? e).sections[j]'hj)
         = ElfFile.Section.contentWellFormedB (e.sections[j]'hjE) := by
      unfold ElfFile.Section.contentWellFormedB
      rw [growEOFWithFreshPtLoadReloc_sections_content pageSize? e j hj hjE]
    rw [this]; exact hAll j hjE
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hVal.types_distinct
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> {
      intros i hi j hj hi_t hj_t
      have hiE : i < e.sections.size :=
        (growEOFWithFreshPtLoadReloc_sections_size pageSize? e) ▸ hi
      have hjE : j < e.sections.size :=
        (growEOFWithFreshPtLoadReloc_sections_size pageSize? e) ▸ hj
      rw [growEOFWithFreshPtLoadReloc_sections_type pageSize? e i hi hiE] at hi_t
      rw [growEOFWithFreshPtLoadReloc_sections_type pageSize? e j hj hjE] at hj_t
      first
      | exact h1 i hiE j hjE hi_t hj_t
      | exact h2 i hiE j hjE hi_t hj_t
      | exact h3 i hiE j hjE hi_t hj_t
      | exact h4 i hiE j hjE hi_t hj_t
      | exact h5 i hiE j hjE hi_t hj_t
      | exact h6 i hiE j hjE hi_t hj_t
    }
  · unfold ElfFile.namedSectionsUnique
    rw [growEOFWithFreshPtLoadReloc_shstrtab]
    cases hSt : e.shstrtab with
    | none => trivial
    | some st =>
        obtain ⟨h1, h2⟩ := by
          have := hVal.names_unique
          unfold ElfFile.namedSectionsUnique at this
          rw [hSt] at this; exact this
        constructor <;> {
          intros i hi j hj hi_n hj_n
          have hiE : i < e.sections.size :=
            (growEOFWithFreshPtLoadReloc_sections_size pageSize? e) ▸ hi
          have hjE : j < e.sections.size :=
            (growEOFWithFreshPtLoadReloc_sections_size pageSize? e) ▸ hj
          rw [growEOFWithFreshPtLoadReloc_sections_name pageSize? e i hi hiE] at hi_n
          rw [growEOFWithFreshPtLoadReloc_sections_name pageSize? e j hj hjE] at hj_n
          first
          | exact h1 i hiE j hjE hi_n hj_n
          | exact h2 i hiE j hjE hi_n hj_n
        }

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
        -- canExtendLastPtLoad failed; try canAddFreshPtLoad.
        by_cases hAdd : canAddFreshPtLoad e = true
        · simp only [hAdd, ↓reduceIte]
          show (growEOFWithFreshPtLoad pageSize? e).spliceRegionsDisjoint
          exact growEOFWithFreshPtLoad_produces_spliceRegionsDisjoint pageSize? e
            hAdd hHeaderSec
        · simp only [hAdd, Bool.false_eq_true, ↓reduceIte]
          show (growEOFWithFreshPtLoadReloc pageSize? e).spliceRegionsDisjoint
          exact growEOFWithFreshPtLoadReloc_produces_spliceRegionsDisjoint pageSize? e
            hHeaderSec

/-- `growEOFWith` preserves byte-layer `IsValid`.

    Top-level dispatch theorem composing the four branches:

    1. `layoutAlreadyValid e = true` → identity (preservation trivial).
    2. `lastPtLoadIdx e.phdrs = none` → `layoutForEncoding e`.
    3. `canExtendLastPtLoad ... = true` → `growEOFWithMainBody`.
    4. `canExtendLastPtLoad ... = false` ∧ `canAddFreshPtLoad e = true`
       → `growEOFWithFreshPtLoad`.
    5. Both reject → `growEOFWithFreshPtLoadReloc`.

    The fresh-PT_LOAD branches (4, 5) bump `phnum` by 1, so they
    take an explicit `(e.phdrs.size + 1) < UInt16.size` bound to
    discharge the UInt16 round-trip in `header_counts`.  Real ELFs
    satisfy this trivially. -/
theorem growEOFWith_preserves_valid (pageSize? : Option Nat) (e : ElfFile)
    (hVal : e.IsValid)
    (hPhdrFit : (e.phdrs.size + 1) < UInt16.size) :
    (growEOFWith pageSize? e).IsValid := by
  unfold growEOFWith
  by_cases hLay : layoutAlreadyValid e = true
  · -- Fast path: identity.
    simp only [hLay, ↓reduceIte]
    exact hVal
  · simp only [hLay]
    cases hLast : lastPtLoadIdx e.phdrs with
    | none =>
      simp
      exact layoutForEncoding_preserves_valid e hVal
    | some lastIdx =>
      simp only []
      by_cases hExt : (canExtendLastPtLoad e
        (roundUp (currentFileEnd e)
          (match pageSize? with | some n => max n (maxPtLoadAlign e.phdrs) | none => maxPtLoadAlign e.phdrs))
        (roundUp (maxPtLoadVaddrEnd e.phdrs)
          (match pageSize? with | some n => max n (maxPtLoadAlign e.phdrs) | none => maxPtLoadAlign e.phdrs))
        (match pageSize? with | some n => max n (maxPtLoadAlign e.phdrs) | none => maxPtLoadAlign e.phdrs)
        lastIdx) = true
      · simp only [hExt, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        show (growEOFWithMainBody pageSize? e lastIdx).IsValid
        exact growEOFWithMainBody_preserves_valid pageSize? e lastIdx hVal
      · simp only [hExt, Bool.not_false, ↓reduceIte]
        by_cases hAdd : canAddFreshPtLoad e = true
        · simp only [hAdd, ↓reduceIte]
          show (growEOFWithFreshPtLoad pageSize? e).IsValid
          exact growEOFWithFreshPtLoad_preserves_valid pageSize? e hVal hPhdrFit
        · simp only [hAdd, Bool.false_eq_true, ↓reduceIte]
          show (growEOFWithFreshPtLoadReloc pageSize? e).IsValid
          exact growEOFWithFreshPtLoadReloc_preserves_valid pageSize? e hVal hPhdrFit

end Patchelf.Elf
