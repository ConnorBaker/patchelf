/-
  Byte-layer layout pass.

  Ops may grow section content (e.g. `.dynstr` after `--add-needed`),
  leaving the IR's `section.offset` fields pointing at stale slots too
  small to hold the new content. This module recomputes section
  offsets and updates phdr entries so the encoder can emit a valid
  file.

  Strategy: keep section 0 (SHT_NULL) where it is (vacuous),
  then pack every other non-NOBITS section back-to-back after the
  ELF header + phdr table, honoring `section.addralign`. Place the
  shdr table at the end. Update PT_INTERP and PT_DYNAMIC phdr
  offsets to match their sections' new offsets.

  Deliberately simple and never overlaps. Does NOT preserve PT_LOAD
  vaddr ↔ offset congruence automatically — callers should prefer
  keeping stable offsets when possible; this pass exists for the
  "sections grew, need to reflow" case.
-/
module

public import Patchelf.Elf.ElfFile
public import Patchelf.Elf.SectionOps

@[expose] public section

namespace Patchelf.Elf

open Layout

/-- Update a section's `offset` field. -/
def Section.withOffset (s : Section) (newOff : Nat) : Section :=
  { s with offset := ⟨newOff⟩ }

def phdrWithOffsetSize (ph : Patchelf.Elf.ProgramHeader)
    (newOff newSize : Nat) : Patchelf.Elf.ProgramHeader :=
  { ph with offset := ⟨newOff⟩,
            filesz := ⟨newSize⟩,
            memsz  := ⟨newSize⟩ }

/-- Does the current layout already accommodate each section?
    A layout is valid when every pair of file-resident sections has
    disjoint `[offset, offset + encodedSize)` ranges AND the shdr
    table's range is disjoint from every section's range.

    Section 0 (SHT_NULL) and SHT_NOBITS sections contribute no file
    bytes and are skipped. -/
def layoutAlreadyValid (e : ElfFile) : Bool :=
  decide (e.sectionsNonOverlapping ∧ e.shdrSectionDisjoint)

theorem layoutAlreadyValid_iff (e : ElfFile) :
    layoutAlreadyValid e = true ↔
      e.sectionsNonOverlapping ∧ e.shdrSectionDisjoint := by
  unfold layoutAlreadyValid
  exact decide_eq_true_iff

theorem layoutAlreadyValid_of_spliceRegionsDisjoint (e : ElfFile)
    (h : e.spliceRegionsDisjoint) : layoutAlreadyValid e = true :=
  (layoutAlreadyValid_iff e).mpr ⟨h.sections_disjoint, h.shdr_sec_disjoint⟩

/-- One step of the layout fold.  Indexed step (i carries the section's
    original index in the input array — needed because section 0 is
    treated specially even when its type isn't SHT_NULL).  Threads
    `(acc, cursor)` (placed sections so far, current file offset). -/
def layoutStep (acc : Array Section × Nat) (idxAndSec : Nat × Section) :
    Array Section × Nat :=
  let (i, s) := idxAndSec
  let (sectionsAcc, cursor) := acc
  if i = 0 ∨ s.type = ShType.SHT_NULL ∨ s.type = ShType.SHT_NOBITS then
    (sectionsAcc.push s, cursor)
  else
    let off := roundUp cursor s.addralign.val
    (sectionsAcc.push (s.withOffset off), off + s.encodedSize)

/-- Layout fold helper: walks sections, threading `(acc, cursor)`
    (placed sections so far, current file offset).

    Section 0 and SHT_NULL sections are pushed verbatim (offset 0 /
    unchanged offset; consume no cursor).  SHT_NOBITS sections are
    also pushed verbatim (no file bytes).  Every other section is
    given a fresh `offset = roundUp cursor addralign` and `cursor`
    advances by `s.encodedSize`.

    Foldl form (vs. tail-recursion) so proofs can use
    `Array.foldl_induction` directly. -/
def layoutSectionsFold (sections : Array Section) (cursor0 : Nat) :
    Array Section × Nat :=
  let indexed := sections.mapIdx (fun i s => (i, s))
  indexed.foldl (init := (Array.emptyWithCapacity sections.size, cursor0)) layoutStep

/-- Rebuild a single phdr entry against the freshly-laid-out section
    array.  PT_INTERP / PT_DYNAMIC pick up their target section's new
    offset and `encodedSize`; other phdr types pass through unchanged. -/
def relocatePhdr (interpIdx dynamicIdx : Option Nat)
    (newSections : Array Section) (ph : Patchelf.Elf.ProgramHeader) :
    Patchelf.Elf.ProgramHeader :=
  if ph.type = PhType.PT_INTERP then
    match interpIdx with
    | none => ph
    | some i =>
      if h : i < newSections.size then
        let s := newSections[i]'h
        phdrWithOffsetSize ph s.offset.val s.encodedSize
      else ph
  else if ph.type = PhType.PT_DYNAMIC then
    match dynamicIdx with
    | none => ph
    | some i =>
      if h : i < newSections.size then
        let s := newSections[i]'h
        phdrWithOffsetSize ph s.offset.val s.encodedSize
      else ph
  else ph

/-- Layout pass: assign fresh offsets to every non-NULL section so
    they pack contiguously (respecting `addralign`), then place the
    shdr table after all sections. Updates the header's `shoff` and
    PT_INTERP / PT_DYNAMIC phdr entries to agree with the new layout.

    Section 0 (SHT_NULL) keeps offset 0 by convention.
    NOBITS sections keep their declared offset (they contribute no
    file bytes).
    Phdr table stays at its current `header.phoff` (typically 64,
    right after the header).

    The pass is idempotent on already-well-laid-out files that were
    produced by this encoder. -/
def layoutForEncoding (e : ElfFile) : ElfFile :=
  -- Reserve [0, ehdrSize) for the header, [phoff, phoff + phnum*phdrSize)
  -- for the phdr table. Start packing sections after max(ehdrSize,
  -- phoff + phnum*phdrSize).
  let phdrTableEnd := e.header.phoff.val
                      + e.phdrs.size * Layout.phdrSize
  let initialCursor := max Layout.ehdrSize phdrTableEnd
  let result := layoutSectionsFold e.sections initialCursor
  let newSections := result.1
  let cursor := result.2
  -- Place shdr table at end (8-byte aligned).
  let shoff := roundUp cursor 8
  let newPhdrs := e.phdrs.map (relocatePhdr e.interpIdx e.dynamicIdx newSections)
  let newHeader : Patchelf.Elf.ElfHeader :=
    { e.header with shoff := ⟨shoff⟩ }
  { header := newHeader, phdrs := newPhdrs, sections := newSections }

/-! ## Splice-region full validity

    `layoutFullyValid` is a Bool-valued check equivalent to
    `spliceRegionsDisjoint`.  Stronger than `layoutAlreadyValid`,
    which only checks section-section + shdr-section overlaps.
    The full predicate also covers (header, phdr-table),
    (header, shdr-table), (phdr-table, shdr-table), (header, section),
    (phdr-table, section).  Real ELF inputs always satisfy it; the
    encoder's existing `layoutAlreadyValid` is the optimization-friendly
    byte-stability check, while this is the verification predicate.

    Together with the per-struct forward roundtrips, this is the
    structural backbone for unconditional Tier D. -/
def layoutFullyValid (e : ElfFile) : Bool := decide e.spliceRegionsDisjoint

theorem layoutFullyValid_iff (e : ElfFile) :
    layoutFullyValid e = true ↔ e.spliceRegionsDisjoint := by
  unfold layoutFullyValid; exact decide_eq_true_iff

theorem spliceRegionsDisjoint_of_layoutFullyValid (e : ElfFile)
    (h : layoutFullyValid e = true) : e.spliceRegionsDisjoint :=
  (layoutFullyValid_iff e).mp h

/-! ## `Section.withOffset` field preservation

    `withOffset` only rewrites `offset`; every other section field
    (including `content`, hence `encodedSize`) is unchanged. -/

@[simp] theorem withOffset_type (s : Section) (n : Nat) :
    (Section.withOffset s n).type = s.type := rfl

@[simp] theorem withOffset_content (s : Section) (n : Nat) :
    (Section.withOffset s n).content = s.content := rfl

@[simp] theorem withOffset_encodedSize (s : Section) (n : Nat) :
    (Section.withOffset s n).encodedSize = s.encodedSize := by
  unfold Section.encodedSize
  rfl

@[simp] theorem withOffset_addralign (s : Section) (n : Nat) :
    (Section.withOffset s n).addralign = s.addralign := rfl

/-! ## `roundUp` arithmetic facts -/

theorem le_roundUp (n align : Nat) : n ≤ roundUp n align := by
  unfold roundUp
  by_cases hA : align = 0
  · simp [hA]
  · simp [hA]
    have hPos : 0 < align := Nat.pos_of_ne_zero hA
    -- Goal: n ≤ (n + align - 1) / align * align.
    have hDM := Nat.div_add_mod (n + align - 1) align
    -- hDM: align * ((n + align - 1) / align) + (n + align - 1) % align = n + align - 1
    have hModLt : (n + align - 1) % align < align := Nat.mod_lt _ hPos
    have hMul : (n + align - 1) / align * align = align * ((n + align - 1) / align) :=
      Nat.mul_comm _ _
    rw [hMul]
    omega

/-! ## `layoutSectionsFold` structural facts -/

namespace LayoutSectionsFold

/-- One step of the layout fold advances `acc.size` by 1. -/
theorem step_size_eq (acc : Array Section × Nat)
    (idx : Nat) (s : Section) :
    (layoutStep acc (idx, s)).1.size = acc.1.size + 1 := by
  unfold layoutStep
  by_cases hAlt : idx = 0 ∨ s.type = ShType.SHT_NULL ∨ s.type = ShType.SHT_NOBITS
  · simp [hAlt, Array.size_push]
  · simp [hAlt, Array.size_push]

/-- One step of the layout fold's cursor is monotone. -/
theorem step_cursor_mono (acc : Array Section × Nat)
    (idx : Nat) (s : Section) :
    acc.2 ≤ (layoutStep acc (idx, s)).2 := by
  unfold layoutStep
  by_cases hAlt : idx = 0 ∨ s.type = ShType.SHT_NULL ∨ s.type = ShType.SHT_NOBITS
  · simp [hAlt]
  · simp [hAlt]
    have := le_roundUp acc.2 s.addralign.val
    omega

/-- For any index `j < state.1.size` (i.e. valid in the pre-step state),
    the post-step `getElem` agrees with the pre-step `getElem`.  Both
    branches of `layoutStep` push exactly one element, so existing
    indices read through to the original.  Used to discharge the four
    "preserved by step" subgoals in the placement / pair-disjoint
    stability proofs. -/
theorem layoutStep_getElem_lt (state : Array Section × Nat)
    (idx : Nat) (s : Section) (j : Nat) (hjLt : j < state.1.size) :
    (layoutStep state (idx, s)).1[j]'(by rw [step_size_eq]; omega)
      = state.1[j]'hjLt := by
  unfold layoutStep
  by_cases hAlt : idx = 0 ∨ s.type = ShType.SHT_NULL ∨ s.type = ShType.SHT_NOBITS
  · simp [hAlt]; rw [Array.getElem_push_lt hjLt]
  · simp [hAlt]; rw [Array.getElem_push_lt hjLt]

/-! Size + cursor floor invariants. -/

theorem size_eq (sections : Array Section) (cursor0 : Nat) :
    (layoutSectionsFold sections cursor0).1.size = sections.size := by
  unfold layoutSectionsFold
  let indexed := sections.mapIdx (fun i s => (i, s))
  have hIndexedSize : indexed.size = sections.size := Array.size_mapIdx
  show (Array.foldl layoutStep (Array.emptyWithCapacity sections.size, cursor0) indexed).1.size
        = sections.size
  rw [show sections.size = indexed.size from hIndexedSize.symm] at *
  have h := @Array.foldl_induction (Nat × Section) (Array Section × Nat) indexed
    (motive := fun k state => state.1.size = k)
    (init := (Array.emptyWithCapacity indexed.size, cursor0))
    (h0 := by simp)
    (f := layoutStep)
    (hf := by
      intros i state ih
      rw [step_size_eq, ih])
  exact h

theorem cursor_floor (sections : Array Section) (cursor0 : Nat) :
    cursor0 ≤ (layoutSectionsFold sections cursor0).2 := by
  unfold layoutSectionsFold
  let indexed := sections.mapIdx (fun i s => (i, s))
  show cursor0 ≤ (Array.foldl layoutStep (Array.emptyWithCapacity sections.size, cursor0) indexed).2
  have h := @Array.foldl_induction (Nat × Section) (Array Section × Nat) indexed
    (motive := fun _ state => cursor0 ≤ state.2)
    (init := (Array.emptyWithCapacity sections.size, cursor0))
    (h0 := Nat.le_refl _)
    (f := layoutStep)
    (hf := by
      intros i state ih
      exact Nat.le_trans ih (step_cursor_mono state _ _))
  exact h

/-! ## Per-entry placement invariant

    `Placement` records the per-entry guarantee for an output position
    `j < state.1.size`:

    * `.type` and `.encodedSize` are inherited from `sections[j]`,
    * either the entry is "exempt" (j = 0 ∨ original type ∈ {NULL, NOBITS}),
      with offset preserved from the original,
    * or it has fresh offset `o` with `cursor0 ≤ o` and
      `o + encodedSize ≤ state.2`. -/
structure Placement (sections : Array Section) (cursor0 : Nat)
    (state : Array Section × Nat) (j : Nat) : Prop where
  hjA : j < state.1.size
  hjS : j < sections.size
  type_eq : (state.1[j]'hjA).type = (sections[j]'hjS).type
  size_eq : (state.1[j]'hjA).encodedSize = (sections[j]'hjS).encodedSize
  offset_or :
    (((j = 0 ∨ (sections[j]'hjS).type = ShType.SHT_NULL ∨
        (sections[j]'hjS).type = ShType.SHT_NOBITS) ∧
        (state.1[j]'hjA).offset = (sections[j]'hjS).offset)
     ∨ ((¬ (j = 0 ∨ (sections[j]'hjS).type = ShType.SHT_NULL ∨
            (sections[j]'hjS).type = ShType.SHT_NOBITS)) ∧
        cursor0 ≤ (state.1[j]'hjA).offset.val ∧
        (state.1[j]'hjA).offset.val + (state.1[j]'hjA).encodedSize ≤ state.2))

/-- Stability of `Placement` under a layout step: existing entries
    survive the push + cursor advance unchanged. -/
theorem placement_step_existing (sections : Array Section) (cursor0 : Nat)
    (state : Array Section × Nat) (idx : Nat) (s : Section) (j : Nat)
    (hPl : Placement sections cursor0 state j) :
    Placement sections cursor0 (layoutStep state (idx, s)) j := by
  have hCurLe : state.2 ≤ (layoutStep state (idx, s)).2 :=
    step_cursor_mono state idx s
  have hjA' : j < (layoutStep state (idx, s)).1.size := by
    rw [step_size_eq]; have := hPl.hjA; omega
  have hPushEq : (layoutStep state (idx, s)).1[j]'hjA' = state.1[j]'hPl.hjA :=
    layoutStep_getElem_lt state idx s j hPl.hjA
  refine
    { hjA := hjA'
      hjS := hPl.hjS
      type_eq := ?_
      size_eq := ?_
      offset_or := ?_ }
  · rw [hPushEq]; exact hPl.type_eq
  · rw [hPushEq]; exact hPl.size_eq
  · rcases hPl.offset_or with hExempt | hPlace
    · refine Or.inl ⟨hExempt.1, ?_⟩
      rw [hPushEq]; exact hExempt.2
    · refine Or.inr ⟨hPlace.1, ?_, ?_⟩
      · rw [hPushEq]; exact hPlace.2.1
      · rw [hPushEq]; exact Nat.le_trans hPlace.2.2 hCurLe

/-- The freshly-pushed entry has `Placement`. -/
theorem placement_step_new (sections : Array Section) (cursor0 : Nat)
    (state : Array Section × Nat) (i : Nat) (s : Section)
    (hSize : state.1.size = i)
    (hCur : cursor0 ≤ state.2)
    (hiBound : i < sections.size)
    (hSeq : sections[i]'hiBound = s) :
    Placement sections cursor0 (layoutStep state (i, s)) i := by
  subst hSize
  have hjA : state.1.size < (layoutStep state (state.1.size, s)).1.size := by
    rw [step_size_eq]; omega
  by_cases hAlt :
      state.1.size = 0 ∨ s.type = ShType.SHT_NULL ∨ s.type = ShType.SHT_NOBITS
  · have hValEq : (layoutStep state (state.1.size, s)).1[state.1.size]'hjA = s := by
      unfold layoutStep
      simp only [hAlt, ↓reduceIte]
      exact Array.getElem_push_eq
    refine
      { hjA := hjA, hjS := hiBound,
        type_eq := ?_, size_eq := ?_, offset_or := ?_ }
    · rw [hValEq, hSeq]
    · rw [hValEq, hSeq]
    · refine Or.inl ⟨?_, ?_⟩
      · rcases hAlt with h0 | hN | hNB
        · exact Or.inl h0
        · rw [hSeq]; exact Or.inr (Or.inl hN)
        · rw [hSeq]; exact Or.inr (Or.inr hNB)
      · rw [hValEq, hSeq]
  · let off := roundUp state.2 s.addralign.val
    have hValEq : (layoutStep state (state.1.size, s)).1[state.1.size]'hjA
                 = s.withOffset off := by
      unfold layoutStep
      simp only [hAlt, ↓reduceIte]
      exact Array.getElem_push_eq
    have hCurEq : (layoutStep state (state.1.size, s)).2 = off + s.encodedSize := by
      unfold layoutStep
      simp only [hAlt, ↓reduceIte]
      rfl
    refine
      { hjA := hjA, hjS := hiBound,
        type_eq := ?_, size_eq := ?_, offset_or := ?_ }
    · rw [hValEq, withOffset_type, hSeq]
    · rw [hValEq, withOffset_encodedSize, hSeq]
    · refine Or.inr ⟨?_, ?_, ?_⟩
      · rw [hSeq]; exact hAlt
      · rw [hValEq]
        show cursor0 ≤ (s.withOffset off).offset.val
        have : (s.withOffset off).offset.val = off := rfl
        rw [this]
        exact Nat.le_trans hCur (le_roundUp _ _)
      · rw [hValEq, hCurEq]
        show (s.withOffset off).offset.val + (s.withOffset off).encodedSize
            ≤ off + s.encodedSize
        have hOffVal : (s.withOffset off).offset.val = off := rfl
        rw [hOffVal, withOffset_encodedSize]
        exact Nat.le_refl _

/-- Convenience: from a `Placement` plus `hSection0Null`, derive the
    output entry's NOBITS-or-NULL fact when the input was exempt.
    Returns `Or.inl hNOBITS` or `Or.inr hNULL`.  Used to collapse
    the 3-arm `rcases hExempt.1 with hj0 | hN | hNB` cascade — the
    j = 0 case is discharged by hSection0Null. -/
theorem Placement.exempt_to_NOBITS_or_NULL
    {sections : Array Section} {cursor0 : Nat}
    {state : Array Section × Nat} {j : Nat}
    (hPl : Placement sections cursor0 state j)
    (hSection0Null : ∀ (h : 0 < sections.size),
      (sections[0]'h).type = ShType.SHT_NULL)
    (hExempt : (j = 0 ∨ (sections[j]'hPl.hjS).type = ShType.SHT_NULL ∨
                (sections[j]'hPl.hjS).type = ShType.SHT_NOBITS) ∧
               (state.1[j]'hPl.hjA).offset = (sections[j]'hPl.hjS).offset) :
    (state.1[j]'hPl.hjA).type = ShType.SHT_NOBITS ∨
    (state.1[j]'hPl.hjA).type = ShType.SHT_NULL := by
  rcases hExempt.1 with hj0 | hN | hNB
  · subst hj0
    exact Or.inr (hPl.type_eq.trans (hSection0Null hPl.hjS))
  · exact Or.inr (hPl.type_eq.trans hN)
  · exact Or.inl (hPl.type_eq.trans hNB)

/-- Pairwise non-overlap claim for two output entries `j ≠ j'`:
    either at least one is NOBITS / NULL, or their byte ranges
    `[offset, offset+encodedSize)` are interval-disjoint.

    Disjunct order matches `ElfFile.sectionsNonOverlapping`'s
    NOBITS-NOBITS-NULL-NULL-IntervalDisjoint shape so the bridge from
    layoutForEncoding output to spliceRegionsDisjoint composes by
    `exact`. -/
def PairDisjoint (state : Array Section × Nat) (j j' : Nat) : Prop :=
  ∀ (hjA : j < state.1.size) (hjA' : j' < state.1.size),
    let s  := state.1[j]'hjA
    let s' := state.1[j']'hjA'
    s.type = ShType.SHT_NOBITS ∨ s'.type = ShType.SHT_NOBITS ∨
    s.type = ShType.SHT_NULL ∨ s'.type = ShType.SHT_NULL ∨
    IntervalDisjoint
      s.offset.val (s.offset.val + s.encodedSize)
      s'.offset.val (s'.offset.val + s'.encodedSize)

/-- `PairDisjoint` is symmetric. -/
theorem pairDisjoint_symm (state : Array Section × Nat) (j j' : Nat)
    (hPD : PairDisjoint state j j') : PairDisjoint state j' j := by
  unfold PairDisjoint
  intros hjA hjA'
  have h := hPD hjA' hjA
  -- New disjunct order: s.NOBITS ∨ s'.NOBITS ∨ s.NULL ∨ s'.NULL ∨ ID
  rcases h with h | h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inl h))
  · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
    rcases h with hL | hR
    · exact Or.inr hL
    · exact Or.inl hR

/-- Stability of `PairDisjoint` under a layout step: indices `< state.1.size`
    survive the push (getElem unchanged). -/
theorem pairDisjoint_step_existing
    (state : Array Section × Nat) (idx : Nat) (s : Section)
    (j j' : Nat) (hjLt : j < state.1.size) (hjLt' : j' < state.1.size)
    (hPD : PairDisjoint state j j') :
    PairDisjoint (layoutStep state (idx, s)) j j' := by
  unfold PairDisjoint
  intros _ _
  rw [layoutStep_getElem_lt state idx s j hjLt,
      layoutStep_getElem_lt state idx s j' hjLt']
  exact hPD hjLt hjLt'

/-- New-entry vs. existing-entry disjointness: at the step that places
    a new entry at `state.1.size = i`, its byte range is interval-disjoint
    from any existing non-exempt entry's range, because the new entry's
    offset (= roundUp state.2 _) is ≥ state.2, which already dominates
    every prior non-exempt entry's end-offset.

    `hSection0Null` requires `sections[0].type = SHT_NULL` (an ELF-spec
    invariant the parser's IsValid enforces).  Used in the j = 0 case
    of an existing-exempt entry's discharge: by the type_eq from
    Placement, the output entry at index 0 also has type SHT_NULL,
    which satisfies the disjointness disjunction. -/
theorem pairDisjoint_step_new_vs_old
    (sections : Array Section) (cursor0 : Nat)
    (state : Array Section × Nat) (i : Nat) (s : Section) (j : Nat)
    (hSize : state.1.size = i)
    (hCur : cursor0 ≤ state.2)
    (hiBound : i < sections.size)
    (hSeq : sections[i]'hiBound = s)
    (hjLt : j < state.1.size)
    (hPlj : Placement sections cursor0 state j)
    (hSection0Null : ∀ (h : 0 < sections.size),
      (sections[0]'h).type = ShType.SHT_NULL) :
    PairDisjoint (layoutStep state (i, s)) j i := by
  unfold PairDisjoint
  intros _ hjA'
  -- For the j (existing) entry: getElem is preserved by the push.
  have hPushEqJ : (layoutStep state (i, s)).1[j]'_ = state.1[j]'hjLt :=
    layoutStep_getElem_lt state i s j hjLt
  -- For the new i entry: its value depends on the exempt branch.
  by_cases hAlt : i = 0 ∨ s.type = ShType.SHT_NULL ∨ s.type = ShType.SHT_NOBITS
  · -- New entry exempt: pushed `s` verbatim.
    have hPushEqI : (layoutStep state (i, s)).1[i]'hjA' = s := by
      subst hSize
      unfold layoutStep
      simp only [hAlt, ↓reduceIte]
      exact Array.getElem_push_eq
    rw [hPushEqI]
    rcases hAlt with h0 | hN | hNB
    · exfalso; rw [hSize, h0] at hjLt; exact absurd hjLt (Nat.not_lt_zero _)
    · -- s.type = NULL: s' (= new entry value) is NULL.  Disjunct 4: s'.NULL.
      refine Or.inr (Or.inr (Or.inr (Or.inl hN)))
    · -- s.type = NOBITS: s'.NOBITS.  Disjunct 2.
      refine Or.inr (Or.inl hNB)
  · -- New entry non-exempt: pushed `s.withOffset off`, where off ≥ state.2.
    let off := roundUp state.2 s.addralign.val
    have hPushEqI : (layoutStep state (i, s)).1[i]'hjA' = s.withOffset off := by
      subst hSize
      unfold layoutStep
      simp only [hAlt, ↓reduceIte]
      exact Array.getElem_push_eq
    rw [hPushEqI, hPushEqJ]
    rcases hPlj.offset_or with hExj | hPlacej
    · -- j exempt: derive s.NOBITS or s.NULL via the helper.  PairDisjoint's
      -- disjunct order is s.NOBITS ∨ s'.NOBITS ∨ s.NULL ∨ s'.NULL ∨ ID.
      rcases hPlj.exempt_to_NOBITS_or_NULL hSection0Null hExj with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
    · -- j non-exempt.
      refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
      left
      show (state.1[j]'hjLt).offset.val + (state.1[j]'hjLt).encodedSize
          ≤ (s.withOffset off).offset.val
      have hValEq : (s.withOffset off).offset.val = off := rfl
      rw [hValEq]
      have hRoundUpGe : state.2 ≤ roundUp state.2 s.addralign.val := le_roundUp _ _
      exact Nat.le_trans hPlacej.2.2 hRoundUpGe

/-- Strengthened motive for the layout fold: size, cursor floor,
    per-entry placement, and pairwise non-overlap. -/
structure LayoutInv (sections : Array Section) (cursor0 : Nat)
    (k : Nat) (state : Array Section × Nat) : Prop where
  size_eq : state.1.size = k
  cursor_floor : cursor0 ≤ state.2
  per_entry : ∀ (j : Nat), j < k → Placement sections cursor0 state j
  pair_disj : ∀ (j j' : Nat), j < k → j' < k → j ≠ j' →
    PairDisjoint state j j'

/-- Master fold-induction invariant.  Bundles size, cursor floor,
    per-entry placement, and pairwise non-overlap.

    Closed at `k = sections.size`, this gives every output entry's
    `Placement` and `PairDisjoint` for any pair of distinct indices.

    Requires `hSection0Null` — the ELF-spec invariant that
    `sections[0].type = SHT_NULL` (parser's IsValid enforces it).
    Used to discharge the j = 0 case in pairwise non-overlap. -/
theorem layoutSectionsFold_inv (sections : Array Section) (cursor0 : Nat)
    (hSection0Null : ∀ (h : 0 < sections.size),
      (sections[0]'h).type = ShType.SHT_NULL) :
    LayoutInv sections cursor0 sections.size
      (layoutSectionsFold sections cursor0) := by
  unfold layoutSectionsFold
  let indexed := sections.mapIdx (fun i s => (i, s))
  have hIndexedSize : indexed.size = sections.size := Array.size_mapIdx
  show LayoutInv sections cursor0 sections.size
    (Array.foldl layoutStep (Array.emptyWithCapacity sections.size, cursor0) indexed)
  rw [show sections.size = indexed.size from hIndexedSize.symm]
  apply @Array.foldl_induction (Nat × Section) (Array Section × Nat) indexed
    (motive := LayoutInv sections cursor0)
    (init := (Array.emptyWithCapacity sections.size, cursor0))
    (h0 := by
      refine ⟨?_, Nat.le_refl _, ?_, ?_⟩
      · simp
      · intros j hj; exact absurd hj (Nat.not_lt_zero _)
      · intros j j' hj _ _; exact absurd hj (Nat.not_lt_zero _))
    (f := layoutStep)
    (hf := by
      intros i state ih
      have hiBound : i.val < sections.size := hIndexedSize ▸ i.isLt
      have hSeq : indexed[i] = (i.val, sections[i.val]'hiBound) := by
        show indexed[i.val] = _; rw [Array.getElem_mapIdx]
      rw [hSeq]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [step_size_eq]; rw [ih.size_eq]
      · exact Nat.le_trans ih.cursor_floor (step_cursor_mono _ _ _)
      · -- per_entry
        intros j hjLt
        by_cases hjOld : j < state.1.size
        · have hjOldK : j < i.val := by rw [ih.size_eq] at hjOld; exact hjOld
          exact placement_step_existing sections cursor0 state i.val
                  (sections[i.val]'hiBound) j (ih.per_entry j hjOldK)
        · have hjGe : state.1.size ≤ j := Nat.le_of_not_lt hjOld
          have hjEq : i.val = j := by
            rw [ih.size_eq] at hjGe; omega
          subst hjEq
          exact placement_step_new sections cursor0 state i.val
                  (sections[i.val]'hiBound) ih.size_eq ih.cursor_floor hiBound rfl
      · -- pair_disj
        intros j j' hjLt hjLt' hjNe
        by_cases hjOld : j < state.1.size
        all_goals by_cases hjOld' : j' < state.1.size
        · -- both old: stability.
          have hjOldK : j < i.val := by rw [ih.size_eq] at hjOld; exact hjOld
          have hjOldK' : j' < i.val := by rw [ih.size_eq] at hjOld'; exact hjOld'
          exact pairDisjoint_step_existing state i.val
                  (sections[i.val]'hiBound) j j' hjOld hjOld'
                  (ih.pair_disj j j' hjOldK hjOldK' hjNe)
        · -- j old, j' new: j' = state.1.size = i.val.
          have hjOldK : j < i.val := by rw [ih.size_eq] at hjOld; exact hjOld
          have hjGe' : state.1.size ≤ j' := Nat.le_of_not_lt hjOld'
          have hj'Eq : i.val = j' := by
            rw [ih.size_eq] at hjGe'; omega
          subst hj'Eq
          exact pairDisjoint_step_new_vs_old sections cursor0 state i.val
                  (sections[i.val]'hiBound) j ih.size_eq ih.cursor_floor
                  hiBound rfl hjOld (ih.per_entry j hjOldK) hSection0Null
        · -- j new, j' old: symmetric to above.
          have hjOldK' : j' < i.val := by rw [ih.size_eq] at hjOld'; exact hjOld'
          have hjGe : state.1.size ≤ j := Nat.le_of_not_lt hjOld
          have hjEq : i.val = j := by
            rw [ih.size_eq] at hjGe; omega
          subst hjEq
          exact pairDisjoint_symm _ _ _
            (pairDisjoint_step_new_vs_old sections cursor0 state i.val
              (sections[i.val]'hiBound) j' ih.size_eq ih.cursor_floor
              hiBound rfl hjOld' (ih.per_entry j' hjOldK') hSection0Null)
        · -- both new: contradicts hjNe (both equal state.1.size = i.val).
          -- Both hjLt and hjLt' assert `< i.val + 1` (= state.1.size + 1).
          -- Combined with j ≥ state.1.size and j' ≥ state.1.size, both equal i.val.
          exfalso
          have hjGe : state.1.size ≤ j := Nat.le_of_not_lt hjOld
          have hjGe' : state.1.size ≤ j' := Nat.le_of_not_lt hjOld'
          rw [ih.size_eq] at hjGe hjGe'
          exact hjNe (by omega))

/-- Master per-entry invariant: every `j < sections.size` placed by
    `layoutSectionsFold` satisfies `Placement`.

    Note: `Placement` itself doesn't depend on `hSection0Null`, but the
    invariant proof bundles it into the foldl induction.  We supply
    `hSection0Null` here since the bundled motive requires it. -/
theorem layoutSectionsFold_placement (sections : Array Section) (cursor0 : Nat)
    (hSection0Null : ∀ (h : 0 < sections.size),
      (sections[0]'h).type = ShType.SHT_NULL)
    (j : Nat) (hj : j < sections.size) :
    Placement sections cursor0 (layoutSectionsFold sections cursor0) j :=
  (layoutSectionsFold_inv sections cursor0 hSection0Null).per_entry j hj

/-- Pairwise non-overlap: every pair of distinct output entries from
    `layoutSectionsFold` satisfies `PairDisjoint`. -/
theorem layoutSectionsFold_pairDisjoint (sections : Array Section) (cursor0 : Nat)
    (hSection0Null : ∀ (h : 0 < sections.size),
      (sections[0]'h).type = ShType.SHT_NULL)
    (j j' : Nat) (hj : j < sections.size) (hj' : j' < sections.size)
    (hNe : j ≠ j') :
    PairDisjoint (layoutSectionsFold sections cursor0) j j' :=
  (layoutSectionsFold_inv sections cursor0 hSection0Null).pair_disj j j' hj hj' hNe

end LayoutSectionsFold

/-! ## `layoutForEncoding` produces `spliceRegionsDisjoint`

    The bridge from the per-element invariants `LayoutSectionsFold.Placement`
    and `LayoutSectionsFold.PairDisjoint` to the byte-layer's 7-clause
    `spliceRegionsDisjoint` predicate.

    Preconditions (input-driven, all parser-derivable):
    * `hSection0Null`: `e.sections[0].type = SHT_NULL` (ELF spec; IsValid).
    * `hHeaderPhdr`: `e.header.phoff.val ≥ ehdrSize ∨ e.phdrs.size = 0`
      (the header doesn't overlap the phdr table).

    The shdr-table goes at `roundUp finalCursor 8` where `finalCursor`
    is at least `max ehdrSize (phoff + phnum*phdrSize)` (the initial
    cursor) and the phdr table fits inside `[phoff, phoff+phnum*phdrSize)`.
    We derive each clause from `Placement` (per-section bounds) and
    `cursor_floor` (the final cursor ≥ initial cursor). -/

/-- `layoutForEncoding` produces a layout where all 7 splice regions
    are pairwise disjoint.  The output is suitable as the input to
    `encode`'s splice cascade.

    Preconditions:
    * `hSection0Null`: shdr[0] is SHT_NULL (ELF spec invariant; parser's
      IsValid enforces it).
    * `hHeaderPhdr`: `Layout.ehdrSize ≤ e.header.phoff.val` — the
      header doesn't overlap the phdr table.  In practice every
      well-formed ELF has phoff = 64 (right after the 64-byte header). -/
theorem layoutForEncoding_produces_spliceRegionsDisjoint (e : ElfFile)
    (hSection0Null : ∀ (h : 0 < e.sections.size),
      (e.sections[0]'h).type = ShType.SHT_NULL)
    (hHeaderPhdr : Layout.ehdrSize ≤ e.header.phoff.val) :
    (layoutForEncoding e).spliceRegionsDisjoint := by
  -- Local vocabulary.
  let phEnd := e.header.phoff.val + e.phdrs.size * Layout.phdrSize
  let initialCursor := max Layout.ehdrSize phEnd
  let foldRes := layoutSectionsFold e.sections initialCursor
  let newSections := foldRes.1
  let finalCursor := foldRes.2
  let shoff := roundUp finalCursor 8
  -- Structural facts about layoutForEncoding e.
  -- The transformed file's `.sections` = newSections, `.header.shoff` = shoff,
  -- `.header.phoff` = e.header.phoff (unchanged), `.phdrs.size` = e.phdrs.size.
  have hSizeEq : newSections.size = e.sections.size :=
    LayoutSectionsFold.size_eq _ _
  have hCursorFloor : initialCursor ≤ finalCursor :=
    LayoutSectionsFold.cursor_floor _ _
  have hEhdrLeInit : Layout.ehdrSize ≤ initialCursor := Nat.le_max_left _ _
  have hPhEndLeInit : phEnd ≤ initialCursor := Nat.le_max_right _ _
  have hInitLeShoff : initialCursor ≤ shoff :=
    Nat.le_trans hCursorFloor (le_roundUp _ _)
  have hEhdrLeShoff : Layout.ehdrSize ≤ shoff :=
    Nat.le_trans hEhdrLeInit hInitLeShoff
  have hPhEndLeShoff : phEnd ≤ shoff :=
    Nat.le_trans hPhEndLeInit hInitLeShoff
  -- Per-entry placement for layoutSectionsFold.
  have hPlacement : ∀ (j : Nat) (hj : j < newSections.size),
      LayoutSectionsFold.Placement e.sections initialCursor foldRes j := by
    intros j hj
    have hjS : j < e.sections.size := hSizeEq ▸ hj
    exact LayoutSectionsFold.layoutSectionsFold_placement
      e.sections initialCursor hSection0Null j hjS
  -- Pairwise non-overlap.
  have hPair : ∀ (j j' : Nat) (hj : j < newSections.size)
                 (hj' : j' < newSections.size),
      j ≠ j' → LayoutSectionsFold.PairDisjoint foldRes j j' := by
    intros j j' hj hj' hNe
    have hjS : j < e.sections.size := hSizeEq ▸ hj
    have hj'S : j' < e.sections.size := hSizeEq ▸ hj'
    exact LayoutSectionsFold.layoutSectionsFold_pairDisjoint
      e.sections initialCursor hSection0Null j j' hjS hj'S hNe
  -- The transformed file's sections / shoff / phoff are these values.
  -- Verify by `rfl`-style reduction on layoutForEncoding's body.
  have hLfeSections : (layoutForEncoding e).sections = newSections := rfl
  have hLfeShoff : (layoutForEncoding e).header.shoff = ⟨shoff⟩ := rfl
  have hLfePhoff : (layoutForEncoding e).header.phoff = e.header.phoff := rfl
  have hLfePhdrsSize : (layoutForEncoding e).phdrs.size = e.phdrs.size := by
    show (e.phdrs.map _).size = _
    exact Array.size_map
  -- Build all 7 clauses.
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
    -- (layoutForEncoding e).sections = newSections by rfl, so the
    -- `hj : j < (layoutForEncoding e).sections.size` is the same as
    -- `j < newSections.size` definitionally.
    have hjN : j < newSections.size := hj
    have hj'N : j' < newSections.size := hj'
    exact hPair j j' hjN hj'N hNe hjN hj'N
  · -- hdr_phdr_disjoint
    show IntervalDisjoint 0 Layout.ehdrSize
      (layoutForEncoding e).header.phoff.val
      ((layoutForEncoding e).header.phoff.val
        + (layoutForEncoding e).phdrs.size * Layout.phdrSize)
    rw [hLfePhoff, hLfePhdrsSize]
    exact Or.inl hHeaderPhdr
  · -- hdr_shdr_disjoint
    show IntervalDisjoint 0 Layout.ehdrSize
      (layoutForEncoding e).header.shoff.val
      ((layoutForEncoding e).header.shoff.val
        + (layoutForEncoding e).sections.size * Layout.shdrSize)
    rw [hLfeShoff, hLfeSections]
    show IntervalDisjoint 0 Layout.ehdrSize shoff (shoff + newSections.size * Layout.shdrSize)
    exact Or.inl hEhdrLeShoff
  · -- phdr_shdr_disjoint
    show IntervalDisjoint
      (layoutForEncoding e).header.phoff.val
      ((layoutForEncoding e).header.phoff.val
        + (layoutForEncoding e).phdrs.size * Layout.phdrSize)
      (layoutForEncoding e).header.shoff.val
      ((layoutForEncoding e).header.shoff.val
        + (layoutForEncoding e).sections.size * Layout.shdrSize)
    rw [hLfePhoff, hLfePhdrsSize, hLfeShoff, hLfeSections]
    show IntervalDisjoint e.header.phoff.val phEnd shoff
            (shoff + newSections.size * Layout.shdrSize)
    exact Or.inl hPhEndLeShoff
  · -- hdr_sec_disjoint
    intros j hj
    have hjN : j < newSections.size := hj
    have hPl := hPlacement j hjN
    rcases hPl.offset_or with hExempt | hPlace
    · -- Exempt: derive NOBITS or NULL via the helper.
      rcases hPl.exempt_to_NOBITS_or_NULL hSection0Null hExempt with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · refine Or.inr (Or.inr (Or.inl ?_))
      show Layout.ehdrSize ≤ (newSections[j]'hjN).offset.val
      exact Nat.le_trans hEhdrLeInit hPlace.2.1
  · -- phdr_sec_disjoint
    intros j hj
    have hjN : j < newSections.size := hj
    have hPl := hPlacement j hjN
    show
      ((layoutForEncoding e).sections[j]'hj).type = ShType.SHT_NOBITS ∨
      ((layoutForEncoding e).sections[j]'hj).type = ShType.SHT_NULL ∨
      IntervalDisjoint
        (layoutForEncoding e).header.phoff.val
        ((layoutForEncoding e).header.phoff.val
          + (layoutForEncoding e).phdrs.size * Layout.phdrSize)
        ((layoutForEncoding e).sections[j]'hj).offset.val
        (((layoutForEncoding e).sections[j]'hj).offset.val
          + ((layoutForEncoding e).sections[j]'hj).encodedSize)
    rw [hLfePhoff, hLfePhdrsSize]
    rcases hPl.offset_or with hExempt | hPlace
    · rcases hPl.exempt_to_NOBITS_or_NULL hSection0Null hExempt with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · refine Or.inr (Or.inr (Or.inl ?_))
      show phEnd ≤ (newSections[j]'hjN).offset.val
      exact Nat.le_trans hPhEndLeInit hPlace.2.1
  · -- shdr_sec_disjoint
    intros j hj
    have hjN : j < newSections.size := hj
    have hPl := hPlacement j hjN
    show
      ((layoutForEncoding e).sections[j]'hj).type = ShType.SHT_NOBITS ∨
      ((layoutForEncoding e).sections[j]'hj).type = ShType.SHT_NULL ∨
      IntervalDisjoint
        (layoutForEncoding e).header.shoff.val
        ((layoutForEncoding e).header.shoff.val
          + (layoutForEncoding e).sections.size * Layout.shdrSize)
        ((layoutForEncoding e).sections[j]'hj).offset.val
        (((layoutForEncoding e).sections[j]'hj).offset.val
          + ((layoutForEncoding e).sections[j]'hj).encodedSize)
    rw [hLfeShoff]
    rcases hPl.offset_or with hExempt | hPlace
    · rcases hPl.exempt_to_NOBITS_or_NULL hSection0Null hExempt with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · refine Or.inr (Or.inr (Or.inr ?_))
      show (newSections[j]'hjN).offset.val + (newSections[j]'hjN).encodedSize ≤ shoff
      have hFinLeShoff : finalCursor ≤ shoff := le_roundUp _ _
      exact Nat.le_trans hPlace.2.2 hFinLeShoff

end Patchelf.Elf
