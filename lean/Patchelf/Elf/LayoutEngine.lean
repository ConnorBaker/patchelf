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

/-! ## Generic placement fold

    `placeStep` is the shared kernel of two layout strategies in the
    encoder pipeline:

    * `layoutForEncoding` (this module) — verbatim = `i = 0 ∨ NULL ∨
      NOBITS`, transform = `Section.withOffset`, baseOffset = 0.
    * `growEOFWith` (`GrowEOF.lean`) — verbatim = `¬ stale[i]`,
      transform updates both `offset` and `addr`, baseOffset =
      `startOffset` (the page-aligned end-of-file).

    Both feed the same `Placement` / `PairDisjoint` machinery and the
    same bridge to `spliceRegionsDisjoint`; only the verbatim predicate,
    transform, and baseOffset change.  See `placeFold_inv` for the
    master fold-induction theorem, and the `Section.withOffset`
    instantiation for `layoutForEncoding`. -/

/-- One step of the placement fold, parameterized by:
    * `verbatim` — predicate selecting which entries pass through
      unchanged (no cursor advance, original offset preserved).
    * `transform` — `(s, off) ↦ s'` placement function applied when
      verbatim is false.  Callers must supply `transform_*` lemmas
      stating how `s'`'s `type` / `encodedSize` / `offset.val` relate
      to the inputs.  See `placeStep_offset` and the master fold
      theorems for the contract.

    Threads `(acc, cursor)` (placed sections so far, current cumulative
    cursor — measured *relative* to `baseOffset` in the placed branch). -/
def placeStep
    (verbatim : Nat → Section → Bool)
    (transform : Section → Nat → Section)
    (acc : Array Section × Nat) (idxAndSec : Nat × Section) :
    Array Section × Nat :=
  let (i, s) := idxAndSec
  let (sectionsAcc, cursor) := acc
  if verbatim i s then
    (sectionsAcc.push s, cursor)
  else
    let off := roundUp cursor s.addralign.val
    (sectionsAcc.push (transform s off), off + s.encodedSize)

/-- The placement fold: walks sections, threading `(acc, cursor)`.
    See `placeStep` for the per-entry semantics.

    Foldl form (vs. tail-recursion) so proofs can use
    `Array.foldl_induction` directly. -/
def placeFold
    (verbatim : Nat → Section → Bool)
    (transform : Section → Nat → Section)
    (sections : Array Section) (cursor0 : Nat) :
    Array Section × Nat :=
  let indexed := sections.mapIdx (fun i s => (i, s))
  indexed.foldl (init := (Array.emptyWithCapacity sections.size, cursor0))
    (placeStep verbatim transform)

/-- One step of the layout fold (specialization of `placeStep` for
    `layoutForEncoding`).  Indexed step (i carries the section's
    original index in the input array — needed because section 0 is
    treated specially even when its type isn't SHT_NULL).  Threads
    `(acc, cursor)` (placed sections so far, current file offset). -/
def layoutVerbatim (i : Nat) (s : Section) : Bool :=
  decide (i = 0 ∨ s.type = ShType.SHT_NULL ∨ s.type = ShType.SHT_NOBITS)

@[inline] def layoutStep := placeStep layoutVerbatim Section.withOffset

/-- Layout fold helper: walks sections, threading `(acc, cursor)`
    (placed sections so far, current file offset).

    Section 0 and SHT_NULL sections are pushed verbatim (offset 0 /
    unchanged offset; consume no cursor).  SHT_NOBITS sections are
    also pushed verbatim (no file bytes).  Every other section is
    given a fresh `offset = roundUp cursor addralign` and `cursor`
    advances by `s.encodedSize`. -/
@[inline] def layoutSectionsFold := placeFold layoutVerbatim Section.withOffset

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

/-! ## `placeFold` structural facts (shared kernel)

    The fold-induction infrastructure is parameterized over `verbatim`
    (predicate selecting which entries pass through unchanged), `transform`
    (placement function for non-verbatim entries), and `baseOffset` (the
    constant absolute base, e.g. `0` for `layoutForEncoding` or
    `startOffset` for `growEOFWith`).  Callers supply the `transform_*`
    hypotheses bundled below; the master theorem `placeFold_inv` produces
    `Placement` and `PairDisjoint` facts for every output index. -/

namespace PlaceFold

/-- Bundles the field-preservation contract that any concrete `transform`
    must satisfy.  The `Placement` invariant is stated *abstractly* in
    these fields, so each client just exhibits its own `Spec` instance. -/
structure TransformSpec (transform : Section → Nat → Section) (baseOffset : Nat) : Prop where
  type_eq        : ∀ (s : Section) (o : Nat), (transform s o).type = s.type
  encodedSize_eq : ∀ (s : Section) (o : Nat), (transform s o).encodedSize = s.encodedSize
  offset_eq      : ∀ (s : Section) (o : Nat), (transform s o).offset.val = baseOffset + o

variable {verbatim : Nat → Section → Bool}
variable {transform : Section → Nat → Section} {baseOffset : Nat}

/-- One step of the placement fold advances `acc.size` by 1. -/
theorem step_size_eq (acc : Array Section × Nat)
    (idx : Nat) (s : Section) :
    (placeStep verbatim transform acc (idx, s)).1.size = acc.1.size + 1 := by
  unfold placeStep
  by_cases hAlt : verbatim idx s
  · simp [hAlt, Array.size_push]
  · simp [hAlt, Array.size_push]

/-- One step of the placement fold's cursor is monotone. -/
theorem step_cursor_mono (acc : Array Section × Nat)
    (idx : Nat) (s : Section) :
    acc.2 ≤ (placeStep verbatim transform acc (idx, s)).2 := by
  unfold placeStep
  by_cases hAlt : verbatim idx s
  · simp [hAlt]
  · simp [hAlt]
    have := le_roundUp acc.2 s.addralign.val
    omega

/-- For any index `j < state.1.size` (i.e. valid in the pre-step state),
    the post-step `getElem` agrees with the pre-step `getElem`.  Both
    branches of `placeStep` push exactly one element, so existing
    indices read through to the original. -/
theorem step_getElem_lt (state : Array Section × Nat)
    (idx : Nat) (s : Section) (j : Nat) (hjLt : j < state.1.size) :
    (placeStep verbatim transform state (idx, s)).1[j]'(by rw [step_size_eq]; omega)
      = state.1[j]'hjLt := by
  unfold placeStep
  by_cases hAlt : verbatim idx s
  · simp [hAlt]; rw [Array.getElem_push_lt hjLt]
  · simp [hAlt]; rw [Array.getElem_push_lt hjLt]

/-! Size + cursor floor invariants. -/

theorem size_eq (sections : Array Section) (cursor0 : Nat) :
    (placeFold verbatim transform sections cursor0).1.size = sections.size := by
  unfold placeFold
  let indexed := sections.mapIdx (fun i s => (i, s))
  have hIndexedSize : indexed.size = sections.size := Array.size_mapIdx
  show (Array.foldl (placeStep verbatim transform)
        (Array.emptyWithCapacity sections.size, cursor0) indexed).1.size
        = sections.size
  rw [show sections.size = indexed.size from hIndexedSize.symm] at *
  have h := @Array.foldl_induction (Nat × Section) (Array Section × Nat) indexed
    (motive := fun k state => state.1.size = k)
    (init := (Array.emptyWithCapacity indexed.size, cursor0))
    (h0 := by simp)
    (f := placeStep verbatim transform)
    (hf := by
      intros i state ih
      rw [step_size_eq, ih])
  exact h

theorem cursor_floor (sections : Array Section) (cursor0 : Nat) :
    cursor0 ≤ (placeFold verbatim transform sections cursor0).2 := by
  unfold placeFold
  let indexed := sections.mapIdx (fun i s => (i, s))
  show cursor0 ≤
      (Array.foldl (placeStep verbatim transform)
        (Array.emptyWithCapacity sections.size, cursor0) indexed).2
  have h := @Array.foldl_induction (Nat × Section) (Array Section × Nat) indexed
    (motive := fun _ state => cursor0 ≤ state.2)
    (init := (Array.emptyWithCapacity sections.size, cursor0))
    (h0 := Nat.le_refl _)
    (f := placeStep verbatim transform)
    (hf := by
      intros i state ih
      exact Nat.le_trans ih (step_cursor_mono state _ _))
  exact h

/-! ## Per-entry placement invariant

    `Placement` records the per-entry guarantee for an output position
    `j < state.1.size`:

    * `.type` and `.encodedSize` are inherited from `sections[j]`,
    * either the entry is verbatim, with `offset = sections[j].offset`,
    * or it has fresh offset `o` with
      `baseOffset + cursor0 ≤ o` and `o + encodedSize ≤ baseOffset + state.2`.

    Note: the placed-branch bound uses `baseOffset + cursor0` (an
    *absolute* lower bound) rather than `cursor0` (the relative one).
    This matches both clients: `layoutForEncoding` has `baseOffset = 0`
    and `cursor0 = max ehdrSize phEnd`, while `growEOFWith` has
    `baseOffset = startOffset` and `cursor0 = 0`. -/
structure Placement
    (verbatim : Nat → Section → Bool) (baseOffset : Nat)
    (sections : Array Section) (cursor0 : Nat)
    (state : Array Section × Nat) (j : Nat) : Prop where
  hjA : j < state.1.size
  hjS : j < sections.size
  type_eq : (state.1[j]'hjA).type = (sections[j]'hjS).type
  size_eq : (state.1[j]'hjA).encodedSize = (sections[j]'hjS).encodedSize
  offset_or :
    (verbatim j (sections[j]'hjS) = true ∧
        (state.1[j]'hjA).offset = (sections[j]'hjS).offset)
     ∨ (verbatim j (sections[j]'hjS) = false ∧
        baseOffset + cursor0 ≤ (state.1[j]'hjA).offset.val ∧
        (state.1[j]'hjA).offset.val + (state.1[j]'hjA).encodedSize
          ≤ baseOffset + state.2)

/-- Stability of `Placement` under a placement step: existing entries
    survive the push + cursor advance unchanged. -/
theorem placement_step_existing (sections : Array Section) (cursor0 : Nat)
    (state : Array Section × Nat) (idx : Nat) (s : Section) (j : Nat)
    (hPl : Placement verbatim baseOffset sections cursor0 state j) :
    Placement verbatim baseOffset sections cursor0
      (placeStep verbatim transform state (idx, s)) j := by
  have hCurLe : state.2 ≤ (placeStep verbatim transform state (idx, s)).2 :=
    step_cursor_mono state idx s
  have hjA' : j < (placeStep verbatim transform state (idx, s)).1.size := by
    rw [step_size_eq]; have := hPl.hjA; omega
  have hPushEq : (placeStep verbatim transform state (idx, s)).1[j]'hjA'
                  = state.1[j]'hPl.hjA :=
    step_getElem_lt state idx s j hPl.hjA
  refine
    { hjA := hjA'
      hjS := hPl.hjS
      type_eq := ?_
      size_eq := ?_
      offset_or := ?_ }
  · rw [hPushEq]; exact hPl.type_eq
  · rw [hPushEq]; exact hPl.size_eq
  · rcases hPl.offset_or with hVerb | hPlace
    · refine Or.inl ⟨hVerb.1, ?_⟩
      rw [hPushEq]; exact hVerb.2
    · refine Or.inr ⟨hPlace.1, ?_, ?_⟩
      · rw [hPushEq]; exact hPlace.2.1
      · rw [hPushEq]; exact Nat.le_trans hPlace.2.2 (Nat.add_le_add_left hCurLe _)

/-- The freshly-pushed entry has `Placement`. -/
theorem placement_step_new (hSpec : TransformSpec transform baseOffset)
    (sections : Array Section) (cursor0 : Nat)
    (state : Array Section × Nat) (i : Nat) (s : Section)
    (hSize : state.1.size = i)
    (hCur : cursor0 ≤ state.2)
    (hiBound : i < sections.size)
    (hSeq : sections[i]'hiBound = s) :
    Placement verbatim baseOffset sections cursor0
      (placeStep verbatim transform state (i, s)) i := by
  subst hSize
  have hjA : state.1.size < (placeStep verbatim transform state (state.1.size, s)).1.size := by
    rw [step_size_eq]; omega
  by_cases hAlt : verbatim state.1.size s = true
  · -- Verbatim: pushed `s` unchanged.
    have hValEq : (placeStep verbatim transform state (state.1.size, s)).1[state.1.size]'hjA = s := by
      unfold placeStep
      simp only [hAlt]
      exact Array.getElem_push_eq
    refine
      { hjA := hjA, hjS := hiBound,
        type_eq := ?_, size_eq := ?_, offset_or := ?_ }
    · rw [hValEq, hSeq]
    · rw [hValEq, hSeq]
    · refine Or.inl ⟨?_, ?_⟩
      · rw [hSeq]; exact hAlt
      · rw [hValEq, hSeq]
  · -- Placed: pushed `transform s off`, where `off = roundUp state.2 ...`.
    have hAltFalse : verbatim state.1.size s = false := by
      cases h : verbatim state.1.size s
      · rfl
      · exact absurd h hAlt
    let off := roundUp state.2 s.addralign.val
    have hValEq : (placeStep verbatim transform state (state.1.size, s)).1[state.1.size]'hjA
                 = transform s off := by
      unfold placeStep
      simp only [hAlt]
      exact Array.getElem_push_eq
    have hCurEq : (placeStep verbatim transform state (state.1.size, s)).2
                 = off + s.encodedSize := by
      unfold placeStep
      simp only [hAlt]
      rfl
    refine
      { hjA := hjA, hjS := hiBound,
        type_eq := ?_, size_eq := ?_, offset_or := ?_ }
    · rw [hValEq, hSpec.type_eq, hSeq]
    · rw [hValEq, hSpec.encodedSize_eq, hSeq]
    · refine Or.inr ⟨?_, ?_, ?_⟩
      · rw [hSeq]; exact hAltFalse
      · rw [hValEq, hSpec.offset_eq]
        -- baseOffset + cursor0 ≤ baseOffset + off, since cursor0 ≤ state.2 ≤ off.
        have hRoundUpGe : state.2 ≤ roundUp state.2 s.addralign.val := le_roundUp _ _
        have hCurOff : cursor0 ≤ off := Nat.le_trans hCur hRoundUpGe
        exact Nat.add_le_add_left hCurOff _
      · rw [hValEq, hSpec.offset_eq, hSpec.encodedSize_eq, hCurEq]
        -- baseOffset + off + s.encodedSize ≤ baseOffset + (off + s.encodedSize).
        omega

/-- Pairwise non-overlap claim for two output entries `j ≠ j'`:
    either at least one is NOBITS / NULL, or their byte ranges
    `[offset, offset+encodedSize)` are interval-disjoint.

    Disjunct order matches `ElfFile.sectionsNonOverlapping`'s
    NOBITS-NOBITS-NULL-NULL-IntervalDisjoint shape so the bridge to
    `spliceRegionsDisjoint` composes by `exact`. -/
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
  rcases h with h | h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inl h))
  · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
    rcases h with hL | hR
    · exact Or.inr hL
    · exact Or.inl hR

/-- Stability of `PairDisjoint` under a placement step: indices
    `< state.1.size` survive the push (getElem unchanged). -/
theorem pairDisjoint_step_existing
    (state : Array Section × Nat) (idx : Nat) (s : Section)
    (j j' : Nat) (hjLt : j < state.1.size) (hjLt' : j' < state.1.size)
    (hPD : PairDisjoint state j j') :
    PairDisjoint (placeStep verbatim transform state (idx, s)) j j' := by
  unfold PairDisjoint
  intros _ _
  rw [step_getElem_lt state idx s j hjLt,
      step_getElem_lt state idx s j' hjLt']
  exact hPD hjLt hjLt'

/-- Client-supplied "structural" witnesses for verbatim entries.  Bundles
    two facts that fall out of the input invariants:

    * `bound` — every verbatim entry is NULL, NOBITS, or its file range
      ends at or before `baseOffset`.  The third disjunct lets `growEOFWith`
      handle non-stale non-NULL non-NOBITS entries (they sit inside the
      original file region, which ends below the appended region's start).
    * `pair_disj` — any two distinct verbatim entries are pairwise
      disjoint (NULL/NOBITS short-circuit, or their file ranges
      `[offset, offset + encodedSize)` are interval-disjoint).

    For `layoutForEncoding` (`baseOffset = 0`), `bound` is satisfied
    via NULL/NOBITS only (combined with `hSection0Null`); `pair_disj`
    is vacuous in non-NULL/NOBITS shape since both entries fall under
    NULL/NOBITS.

    For `growEOFWith` (`baseOffset = startOffset`), both come from
    `sectionStale = false` for non-stale entries: the file range is
    bounded by `currentFileEnd ≤ startOffset`, and `sectionOverlapsAny
    = false` directly gives pairwise disjointness. -/
structure VerbatimWitness
    (verbatim : Nat → Section → Bool) (baseOffset : Nat)
    (sections : Array Section) : Prop where
  bound : ∀ (j : Nat) (hjS : j < sections.size),
    verbatim j (sections[j]'hjS) = true →
    (sections[j]'hjS).type = ShType.SHT_NULL ∨
    (sections[j]'hjS).type = ShType.SHT_NOBITS ∨
    (sections[j]'hjS).offset.val + (sections[j]'hjS).encodedSize ≤ baseOffset
  pair_disj : ∀ (j j' : Nat) (hj : j < sections.size) (hj' : j' < sections.size),
    j ≠ j' →
    verbatim j (sections[j]'hj) = true →
    verbatim j' (sections[j']'hj') = true →
    (sections[j]'hj).type = ShType.SHT_NOBITS ∨
    (sections[j']'hj').type = ShType.SHT_NOBITS ∨
    (sections[j]'hj).type = ShType.SHT_NULL ∨
    (sections[j']'hj').type = ShType.SHT_NULL ∨
    IntervalDisjoint
      (sections[j]'hj).offset.val
      ((sections[j]'hj).offset.val + (sections[j]'hj).encodedSize)
      (sections[j']'hj').offset.val
      ((sections[j']'hj').offset.val + (sections[j']'hj').encodedSize)

/-- New-entry vs. existing-entry disjointness: at the step that places
    a new entry at `state.1.size = i`, its byte range is interval-disjoint
    from any existing entry's range.

    Three cases by how the new entry and existing entry j are pushed:

    - Both verbatim: `hVerb.pair_disj` applies directly (file ranges
      preserved on both sides).
    - One verbatim, one placed: the placed side is bounded by
      `baseOffset + cursor0`-ish, the verbatim side by the bound disjunct
      of `hVerb.bound`.  Combine for a separator at `baseOffset`.
    - Both placed: cursor monotonicity gives the clean separator.

    NOTE: `_hCur` is part of the master-fold contract (the cursor floor
    invariant passed by `placeFold_inv`); not directly used here, kept
    for API symmetry with `placement_step_new`. -/
theorem pairDisjoint_step_new_vs_old (hSpec : TransformSpec transform baseOffset)
    (sections : Array Section) (cursor0 : Nat)
    (state : Array Section × Nat) (i : Nat) (s : Section) (j : Nat)
    (hSize : state.1.size = i)
    (_hCur : cursor0 ≤ state.2)
    (hiBound : i < sections.size)
    (hSeq : sections[i]'hiBound = s)
    (hjLt : j < state.1.size)
    (hjNe : j ≠ i)
    (hPlj : Placement verbatim baseOffset sections cursor0 state j)
    (hVerb : VerbatimWitness verbatim baseOffset sections) :
    PairDisjoint (placeStep verbatim transform state (i, s)) j i := by
  unfold PairDisjoint
  intros _ hjA'
  -- For the j (existing) entry: getElem is preserved by the push.
  have hPushEqJ : (placeStep verbatim transform state (i, s)).1[j]'_ = state.1[j]'hjLt :=
    step_getElem_lt state i s j hjLt
  by_cases hAlt : verbatim i s = true
  · -- New entry verbatim: pushed `s` unchanged.
    have hPushEqI : (placeStep verbatim transform state (i, s)).1[i]'hjA' = s := by
      subst hSize
      unfold placeStep
      simp only [hAlt]
      exact Array.getElem_push_eq
    rw [hPushEqI, hPushEqJ]
    have hVerbI : verbatim i (sections[i]'hiBound) = true := by rw [hSeq]; exact hAlt
    rcases hPlj.offset_or with hVerbJ | hPlacej
    · -- Both verbatim: apply hVerb.pair_disj directly, then rewrite to state.
      have hVerbJ' : verbatim j (sections[j]'hPlj.hjS) = true := hVerbJ.1
      have hPair := hVerb.pair_disj j i hPlj.hjS hiBound hjNe hVerbJ' hVerbI
      have hOffJ : (state.1[j]'hjLt).offset.val = (sections[j]'hPlj.hjS).offset.val := by
        rw [hVerbJ.2]
      have hSzJ : (state.1[j]'hjLt).encodedSize = (sections[j]'hPlj.hjS).encodedSize :=
        hPlj.size_eq
      have hTyJ : (state.1[j]'hjLt).type = (sections[j]'hPlj.hjS).type := hPlj.type_eq
      rcases hPair with hN | hN | hN | hN | hID
      · exact Or.inl (hTyJ.trans hN)
      · exact Or.inr (Or.inl (by rw [← hSeq]; exact hN))
      · exact Or.inr (Or.inr (Or.inl (hTyJ.trans hN)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [← hSeq]; exact hN))))
      · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
        rw [hOffJ, hSzJ, ← hSeq]; exact hID
    · -- j placed, new entry verbatim: bound on new entry ⇒ disjoint left.
      rcases hVerb.bound i hiBound hVerbI with hN | hNB | hBnd
      · -- s = sections[i] is NULL.
        refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
        rw [← hSeq]; exact hN
      · -- s = sections[i] is NOBITS.
        refine Or.inr (Or.inl ?_)
        rw [← hSeq]; exact hNB
      · -- File-range bound: sections[i].range ≤ baseOffset ≤ baseOffset + cursor0 ≤ j.offset.
        refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
        right
        show s.offset.val + s.encodedSize ≤ (state.1[j]'hjLt).offset.val
        rw [← hSeq]
        have hLeBase : (sections[i]'hiBound).offset.val + (sections[i]'hiBound).encodedSize
                      ≤ baseOffset := hBnd
        have hBaseLeJ : baseOffset ≤ (state.1[j]'hjLt).offset.val := by
          have := hPlacej.2.1
          omega
        omega
  · -- New entry placed: pushed `transform s off`, where off ≥ state.2.
    have hAltFalse : verbatim i s = false := by
      cases h : verbatim i s
      · rfl
      · exact absurd h hAlt
    let off := roundUp state.2 s.addralign.val
    have hPushEqI : (placeStep verbatim transform state (i, s)).1[i]'hjA' = transform s off := by
      subst hSize
      unfold placeStep
      simp only [hAlt]
      exact Array.getElem_push_eq
    rw [hPushEqI, hPushEqJ]
    rcases hPlj.offset_or with hVerbJ | hPlacej
    · -- j verbatim, new entry placed.
      have hVerbJ' : verbatim j (sections[j]'hPlj.hjS) = true := hVerbJ.1
      rcases hVerb.bound j hPlj.hjS hVerbJ' with hN | hNB | hBndJ
      · refine Or.inr (Or.inr (Or.inl ?_)); exact hPlj.type_eq.trans hN
      · exact Or.inl (hPlj.type_eq.trans hNB)
      · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
        left
        show (state.1[j]'hjLt).offset.val + (state.1[j]'hjLt).encodedSize
            ≤ (transform s off).offset.val
        rw [hSpec.offset_eq]
        have hOffJ : (state.1[j]'hjLt).offset.val = (sections[j]'hPlj.hjS).offset.val := by
          rw [hVerbJ.2]
        have hSzJ : (state.1[j]'hjLt).encodedSize = (sections[j]'hPlj.hjS).encodedSize :=
          hPlj.size_eq
        rw [hOffJ, hSzJ]
        -- state[j].range ≤ baseOffset; new entry at baseOffset + off ≥ baseOffset.
        omega
    · -- Both placed: cursor-monotone separator.
      refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
      left
      show (state.1[j]'hjLt).offset.val + (state.1[j]'hjLt).encodedSize
          ≤ (transform s off).offset.val
      rw [hSpec.offset_eq]
      have hRoundUpGe : state.2 ≤ off := le_roundUp _ _
      have hLe : (state.1[j]'hjLt).offset.val + (state.1[j]'hjLt).encodedSize
                ≤ baseOffset + state.2 := hPlacej.2.2
      omega

/-- Strengthened motive for the placement fold: size, cursor floor,
    per-entry placement, and pairwise non-overlap. -/
structure FoldInv
    (verbatim : Nat → Section → Bool) (baseOffset : Nat)
    (sections : Array Section) (cursor0 : Nat)
    (k : Nat) (state : Array Section × Nat) : Prop where
  size_eq : state.1.size = k
  cursor_floor : cursor0 ≤ state.2
  per_entry : ∀ (j : Nat), j < k →
    Placement verbatim baseOffset sections cursor0 state j
  pair_disj : ∀ (j j' : Nat), j < k → j' < k → j ≠ j' →
    PairDisjoint state j j'

/-- Master fold-induction invariant.  Bundles size, cursor floor,
    per-entry placement, and pairwise non-overlap.

    Closed at `k = sections.size`, this gives every output entry's
    `Placement` and `PairDisjoint` for any pair of distinct indices. -/
theorem placeFold_inv (hSpec : TransformSpec transform baseOffset)
    (sections : Array Section) (cursor0 : Nat)
    (hVerb : VerbatimWitness verbatim baseOffset sections) :
    FoldInv verbatim baseOffset sections cursor0 sections.size
      (placeFold verbatim transform sections cursor0) := by
  unfold placeFold
  let indexed := sections.mapIdx (fun i s => (i, s))
  have hIndexedSize : indexed.size = sections.size := Array.size_mapIdx
  show FoldInv verbatim baseOffset sections cursor0 sections.size
    (Array.foldl (placeStep verbatim transform)
      (Array.emptyWithCapacity sections.size, cursor0) indexed)
  rw [show sections.size = indexed.size from hIndexedSize.symm]
  apply @Array.foldl_induction (Nat × Section) (Array Section × Nat) indexed
    (motive := FoldInv verbatim baseOffset sections cursor0)
    (init := (Array.emptyWithCapacity sections.size, cursor0))
    (h0 := by
      refine ⟨?_, Nat.le_refl _, ?_, ?_⟩
      · simp
      · intros j hj; exact absurd hj (Nat.not_lt_zero _)
      · intros j j' hj _ _; exact absurd hj (Nat.not_lt_zero _))
    (f := placeStep verbatim transform)
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
          exact placement_step_new hSpec sections cursor0 state i.val
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
          exact pairDisjoint_step_new_vs_old hSpec sections cursor0 state i.val
                  (sections[i.val]'hiBound) j ih.size_eq ih.cursor_floor
                  hiBound rfl hjOld hjNe (ih.per_entry j hjOldK) hVerb
        · -- j new, j' old: symmetric to above.
          have hjOldK' : j' < i.val := by rw [ih.size_eq] at hjOld'; exact hjOld'
          have hjGe : state.1.size ≤ j := Nat.le_of_not_lt hjOld
          have hjEq : i.val = j := by
            rw [ih.size_eq] at hjGe; omega
          subst hjEq
          exact pairDisjoint_symm _ _ _
            (pairDisjoint_step_new_vs_old hSpec sections cursor0 state i.val
              (sections[i.val]'hiBound) j' ih.size_eq ih.cursor_floor
              hiBound rfl hjOld' hjNe.symm (ih.per_entry j' hjOldK') hVerb)
        · -- both new: contradicts hjNe (both equal state.1.size = i.val).
          exfalso
          have hjGe : state.1.size ≤ j := Nat.le_of_not_lt hjOld
          have hjGe' : state.1.size ≤ j' := Nat.le_of_not_lt hjOld'
          rw [ih.size_eq] at hjGe hjGe'
          exact hjNe (by omega))

/-- Master per-entry invariant: every `j < sections.size` placed by
    `placeFold` satisfies `Placement`. -/
theorem placeFold_placement (hSpec : TransformSpec transform baseOffset)
    (sections : Array Section) (cursor0 : Nat)
    (hVerb : VerbatimWitness verbatim baseOffset sections)
    (j : Nat) (hj : j < sections.size) :
    Placement verbatim baseOffset sections cursor0
      (placeFold verbatim transform sections cursor0) j :=
  (placeFold_inv hSpec sections cursor0 hVerb).per_entry j hj

/-- Pairwise non-overlap: every pair of distinct output entries from
    `placeFold` satisfies `PairDisjoint`. -/
theorem placeFold_pairDisjoint (hSpec : TransformSpec transform baseOffset)
    (sections : Array Section) (cursor0 : Nat)
    (hVerb : VerbatimWitness verbatim baseOffset sections)
    (j j' : Nat) (hj : j < sections.size) (hj' : j' < sections.size)
    (hNe : j ≠ j') :
    PairDisjoint (placeFold verbatim transform sections cursor0) j j' :=
  (placeFold_inv hSpec sections cursor0 hVerb).pair_disj j j' hj hj' hNe

/-! ## Per-entry section-value witness

    `Placement` exposes `type_eq`, `size_eq`, and `offset_or` — a partial
    view of how each output entry relates to the input.  For
    `_preserves_valid` proofs we need MORE: the actual section value at
    every output index, so that per-field projections (name, content,
    link, …) can be derived for the per-entry IsValid clauses that
    don't bottom out in the three exposed fields.

    `ValueInv` records the foldl-induction motive carrying both
    `state.1.size = k` and the per-entry value witness.  Closed at
    `k = sections.size`, the resulting `placeFold_value_witness` is
    a structural fact about `placeStep`/`placeFold` independent of
    `TransformSpec` and `VerbatimWitness`. -/

/-- Foldl-induction motive: at step k, `state.1.size = k` and every
    output index `j < k` has a verbatim/transform witness. -/
structure ValueInv
    (verbatim : Nat → Section → Bool)
    (transform : Section → Nat → Section)
    (sections : Array Section)
    (k : Nat) (state : Array Section × Nat) : Prop where
  size_eq : state.1.size = k
  per_entry : ∀ (j : Nat) (_hjLt : j < k) (hjA : j < state.1.size)
                (hjS : j < sections.size),
    (verbatim j (sections[j]'hjS) = true ∧
        state.1[j]'hjA = sections[j]'hjS) ∨
    (verbatim j (sections[j]'hjS) = false ∧
        ∃ off, state.1[j]'hjA = transform (sections[j]'hjS) off)

/-- `placeFold` produces a fold-state where every output entry's value
    is either the input section verbatim or `transform input off` for
    some `off`.  Foundation for per-field preservation. -/
theorem placeFold_value_inv
    (sections : Array Section) (cursor0 : Nat) :
    ValueInv verbatim transform sections sections.size
      (placeFold verbatim transform sections cursor0) := by
  unfold placeFold
  let indexed := sections.mapIdx (fun i s => (i, s))
  have hIndexedSize : indexed.size = sections.size := Array.size_mapIdx
  show ValueInv verbatim transform sections sections.size
    (Array.foldl (placeStep verbatim transform)
      (Array.emptyWithCapacity sections.size, cursor0) indexed)
  rw [show sections.size = indexed.size from hIndexedSize.symm]
  apply @Array.foldl_induction (Nat × Section) (Array Section × Nat) indexed
    (motive := ValueInv verbatim transform sections)
    (init := (Array.emptyWithCapacity sections.size, cursor0))
    (h0 := by
      refine ⟨?_, ?_⟩
      · simp
      · intros j hjLt _ _; exact absurd hjLt (Nat.not_lt_zero _))
    (f := placeStep verbatim transform)
    (hf := by
      intros i state ih
      obtain ⟨hSize, ihAll⟩ := ih
      have hiBound : i.val < sections.size := hIndexedSize ▸ i.isLt
      have hSeq : indexed[i] = (i.val, sections[i.val]'hiBound) := by
        show indexed[i.val] = _; rw [Array.getElem_mapIdx]
      rw [hSeq]
      refine ⟨?_, ?_⟩
      · -- size_eq for the next step.
        rw [step_size_eq, hSize]
      · -- per_entry
        intros j hjLt hjA hjS
        by_cases hjOld : j < state.1.size
        · -- Existing entry: step_getElem_lt + IH.
          rw [step_getElem_lt state i.val _ j hjOld]
          have hjLtOld : j < ↑i := hSize ▸ hjOld
          exact ihAll j hjLtOld hjOld hjS
        · -- New entry: j = state.1.size = i.val.
          -- Following `placement_step_new`'s pattern: prove a specialized
          -- value-equation as a `have`, then use it to discharge both
          -- disjunction cases.
          have hjGe : state.1.size ≤ j := Nat.le_of_not_lt hjOld
          have hjEq : j = state.1.size := by
            have : j < state.1.size + 1 := by
              rw [step_size_eq] at hjA; exact hjA
            omega
          -- The goal references `sections[j]'hjS`.  Once we know j = state.1.size = i.val,
          -- it equals `sections[i.val]'hiBound`.  Build that equality up front.
          have hSecEq : sections[j]'hjS = sections[i.val]'hiBound := by
            congr 1
            rw [hjEq, hSize]
          -- Verbatim/placed dispatch.
          by_cases hAlt : verbatim i.val (sections[i.val]'hiBound) = true
          · -- Verbatim: state.1[j] = sections[i.val].
            have hValEq : (placeStep verbatim transform state
                            (i.val, sections[i.val]'hiBound)).1[j]'hjA
                          = sections[i.val]'hiBound := by
              unfold placeStep
              simp only [hAlt, ↓reduceIte]
              -- Goal: (state.1.push sections[i.val]).getElem j _ = sections[i.val].
              -- j = state.1.size, so this is push_eq.
              have hJ : j = state.1.size := hjEq
              subst hJ
              exact Array.getElem_push_eq
            -- The goal's verbatim takes j; we need to rewrite j ↦ i.val.
            have hjVal : j = i.val := by rw [hjEq, hSize]
            refine Or.inl ⟨?_, ?_⟩
            · rw [hSecEq, hjVal]; exact hAlt
            · rw [hValEq, hSecEq]
          · -- Placed: state.1[j] = transform sections[i.val] off.
            have hAltF : verbatim i.val (sections[i.val]'hiBound) = false := by
              cases h : verbatim i.val (sections[i.val]'hiBound)
              · rfl
              · exact absurd h hAlt
            let off := roundUp state.2 (sections[i.val]'hiBound).addralign.val
            have hValEq : (placeStep verbatim transform state
                            (i.val, sections[i.val]'hiBound)).1[j]'hjA
                          = transform (sections[i.val]'hiBound) off := by
              unfold placeStep
              simp only [hAltF, Bool.false_eq_true, ↓reduceIte]
              have hJ : j = state.1.size := hjEq
              subst hJ
              exact Array.getElem_push_eq
            have hjVal : j = i.val := by rw [hjEq, hSize]
            refine Or.inr ⟨?_, off, ?_⟩
            · rw [hSecEq, hjVal]; exact hAltF
            · rw [hValEq, hSecEq])

/-- Per-entry value witness: every output index of `placeFold` is
    either the input section unchanged (verbatim) or `transform input
    off` for some offset (placed).  The structural fact that
    `_preserves_valid` proofs consume to derive per-field
    preservation. -/
theorem placeFold_value_witness
    (sections : Array Section) (cursor0 : Nat)
    (j : Nat) (hjS : j < sections.size)
    (hjA : j < (placeFold verbatim transform sections cursor0).1.size) :
    (verbatim j (sections[j]'hjS) = true ∧
        (placeFold verbatim transform sections cursor0).1[j]'hjA
          = sections[j]'hjS) ∨
    (verbatim j (sections[j]'hjS) = false ∧
        ∃ off, (placeFold verbatim transform sections cursor0).1[j]'hjA
                  = transform (sections[j]'hjS) off) :=
  (placeFold_value_inv sections cursor0).per_entry j (size_eq .. ▸ hjA) hjA hjS

end PlaceFold

/-! ## `Section.withOffset` instantiation for `layoutForEncoding`

    `withOffset` only rewrites `offset`; it preserves type, content
    (hence `encodedSize`), and `addralign`.  The `TransformSpec` for
    `Section.withOffset` with `baseOffset = 0` is direct. -/

/-- `Section.withOffset` is a `TransformSpec` with `baseOffset = 0`. -/
theorem withOffset_transformSpec :
    PlaceFold.TransformSpec Section.withOffset 0 :=
  { type_eq        := fun _ _ => rfl
    encodedSize_eq := fun _ _ => withOffset_encodedSize _ _
    offset_eq      := fun s o => by
      show (Section.withOffset s o).offset.val = 0 + o
      have h : (Section.withOffset s o).offset.val = o := rfl
      omega }

/-- Verbatim-witness for `layoutForEncoding`'s verbatim predicate
    (`i = 0 ∨ NULL ∨ NOBITS`).  Combined with `hSection0Null`, every
    verbatim entry is NULL or NOBITS, so the `bound` and `pair_disj`
    fields are trivially satisfied (NULL/NOBITS short-circuits both). -/
theorem layoutVerbatimWitness {sections : Array Section}
    (hSection0Null : ∀ (h : 0 < sections.size),
      (sections[0]'h).type = ShType.SHT_NULL) :
    PlaceFold.VerbatimWitness layoutVerbatim 0 sections := by
  refine ⟨?_, ?_⟩
  · intros j hjS hVerb
    -- verbatim → j=0 ∨ NULL ∨ NOBITS
    have : j = 0 ∨ (sections[j]'hjS).type = ShType.SHT_NULL ∨
           (sections[j]'hjS).type = ShType.SHT_NOBITS := by
      have h := decide_eq_true_iff.mp hVerb
      exact h
    rcases this with h0 | hN | hNB
    · subst h0; exact Or.inl (hSection0Null hjS)
    · exact Or.inl hN
    · exact Or.inr (Or.inl hNB)
  · intros j j' hj hj' _ hVerbJ hVerbJ'
    -- Both verbatim → both NULL/NOBITS (modulo the j=0 case via hSection0Null).
    have hJ : j = 0 ∨ (sections[j]'hj).type = ShType.SHT_NULL ∨
              (sections[j]'hj).type = ShType.SHT_NOBITS :=
      decide_eq_true_iff.mp hVerbJ
    have hJ' : j' = 0 ∨ (sections[j']'hj').type = ShType.SHT_NULL ∨
               (sections[j']'hj').type = ShType.SHT_NOBITS :=
      decide_eq_true_iff.mp hVerbJ'
    rcases hJ with h0 | hN | hNB
    · subst h0
      exact Or.inr (Or.inr (Or.inl (hSection0Null hj)))
    · exact Or.inr (Or.inr (Or.inl hN))
    · exact Or.inl hNB

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
    * `hHeaderPhdr`: header byte range and phdr table don't overlap.
      The clause `IntervalDisjoint 0 ehdrSize phoff (phoff + phnum * phdrSize)`,
      satisfied by every well-formed ELF (phoff = 64 right after the 64-byte
      header) and also by degenerate inputs with `phdrs.size = 0`. -/
theorem layoutForEncoding_produces_spliceRegionsDisjoint (e : ElfFile)
    (hSection0Null : ∀ (h : 0 < e.sections.size),
      (e.sections[0]'h).type = ShType.SHT_NULL)
    (hHeaderPhdr : e.headerPhdrDisjoint) :
    (layoutForEncoding e).spliceRegionsDisjoint := by
  -- Local vocabulary.
  let phEnd := e.header.phoff.val + e.phdrs.size * Layout.phdrSize
  let initialCursor := max Layout.ehdrSize phEnd
  let foldRes := layoutSectionsFold e.sections initialCursor
  let newSections := foldRes.1
  let finalCursor := foldRes.2
  let shoff := roundUp finalCursor 8
  have hSpec := withOffset_transformSpec
  have hVerb := layoutVerbatimWitness hSection0Null
  -- Structural facts.
  have hSizeEq : newSections.size = e.sections.size :=
    PlaceFold.size_eq _ _
  have hCursorFloor : initialCursor ≤ finalCursor :=
    PlaceFold.cursor_floor _ _
  have hEhdrLeInit : Layout.ehdrSize ≤ initialCursor := Nat.le_max_left _ _
  have hPhEndLeInit : phEnd ≤ initialCursor := Nat.le_max_right _ _
  have hInitLeShoff : initialCursor ≤ shoff :=
    Nat.le_trans hCursorFloor (le_roundUp _ _)
  have hEhdrLeShoff : Layout.ehdrSize ≤ shoff :=
    Nat.le_trans hEhdrLeInit hInitLeShoff
  have hPhEndLeShoff : phEnd ≤ shoff :=
    Nat.le_trans hPhEndLeInit hInitLeShoff
  -- Per-entry placement.
  have hPlacement : ∀ (j : Nat) (hj : j < newSections.size),
      PlaceFold.Placement layoutVerbatim 0 e.sections initialCursor foldRes j := by
    intros j hj
    have hjS : j < e.sections.size := hSizeEq ▸ hj
    exact PlaceFold.placeFold_placement hSpec e.sections initialCursor hVerb j hjS
  -- Pairwise non-overlap.
  have hPair : ∀ (j j' : Nat) (hj : j < newSections.size)
                 (hj' : j' < newSections.size),
      j ≠ j' → PlaceFold.PairDisjoint foldRes j j' := by
    intros j j' hj hj' hNe
    have hjS : j < e.sections.size := hSizeEq ▸ hj
    have hj'S : j' < e.sections.size := hSizeEq ▸ hj'
    exact PlaceFold.placeFold_pairDisjoint hSpec e.sections initialCursor hVerb
      j j' hjS hj'S hNe
  -- The transformed file's sections / shoff / phoff.
  have hLfeSections : (layoutForEncoding e).sections = newSections := rfl
  have hLfeShoff : (layoutForEncoding e).header.shoff = ⟨shoff⟩ := rfl
  have hLfePhoff : (layoutForEncoding e).header.phoff = e.header.phoff := rfl
  have hLfePhdrsSize : (layoutForEncoding e).phdrs.size = e.phdrs.size := by
    show (e.phdrs.map _).size = _
    exact Array.size_map
  -- A `Placement` placed-branch entry has offset ≥ initialCursor (since
  -- baseOffset = 0 and cursor0 = initialCursor); its end ≤ finalCursor ≤ shoff.
  -- A verbatim entry is NULL or NOBITS via hVerb.bound (the file-range bound
  -- disjunct collapses since baseOffset = 0; for non-zero-size sections, the
  -- verbatim predicate itself implies NULL/NOBITS via hSection0Null).
  -- Helper: from a Placement whose offset_or branched verbatim, derive
  -- NOBITS/NULL on the output entry.
  have place_verb_to_null_nobits :
      ∀ (j : Nat) (hjN : j < newSections.size)
        (hPl : PlaceFold.Placement layoutVerbatim 0 e.sections initialCursor foldRes j)
        (hVerbAt : layoutVerbatim j (e.sections[j]'hPl.hjS) = true),
        (newSections[j]'hjN).type = ShType.SHT_NOBITS ∨
        (newSections[j]'hjN).type = ShType.SHT_NULL := by
    intros j hjN hPl hVerbAt
    have hVerbAlt : j = 0 ∨ (e.sections[j]'hPl.hjS).type = ShType.SHT_NULL ∨
                    (e.sections[j]'hPl.hjS).type = ShType.SHT_NOBITS :=
      decide_eq_true_iff.mp hVerbAt
    rcases hVerbAlt with h0 | hN | hNB
    · subst h0
      exact Or.inr (hPl.type_eq.trans (hSection0Null hPl.hjS))
    · exact Or.inr (hPl.type_eq.trans hN)
    · exact Or.inl (hPl.type_eq.trans hNB)
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
    have hjN : j < newSections.size := hj
    have hj'N : j' < newSections.size := hj'
    exact hPair j j' hjN hj'N hNe hjN hj'N
  · -- hdr_phdr_disjoint
    show IntervalDisjoint 0 Layout.ehdrSize
      (layoutForEncoding e).header.phoff.val
      ((layoutForEncoding e).header.phoff.val
        + (layoutForEncoding e).phdrs.size * Layout.phdrSize)
    rw [hLfePhoff, hLfePhdrsSize]
    exact hHeaderPhdr
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
    rcases hPl.offset_or with hVerbJ | hPlace
    · rcases place_verb_to_null_nobits j hjN hPl hVerbJ.1 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · refine Or.inr (Or.inr (Or.inl ?_))
      show Layout.ehdrSize ≤ (newSections[j]'hjN).offset.val
      have : 0 + initialCursor ≤ (newSections[j]'hjN).offset.val := hPlace.2.1
      omega
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
    rcases hPl.offset_or with hVerbJ | hPlace
    · rcases place_verb_to_null_nobits j hjN hPl hVerbJ.1 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · refine Or.inr (Or.inr (Or.inl ?_))
      show phEnd ≤ (newSections[j]'hjN).offset.val
      have : 0 + initialCursor ≤ (newSections[j]'hjN).offset.val := hPlace.2.1
      omega
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
    rcases hPl.offset_or with hVerbJ | hPlace
    · rcases place_verb_to_null_nobits j hjN hPl hVerbJ.1 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · refine Or.inr (Or.inr (Or.inr ?_))
      show (newSections[j]'hjN).offset.val + (newSections[j]'hjN).encodedSize ≤ shoff
      have hFinLeShoff : finalCursor ≤ shoff := le_roundUp _ _
      have hFinAdd : (newSections[j]'hjN).offset.val + (newSections[j]'hjN).encodedSize
                    ≤ 0 + finalCursor := hPlace.2.2
      omega

end Patchelf.Elf
