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

@[simp] theorem withOffset_name (s : Section) (n : Nat) :
    (Section.withOffset s n).name = s.name := rfl

@[simp] theorem withOffset_flags (s : Section) (n : Nat) :
    (Section.withOffset s n).flags = s.flags := rfl

@[simp] theorem withOffset_link (s : Section) (n : Nat) :
    (Section.withOffset s n).link = s.link := rfl

@[simp] theorem withOffset_info (s : Section) (n : Nat) :
    (Section.withOffset s n).info = s.info := rfl

@[simp] theorem withOffset_entsize (s : Section) (n : Nat) :
    (Section.withOffset s n).entsize = s.entsize := rfl

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

/-! ## `relocatePhdr` field facts

    Identity on non-PT_INTERP/PT_DYNAMIC phdrs.  Sets `offset` and
    `filesz`/`memsz` for the two retargeted types.  Preserves `type`,
    `vaddr`, `align`, `flags`, `paddr` always. -/

@[simp] theorem relocatePhdr_type (interpIdx dynamicIdx : Option Nat)
    (newSections : Array Section) (ph : Patchelf.Elf.ProgramHeader) :
    (relocatePhdr interpIdx dynamicIdx newSections ph).type = ph.type := by
  unfold relocatePhdr phdrWithOffsetSize
  by_cases h1 : ph.type = PhType.PT_INTERP
  · rw [if_pos h1]
    cases interpIdx with
    | none => rfl
    | some i =>
      by_cases hLt : i < newSections.size
      · simp only [hLt, ↓reduceDIte]
      · simp only [hLt, ↓reduceDIte]
  · rw [if_neg h1]
    by_cases h2 : ph.type = PhType.PT_DYNAMIC
    · rw [if_pos h2]
      cases dynamicIdx with
      | none => rfl
      | some i =>
        by_cases hLt : i < newSections.size
        · simp only [hLt, ↓reduceDIte]
        · simp only [hLt, ↓reduceDIte]
    · rw [if_neg h2]

@[simp] theorem relocatePhdr_align (interpIdx dynamicIdx : Option Nat)
    (newSections : Array Section) (ph : Patchelf.Elf.ProgramHeader) :
    (relocatePhdr interpIdx dynamicIdx newSections ph).align = ph.align := by
  unfold relocatePhdr phdrWithOffsetSize
  by_cases h1 : ph.type = PhType.PT_INTERP
  · rw [if_pos h1]
    cases interpIdx with
    | none => rfl
    | some i =>
      by_cases hLt : i < newSections.size
      · simp only [hLt, ↓reduceDIte]
      · simp only [hLt, ↓reduceDIte]
  · rw [if_neg h1]
    by_cases h2 : ph.type = PhType.PT_DYNAMIC
    · rw [if_pos h2]
      cases dynamicIdx with
      | none => rfl
      | some i =>
        by_cases hLt : i < newSections.size
        · simp only [hLt, ↓reduceDIte]
        · simp only [hLt, ↓reduceDIte]
    · rw [if_neg h2]

@[simp] theorem relocatePhdr_vaddr (interpIdx dynamicIdx : Option Nat)
    (newSections : Array Section) (ph : Patchelf.Elf.ProgramHeader) :
    (relocatePhdr interpIdx dynamicIdx newSections ph).vaddr = ph.vaddr := by
  unfold relocatePhdr phdrWithOffsetSize
  by_cases h1 : ph.type = PhType.PT_INTERP
  · rw [if_pos h1]
    cases interpIdx with
    | none => rfl
    | some i =>
      by_cases hLt : i < newSections.size
      · simp only [hLt, ↓reduceDIte]
      · simp only [hLt, ↓reduceDIte]
  · rw [if_neg h1]
    by_cases h2 : ph.type = PhType.PT_DYNAMIC
    · rw [if_pos h2]
      cases dynamicIdx with
      | none => rfl
      | some i =>
        by_cases hLt : i < newSections.size
        · simp only [hLt, ↓reduceDIte]
        · simp only [hLt, ↓reduceDIte]
    · rw [if_neg h2]

/-- For non-PT_INTERP, non-PT_DYNAMIC phdrs, `relocatePhdr` is identity. -/
theorem relocatePhdr_of_not_interp_dynamic
    (interpIdx dynamicIdx : Option Nat)
    (newSections : Array Section) (ph : Patchelf.Elf.ProgramHeader)
    (hNotInterp : ph.type ≠ PhType.PT_INTERP)
    (hNotDynamic : ph.type ≠ PhType.PT_DYNAMIC) :
    relocatePhdr interpIdx dynamicIdx newSections ph = ph := by
  unfold relocatePhdr
  rw [if_neg hNotInterp, if_neg hNotDynamic]

/-- For PT_INTERP phdrs with a valid interpIdx, `relocatePhdr`'s
    output `offset` is the section's offset. -/
theorem relocatePhdr_pt_interp
    {interpIdx : Option Nat} (dynamicIdx : Option Nat)
    {newSections : Array Section} {ph : Patchelf.Elf.ProgramHeader}
    (hPh : ph.type = PhType.PT_INTERP)
    {iS : Nat} (hIdx : interpIdx = some iS) (h : iS < newSections.size) :
    (relocatePhdr interpIdx dynamicIdx newSections ph).offset
      = (newSections[iS]'h).offset := by
  unfold relocatePhdr
  rw [if_pos hPh, hIdx]
  simp only [h, ↓reduceDIte]
  rfl

/-- For PT_DYNAMIC phdrs with a valid dynamicIdx, `relocatePhdr`'s
    output `offset` is the section's offset. -/
theorem relocatePhdr_pt_dynamic
    (interpIdx : Option Nat) {dynamicIdx : Option Nat}
    {newSections : Array Section} {ph : Patchelf.Elf.ProgramHeader}
    (hPhNotInterp : ph.type ≠ PhType.PT_INTERP)
    (hPh : ph.type = PhType.PT_DYNAMIC)
    {iS : Nat} (hIdx : dynamicIdx = some iS) (h : iS < newSections.size) :
    (relocatePhdr interpIdx dynamicIdx newSections ph).offset
      = (newSections[iS]'h).offset := by
  unfold relocatePhdr
  rw [if_neg hPhNotInterp, if_pos hPh, hIdx]
  simp only [h, ↓reduceDIte]
  rfl

/-! ## `layoutForEncoding` preserves byte-layer `IsValid`

    Mirrors the `growEOFWithMainBody_preserves_valid` template.
    Output's `sections` come from `layoutSectionsFold` (= `placeFold
    layoutVerbatim Section.withOffset`); `Section.withOffset`
    preserves all non-`offset` fields.  The `_preserves_valid`
    proof dispatches each IsValid clause via per-field preservation
    derived from `placeFold_value_witness`. -/

/-- Per-section field preservation under `layoutSectionsFold`. -/
private theorem layoutSectionsFold_field_eq.{u}
    {α : Type u} (sections : Array Section) (cursor0 : Nat)
    (proj : Section → α)
    (hTransform : ∀ s o, proj (Section.withOffset s o) = proj s)
    (j : Nat)
    (hj : j < (layoutSectionsFold sections cursor0).1.size)
    (hjS : j < sections.size) :
    proj ((layoutSectionsFold sections cursor0).1[j]'hj)
      = proj (sections[j]'hjS) := by
  unfold layoutSectionsFold
  rcases PlaceFold.placeFold_value_witness sections cursor0 j hjS hj with
    ⟨_, hVerb⟩ | ⟨_, off, hPlaced⟩
  · rw [hVerb]
  · rw [hPlaced]; exact hTransform _ _

@[simp] theorem layoutForEncoding_sections_size (e : ElfFile) :
    (layoutForEncoding e).sections.size = e.sections.size := by
  unfold layoutForEncoding
  exact PlaceFold.size_eq _ _

@[simp] theorem layoutForEncoding_header_phnum (e : ElfFile) :
    (layoutForEncoding e).header.phnum = e.header.phnum := by
  unfold layoutForEncoding; rfl

@[simp] theorem layoutForEncoding_header_shnum (e : ElfFile) :
    (layoutForEncoding e).header.shnum = e.header.shnum := by
  unfold layoutForEncoding; rfl

@[simp] theorem layoutForEncoding_header_shstrndx (e : ElfFile) :
    (layoutForEncoding e).header.shstrndx = e.header.shstrndx := by
  unfold layoutForEncoding; rfl

@[simp] theorem layoutForEncoding_header_phentsize (e : ElfFile) :
    (layoutForEncoding e).header.phentsize = e.header.phentsize := by
  unfold layoutForEncoding; rfl

@[simp] theorem layoutForEncoding_header_shentsize (e : ElfFile) :
    (layoutForEncoding e).header.shentsize = e.header.shentsize := by
  unfold layoutForEncoding; rfl

@[simp] theorem layoutForEncoding_phdrs_size (e : ElfFile) :
    (layoutForEncoding e).phdrs.size = e.phdrs.size := by
  unfold layoutForEncoding
  exact Array.size_map ..

theorem layoutForEncoding_sections_name (e : ElfFile) (j : Nat)
    (hj : j < (layoutForEncoding e).sections.size)
    (hjE : j < e.sections.size) :
    ((layoutForEncoding e).sections[j]'hj).name = (e.sections[j]'hjE).name := by
  unfold layoutForEncoding at hj ⊢
  exact layoutSectionsFold_field_eq _ _ (·.name) (fun _ _ => rfl) j hj hjE

theorem layoutForEncoding_sections_type (e : ElfFile) (j : Nat)
    (hj : j < (layoutForEncoding e).sections.size)
    (hjE : j < e.sections.size) :
    ((layoutForEncoding e).sections[j]'hj).type = (e.sections[j]'hjE).type := by
  unfold layoutForEncoding at hj ⊢
  exact layoutSectionsFold_field_eq _ _ (·.type) (fun _ _ => rfl) j hj hjE

theorem layoutForEncoding_sections_content (e : ElfFile) (j : Nat)
    (hj : j < (layoutForEncoding e).sections.size)
    (hjE : j < e.sections.size) :
    ((layoutForEncoding e).sections[j]'hj).content = (e.sections[j]'hjE).content := by
  unfold layoutForEncoding at hj ⊢
  exact layoutSectionsFold_field_eq _ _ (·.content) (fun _ _ => rfl) j hj hjE

theorem layoutForEncoding_sections_addralign (e : ElfFile) (j : Nat)
    (hj : j < (layoutForEncoding e).sections.size)
    (hjE : j < e.sections.size) :
    ((layoutForEncoding e).sections[j]'hj).addralign = (e.sections[j]'hjE).addralign := by
  unfold layoutForEncoding at hj ⊢
  exact layoutSectionsFold_field_eq _ _ (·.addralign) (fun _ _ => rfl) j hj hjE

theorem layoutForEncoding_sections_entsize (e : ElfFile) (j : Nat)
    (hj : j < (layoutForEncoding e).sections.size)
    (hjE : j < e.sections.size) :
    ((layoutForEncoding e).sections[j]'hj).entsize = (e.sections[j]'hjE).entsize := by
  unfold layoutForEncoding at hj ⊢
  exact layoutSectionsFold_field_eq _ _ (·.entsize) (fun _ _ => rfl) j hj hjE

theorem layoutForEncoding_header_ident (e : ElfFile) :
    (layoutForEncoding e).header.ident = e.header.ident := by
  unfold layoutForEncoding; rfl

theorem layoutForEncoding_header_entry (e : ElfFile) :
    (layoutForEncoding e).header.entry = e.header.entry := by
  unfold layoutForEncoding; rfl

theorem layoutForEncoding_findUniqueTypeIdx (e : ElfFile) (ty : ShType) :
    (layoutForEncoding e).findUniqueTypeIdx ty = e.findUniqueTypeIdx ty := by
  apply ElfFile.firstIdxWhereIn_congr
  · exact layoutForEncoding_sections_size _
  · intros k hk hk'
    have := layoutForEncoding_sections_type e k hk hk'
    simp [this]

@[simp] theorem layoutForEncoding_dynamicIdx (e : ElfFile) :
    (layoutForEncoding e).dynamicIdx = e.dynamicIdx :=
  layoutForEncoding_findUniqueTypeIdx e ShType.SHT_DYNAMIC

@[simp] theorem layoutForEncoding_dynsymIdx (e : ElfFile) :
    (layoutForEncoding e).dynsymIdx = e.dynsymIdx :=
  layoutForEncoding_findUniqueTypeIdx e ShType.SHT_DYNSYM

theorem layoutForEncoding_contentAt (e : ElfFile) (i? : Option Nat) :
    (layoutForEncoding e).contentAt i? = e.contentAt i? := by
  unfold ElfFile.contentAt
  cases i? with
  | none => rfl
  | some i =>
    simp only [Option.bind_some]
    by_cases hi : i < e.sections.size
    · have hi' : i < (layoutForEncoding e).sections.size :=
        (layoutForEncoding_sections_size e).symm ▸ hi
      rw [dif_pos hi', dif_pos hi]
      rw [layoutForEncoding_sections_content e i hi' hi]
    · have hi' : ¬ i < (layoutForEncoding e).sections.size := by
        intro h; exact hi ((layoutForEncoding_sections_size e).symm ▸ h)
      rw [dif_neg hi', dif_neg hi]

@[simp] theorem layoutForEncoding_dynamic (e : ElfFile) :
    (layoutForEncoding e).dynamic = e.dynamic := by
  unfold ElfFile.dynamic
  rw [layoutForEncoding_dynamicIdx, layoutForEncoding_contentAt]

@[simp] theorem layoutForEncoding_dynsym (e : ElfFile) :
    (layoutForEncoding e).dynsym = e.dynsym := by
  unfold ElfFile.dynsym
  rw [layoutForEncoding_dynsymIdx, layoutForEncoding_contentAt]

@[simp] theorem layoutForEncoding_shstrtab (e : ElfFile) :
    (layoutForEncoding e).shstrtab = e.shstrtab := by
  unfold ElfFile.shstrtab
  rw [layoutForEncoding_header_shstrndx]
  by_cases hSh : e.header.shstrndx.toNat < e.sections.size
  · have hSh' : e.header.shstrndx.toNat < (layoutForEncoding e).sections.size :=
      (layoutForEncoding_sections_size e).symm ▸ hSh
    rw [dif_pos hSh', dif_pos hSh]
    rw [layoutForEncoding_sections_content e _ hSh' hSh]
  · have hSh' : ¬ e.header.shstrndx.toNat < (layoutForEncoding e).sections.size := by
      intro h; exact hSh ((layoutForEncoding_sections_size e).symm ▸ h)
    rw [dif_neg hSh', dif_neg hSh]

theorem layoutForEncoding_findIdxByName (e : ElfFile) (name : ByteArray) :
    (layoutForEncoding e).findIdxByName name = e.findIdxByName name := by
  unfold ElfFile.findIdxByName
  rw [layoutForEncoding_shstrtab]
  cases e.shstrtab with
  | none => rfl
  | some st =>
    apply ElfFile.firstIdxWhereIn_congr
    · exact layoutForEncoding_sections_size _
    · intros k hk hk'
      have := layoutForEncoding_sections_name e k hk hk'
      simp [this]

@[simp] theorem layoutForEncoding_dynstrIdx (e : ElfFile) :
    (layoutForEncoding e).dynstrIdx = e.dynstrIdx :=
  layoutForEncoding_findIdxByName e _

@[simp] theorem layoutForEncoding_dynstr (e : ElfFile) :
    (layoutForEncoding e).dynstr = e.dynstr := by
  unfold ElfFile.dynstr
  rw [layoutForEncoding_dynstrIdx, layoutForEncoding_contentAt]

@[simp] theorem layoutForEncoding_interpIdx (e : ElfFile) :
    (layoutForEncoding e).interpIdx = e.interpIdx :=
  layoutForEncoding_findIdxByName e _

/-- `layoutForEncoding`'s output's i-th phdr is `relocatePhdr` applied
    to the input's i-th phdr.  Used to reason about per-phdr properties
    in `_preserves_loadable`. -/
theorem layoutForEncoding_phdrs_getElem (e : ElfFile) (i : Nat)
    (hi : i < (layoutForEncoding e).phdrs.size)
    (hiE : i < e.phdrs.size) :
    (layoutForEncoding e).phdrs[i]'hi
      = relocatePhdr e.interpIdx e.dynamicIdx
          (layoutSectionsFold e.sections
            (max Layout.ehdrSize (e.header.phoff.val + e.phdrs.size * Layout.phdrSize))).1
          (e.phdrs[i]'hiE) := by
  unfold layoutForEncoding at hi ⊢
  rw [Array.getElem_map]

/-- `layoutForEncoding` preserves byte-layer `IsValid`.

    Same shape as `growEOFWithMainBody_preserves_valid`: per-section
    `(name, type, content)` and header counts are all preserved;
    only `(offset, addr)` and `header.shoff` change.  Phdrs go
    through `relocatePhdr` (which only mutates PT_INTERP /
    PT_DYNAMIC entries' offsets/sizes — does not change the array
    size). -/
theorem layoutForEncoding_preserves_valid (e : ElfFile) (hVal : e.IsValid) :
    (layoutForEncoding e).IsValid := by
  refine
    { header_counts := ?_, sections_wf := ?_, strtabs_wf := ?_,
      dynamic_wf := ?_, dynsym_wf := ?_, content_wf := ?_,
      types_distinct := ?_, names_unique := ?_ }
  ----------------------------------------
  -- header_counts: phnum/shnum/etc. unchanged.
  ----------------------------------------
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hVal.header_counts
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [layoutForEncoding_header_phnum, layoutForEncoding_phdrs_size]; exact h1
    · rw [layoutForEncoding_header_shnum, layoutForEncoding_sections_size]; exact h2
    · rw [layoutForEncoding_header_phentsize]; exact h3
    · rw [layoutForEncoding_header_shentsize]; exact h4
    · rw [layoutForEncoding_header_shstrndx, layoutForEncoding_sections_size]; exact h5
  · intro h0
    have h0' : 0 < e.sections.size := (layoutForEncoding_sections_size e) ▸ h0
    rw [layoutForEncoding_sections_type e 0 h0 h0']
    exact hVal.sections_wf h0'
  · have hAll := hVal.strtabs_wf
    show (layoutForEncoding e).sections.all _ = true
    unfold ElfFile.strtabsWellFormed at hAll
    rw [Array.all_eq_true] at hAll ⊢
    intro j hj
    have hjE : j < e.sections.size := (layoutForEncoding_sections_size e) ▸ hj
    show ElfFile.Section.strtabWellFormedB ((layoutForEncoding e).sections[j]'hj) = true
    have : ElfFile.Section.strtabWellFormedB ((layoutForEncoding e).sections[j]'hj)
         = ElfFile.Section.strtabWellFormedB (e.sections[j]'hjE) := by
      unfold ElfFile.Section.strtabWellFormedB
      rw [layoutForEncoding_sections_content e j hj hjE]
    rw [this]; exact hAll j hjE
  · refine ⟨?_, ?_⟩
    · intro dyn hd
      rw [layoutForEncoding_dynamic] at hd
      exact hVal.dynamic_wf.1 dyn hd
    · intros dyn ds hd hds
      rw [layoutForEncoding_dynamic] at hd
      rw [layoutForEncoding_dynstr] at hds
      exact hVal.dynamic_wf.2 dyn ds hd hds
  · intros syms ds hSyms hDs
    rw [layoutForEncoding_dynsym] at hSyms
    rw [layoutForEncoding_dynstr] at hDs
    exact hVal.dynsym_wf syms ds hSyms hDs
  · have hAll := hVal.content_wf
    show (layoutForEncoding e).sections.all _ = true
    unfold ElfFile.sectionsContentWellFormed at hAll
    rw [Array.all_eq_true] at hAll ⊢
    intro j hj
    have hjE : j < e.sections.size := (layoutForEncoding_sections_size e) ▸ hj
    show ElfFile.Section.contentWellFormedB ((layoutForEncoding e).sections[j]'hj) = true
    have : ElfFile.Section.contentWellFormedB ((layoutForEncoding e).sections[j]'hj)
         = ElfFile.Section.contentWellFormedB (e.sections[j]'hjE) := by
      unfold ElfFile.Section.contentWellFormedB
      rw [layoutForEncoding_sections_content e j hj hjE]
    rw [this]; exact hAll j hjE
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hVal.types_distinct
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> {
      intros i hi j hj hi_t hj_t
      have hiE : i < e.sections.size := (layoutForEncoding_sections_size e) ▸ hi
      have hjE : j < e.sections.size := (layoutForEncoding_sections_size e) ▸ hj
      rw [layoutForEncoding_sections_type e i hi hiE] at hi_t
      rw [layoutForEncoding_sections_type e j hj hjE] at hj_t
      first
      | exact h1 i hiE j hjE hi_t hj_t
      | exact h2 i hiE j hjE hi_t hj_t
      | exact h3 i hiE j hjE hi_t hj_t
      | exact h4 i hiE j hjE hi_t hj_t
      | exact h5 i hiE j hjE hi_t hj_t
      | exact h6 i hiE j hjE hi_t hj_t
    }
  · unfold ElfFile.namedSectionsUnique
    rw [layoutForEncoding_shstrtab]
    cases hSt : e.shstrtab with
    | none => trivial
    | some st =>
        obtain ⟨h1, h2⟩ := by
          have := hVal.names_unique
          unfold ElfFile.namedSectionsUnique at this
          rw [hSt] at this; exact this
        constructor <;> {
          intros i hi j hj hi_n hj_n
          have hiE : i < e.sections.size := (layoutForEncoding_sections_size e) ▸ hi
          have hjE : j < e.sections.size := (layoutForEncoding_sections_size e) ▸ hj
          rw [layoutForEncoding_sections_name e i hi hiE] at hi_n
          rw [layoutForEncoding_sections_name e j hj hjE] at hj_n
          first
          | exact h1 i hiE j hjE hi_n hj_n
          | exact h2 i hiE j hjE hi_n hj_n
        }

/-! ## `layoutForEncoding` preserves `IsLoadable`

    `IsLoadable` adds 4 clauses to `IsValid`: `sectionsNonOverlapping`,
    `ptInterpAgreement`, `ptDynamicAgreement`, `segmentCongruence`.

    * sections-nonoverlap: from `_produces_spliceRegionsDisjoint`'s
      `sections_disjoint` clause.
    * PT_INTERP / PT_DYNAMIC agreement: `relocatePhdr` retargets each
      such phdr to its section's new offset; `interpIdx` / `dynamicIdx`
      are preserved → the output's matched section IS the retargeted
      phdr's target.
    * segmentCongruence: `relocatePhdr` is identity on PT_LOADs (only
      touches PT_INTERP and PT_DYNAMIC).  PT_LOAD offsets / vaddrs /
      aligns are unchanged → congruence preserved if input had it.

    Requires `hSection0Null` + the structural input invariants because
    `layoutForEncoding_preserves_valid` covers the `IsValid` base, and
    the existing `_produces_spliceRegionsDisjoint` provides the
    `sections_disjoint` clause via the `IsLoadable` chain. -/
theorem layoutForEncoding_preserves_loadable (e : ElfFile)
    (hLoad : e.IsLoadable)
    (hSection0Null : ∀ (h : 0 < e.sections.size),
      (e.sections[0]'h).type = ShType.SHT_NULL)
    (hHeaderPhdr : e.headerPhdrDisjoint) :
    (layoutForEncoding e).IsLoadable := by
  refine
    { toIsValid := layoutForEncoding_preserves_valid e hLoad.toIsValid
      sections_nonoverlapping := ?_
      pt_interp_agrees := ?_
      pt_dynamic_agrees := ?_
      segment_congruent := ?_ }
  ----------------------------------------
  -- sections_nonoverlapping: from spliceRegionsDisjoint.
  ----------------------------------------
  · exact (layoutForEncoding_produces_spliceRegionsDisjoint e
            hSection0Null hHeaderPhdr).sections_disjoint
  ----------------------------------------
  -- ptInterpAgreement
  ----------------------------------------
  · unfold ElfFile.ptInterpAgreement
    rw [layoutForEncoding_interpIdx]
    cases hI : e.interpIdx with
    | none => trivial
    | some iS =>
      intro hLt iPh hPh hPhT
      -- Output phdr is relocatePhdr ... (e.phdrs[iPh]).
      have hPhE : iPh < e.phdrs.size := layoutForEncoding_phdrs_size e ▸ hPh
      rw [layoutForEncoding_phdrs_getElem e iPh hPh hPhE]
      -- The PT_INTERP type is preserved by relocatePhdr_type.
      have hPhTE : (e.phdrs[iPh]'hPhE).type = PhType.PT_INTERP := by
        rw [layoutForEncoding_phdrs_getElem e iPh hPh hPhE,
            relocatePhdr_type] at hPhT
        exact hPhT
      -- `iS` came from `(layoutForEncoding e).interpIdx`; after the rw
      -- above, the LHS-side `iS` is the same one and the bound `hLt`
      -- refers to the OUTPUT's sections.
      have hLtE : iS < e.sections.size := layoutForEncoding_sections_size e ▸ hLt
      have hSecE : iS < (layoutSectionsFold e.sections
                          (max Layout.ehdrSize (e.header.phoff.val
                            + e.phdrs.size * Layout.phdrSize))).1.size := by
        unfold layoutSectionsFold
        rw [PlaceFold.size_eq]; exact hLtE
      rw [relocatePhdr_pt_interp e.dynamicIdx hPhTE hI hSecE]
      -- Goal: newSections[iS].offset = (layoutForEncoding e).sections[iS].offset.
      -- These are the same array.
      rfl
  ----------------------------------------
  -- ptDynamicAgreement
  ----------------------------------------
  · unfold ElfFile.ptDynamicAgreement
    rw [layoutForEncoding_dynamicIdx]
    cases hD : e.dynamicIdx with
    | none => trivial
    | some iS =>
      intro hLt iPh hPh hPhT
      have hPhE : iPh < e.phdrs.size := layoutForEncoding_phdrs_size e ▸ hPh
      rw [layoutForEncoding_phdrs_getElem e iPh hPh hPhE]
      have hPhTE : (e.phdrs[iPh]'hPhE).type = PhType.PT_DYNAMIC := by
        rw [layoutForEncoding_phdrs_getElem e iPh hPh hPhE,
            relocatePhdr_type] at hPhT
        exact hPhT
      -- PT_DYNAMIC and PT_INTERP are different — derive `≠`.
      have hPhNotInterp : (e.phdrs[iPh]'hPhE).type ≠ PhType.PT_INTERP := by
        rw [hPhTE]; decide
      have hLtE : iS < e.sections.size := layoutForEncoding_sections_size e ▸ hLt
      have hSecE : iS < (layoutSectionsFold e.sections
                          (max Layout.ehdrSize (e.header.phoff.val
                            + e.phdrs.size * Layout.phdrSize))).1.size := by
        unfold layoutSectionsFold
        rw [PlaceFold.size_eq]; exact hLtE
      rw [relocatePhdr_pt_dynamic e.interpIdx hPhNotInterp hPhTE hD hSecE]
      rfl
  ----------------------------------------
  -- segmentCongruence
  ----------------------------------------
  · unfold ElfFile.segmentCongruence
    intros iPh hPh hPhT
    have hPhE : iPh < e.phdrs.size := layoutForEncoding_phdrs_size e ▸ hPh
    rw [layoutForEncoding_phdrs_getElem e iPh hPh hPhE]
    -- PT_LOAD: relocatePhdr is identity (PT_LOAD ≠ PT_INTERP, PT_LOAD ≠ PT_DYNAMIC).
    have hPhTE : (e.phdrs[iPh]'hPhE).type = PhType.PT_LOAD := by
      rw [layoutForEncoding_phdrs_getElem e iPh hPh hPhE,
          relocatePhdr_type] at hPhT
      exact hPhT
    have hPhNotInterp : (e.phdrs[iPh]'hPhE).type ≠ PhType.PT_INTERP := by
      rw [hPhTE]; decide
    have hPhNotDynamic : (e.phdrs[iPh]'hPhE).type ≠ PhType.PT_DYNAMIC := by
      rw [hPhTE]; decide
    rw [relocatePhdr_of_not_interp_dynamic _ _ _ _ hPhNotInterp hPhNotDynamic]
    exact hLoad.segment_congruent iPh hPhE hPhTE

end Patchelf.Elf
