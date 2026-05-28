/-
  Section content update on the byte-layer `ElfFile`.

  Used by `Adapter.toElfFile` (to splice typed-side mutations back
  into the byte-layer file) and by `Encoder.syncDtStrszInFile` (to
  rewrite `.dynamic`'s DT_STRSZ entry before encode).

  This file is intentionally small.  An earlier design carried
  `IsValid`-preservation infrastructure (per-clause lemmas +
  bundling theorems) for byte-layer section-content updates, but
  ops live on `ValidElfFile` and don't traverse byte-layer
  `IsValid` clauses; the preservation block had zero callers and
  was removed.  Today this file is `updateSectionContent` plus
  three `@[simp]` projection lemmas.
-/
module

public import Patchelf.Elf.ElfFile

@[expose] public section

namespace Patchelf.Elf

/-- Update the content of the section at index `i`. Metadata (name,
    type, flags, addr, offset, link, info, addralign, entsize) is
    preserved. Out-of-bounds indices are no-ops. -/
def ElfFile.updateSectionContent (e : ElfFile) (i : Nat)
    (newContent : SectionContent) : ElfFile :=
  if h : i < e.sections.size then
    let updated := { (e.sections[i]'h) with content := newContent }
    { e with sections := e.sections.set i updated h }
  else e

@[simp] theorem ElfFile.updateSectionContent_header (e : ElfFile)
    (i : Nat) (c : SectionContent) :
    (e.updateSectionContent i c).header = e.header := by
  unfold updateSectionContent
  split <;> rfl

@[simp] theorem ElfFile.updateSectionContent_phdrs (e : ElfFile)
    (i : Nat) (c : SectionContent) :
    (e.updateSectionContent i c).phdrs = e.phdrs := by
  unfold updateSectionContent
  split <;> rfl

@[simp] theorem ElfFile.updateSectionContent_sections_size (e : ElfFile)
    (i : Nat) (c : SectionContent) :
    (e.updateSectionContent i c).sections.size = e.sections.size := by
  unfold updateSectionContent
  split <;> simp

/-! ## `firstIdxWhereIn`'s positive result satisfies the predicate

    If `firstIdxWhereIn a p = some i`, then `i < a.size` and `p (a[i])`.
    This is the structural converse to `findUniqueTypeIdx_eq_some`. -/

theorem ElfFile.firstIdxWhereIn_some_implies
    (a : Array Section) (p : Section → Bool) (i : Nat)
    (h : firstIdxWhereIn a p = some i) :
    ∃ hi : i < a.size, p (a[i]'hi) = true := by
  unfold firstIdxWhereIn at h
  -- Walk the recursion: at each k, if go k = some i, either p (a[k])
  -- and i = k, or recurse to k+1.
  suffices hh : ∀ (n k : Nat) (_ : k + n ≥ a.size),
      firstIdxWhereIn.go a p k = some i →
      ∃ hi : i < a.size, p (a[i]'hi) = true by
    exact hh a.size 0 (by omega) h
  intro n
  induction n with
  | zero =>
    intros k hge hgo
    unfold firstIdxWhereIn.go at hgo
    have hk : ¬ k < a.size := by omega
    rw [dif_neg hk] at hgo
    cases hgo
  | succ m ih =>
    intros k _hge hgo
    unfold firstIdxWhereIn.go at hgo
    by_cases hk : k < a.size
    · rw [dif_pos hk] at hgo
      by_cases hP : p (a[k]'hk) = true
      · rw [if_pos hP] at hgo
        cases hgo
        exact ⟨hk, hP⟩
      · rw [if_neg hP] at hgo
        exact ih (k + 1) (by omega) hgo
    · rw [dif_neg hk] at hgo
      cases hgo

/-- A section returned by `findUniqueTypeIdx ty` has type `ty`. -/
theorem ElfFile.findUniqueTypeIdx_section_type (e : ElfFile) (ty : Layout.ShType)
    (i : Nat) (h : e.findUniqueTypeIdx ty = some i) :
    ∃ hi : i < e.sections.size, (e.sections[i]'hi).type = ty := by
  unfold findUniqueTypeIdx at h
  obtain ⟨hi, hP⟩ := firstIdxWhereIn_some_implies _ _ _ h
  exact ⟨hi, of_decide_eq_true hP⟩

/-! ## Generic congruence for `firstIdxWhereIn`

    `firstIdxWhereIn a p` only depends on the sequence of values
    `p (a[0]), p (a[1]), …`.  Two arrays whose predicate-evaluations
    agree pointwise produce the same result.  We use this to bridge
    `updateSectionContent`-derived arrays back to the original via
    type / name preservation. -/

theorem ElfFile.firstIdxWhereIn_congr
    (a b : Array Section) (p : Section → Bool)
    (hSize : a.size = b.size)
    (hPred : ∀ (k : Nat) (ha : k < a.size) (hb : k < b.size),
      p (a[k]'ha) = p (b[k]'hb)) :
    firstIdxWhereIn a p = firstIdxWhereIn b p := by
  unfold firstIdxWhereIn
  -- Walk by induction on `a.size - k`.  At each `k`:
  --   * out-of-bounds → both sides return `none`;
  --   * in-bounds → `p (a[k]) = p (b[k])`, so the if-branch picks the
  --     same disjunct, and recursive calls match by the IH.
  suffices h : ∀ (n k : Nat) (_ : k + n ≥ a.size),
      firstIdxWhereIn.go a p k = firstIdxWhereIn.go b p k by
    exact h a.size 0 (by omega)
  intro n
  induction n with
  | zero =>
    intros k hge
    unfold firstIdxWhereIn.go
    have hka : ¬ k < a.size := by omega
    have hkb : ¬ k < b.size := by rw [← hSize]; exact hka
    rw [dif_neg hka, dif_neg hkb]
  | succ m ih =>
    intros k _hge
    unfold firstIdxWhereIn.go
    by_cases hka : k < a.size
    · have hkb : k < b.size := by rw [← hSize]; exact hka
      rw [dif_pos hka, dif_pos hkb, hPred k hka hkb]
      by_cases hP : p (b[k]'hkb) = true
      · rw [if_pos hP, if_pos hP]
      · rw [if_neg hP, if_neg hP]
        exact ih (k + 1) (by omega)
    · have hkb : ¬ k < b.size := by rw [← hSize]; exact hka
      rw [dif_neg hka, dif_neg hkb]

/-- `firstIdxWhereIn` is preserved when updating array `a` at index `i`
    with `v`, given `p v = false` AND `p (a[i]) = false`.  The update at
    `i` doesn't affect the result since `i` is a non-matching position in
    both the original and updated arrays. -/
theorem ElfFile.firstIdxWhereIn_update_both_false
    (a : Array Section) (p : Section → Bool)
    (i : Nat) (hi : i < a.size) (v : Section)
    (hv : p v = false) (horig : p (a[i]'hi) = false) :
    firstIdxWhereIn (a.set i v hi) p = firstIdxWhereIn a p :=
  firstIdxWhereIn_congr _ _ _
    (by simp [Array.size_set])
    (fun k ha hb => by
      by_cases hki : k = i
      · subst hki
        simp [Array.getElem_set_self, horig, hv]
      · simp [Array.getElem_set, Ne.symm hki])

/-- Sections-array field after update. -/
theorem ElfFile.updateSectionContent_sections (e : ElfFile)
    (i : Nat) (c : SectionContent) (h : i < e.sections.size) :
    (e.updateSectionContent i c).sections =
      e.sections.set i { e.sections[i]'h with content := c } h := by
  unfold updateSectionContent
  rw [dif_pos h]

/-- Sections at indices ≠ `i` are unchanged. -/
theorem ElfFile.updateSectionContent_getElem_ne (e : ElfFile)
    (i : Nat) (c : SectionContent) (j : Nat) (hj : j < e.sections.size)
    (hne : j ≠ i)
    (hj' : j < (e.updateSectionContent i c).sections.size) :
    ((e.updateSectionContent i c).sections[j]'hj') = (e.sections[j]'hj) := by
  by_cases hi : i < e.sections.size
  · simp [updateSectionContent_sections _ _ _ hi, Array.getElem_set, Ne.symm hne]
  · simp [updateSectionContent, dif_neg hi]

/-- The section at index `i` after update has only its `content` field
    changed. -/
theorem ElfFile.updateSectionContent_getElem_self (e : ElfFile)
    (i : Nat) (c : SectionContent) (hi : i < e.sections.size)
    (hi' : i < (e.updateSectionContent i c).sections.size) :
    ((e.updateSectionContent i c).sections[i]'hi') =
      { e.sections[i]'hi with content := c } := by
  simp [updateSectionContent_sections _ _ _ hi, Array.getElem_set_self]

/-! ## Type / name preservation under updateSectionContent

    `updateSectionContent` changes `content` at index `i`.  Since
    `Section.type = content.type`, the type at `j ≠ i` is unchanged
    (same content → same type), and the type at `j = i` becomes `c.type`.

    For same-constructor updates (e.g. `.dynamic dyn → .dynamic dyn'`),
    `c.type = original.type` so type appears preserved even at `j = i`.
    Callers that need the `j = i` case separately use
    `updateSectionContent_type_self`. -/

/-- Type at `j ≠ i` is preserved: content at `j` is unchanged. -/
theorem ElfFile.updateSectionContent_type (e : ElfFile)
    (i : Nat) (c : SectionContent) (j : Nat) (hj : j < e.sections.size)
    (hne : j ≠ i)
    (hj' : j < (e.updateSectionContent i c).sections.size) :
    ((e.updateSectionContent i c).sections[j]'hj').type
      = (e.sections[j]'hj).type := by
  rw [show (e.updateSectionContent i c).sections[j]'hj'
        = e.sections[j]'hj from
    updateSectionContent_getElem_ne _ _ _ _ hj hne hj']

/-- Type at `j = i` becomes `c.type`. -/
theorem ElfFile.updateSectionContent_type_self (e : ElfFile)
    (i : Nat) (c : SectionContent) (hi : i < e.sections.size)
    (hi' : i < (e.updateSectionContent i c).sections.size) :
    ((e.updateSectionContent i c).sections[i]'hi').type = c.type := by
  rw [show (e.updateSectionContent i c).sections[i]'hi'
        = { e.sections[i]'hi with content := c } from
    updateSectionContent_getElem_self _ _ _ hi hi']
  rfl

/-- Name preservation at every index. -/
theorem ElfFile.updateSectionContent_name (e : ElfFile)
    (i : Nat) (c : SectionContent) (j : Nat) (hj : j < e.sections.size)
    (hj' : j < (e.updateSectionContent i c).sections.size) :
    ((e.updateSectionContent i c).sections[j]'hj').name
      = (e.sections[j]'hj).name := by
  by_cases hje : j = i
  · subst hje
    rw [updateSectionContent_getElem_self _ _ _ hj hj']
  · rw [updateSectionContent_getElem_ne _ _ _ _ hj hje hj']

/-- Offset preservation. -/
theorem ElfFile.updateSectionContent_offset (e : ElfFile)
    (i : Nat) (c : SectionContent) (j : Nat) (hj : j < e.sections.size)
    (hj' : j < (e.updateSectionContent i c).sections.size) :
    ((e.updateSectionContent i c).sections[j]'hj').offset
      = (e.sections[j]'hj).offset := by
  by_cases hje : j = i
  · subst hje
    rw [updateSectionContent_getElem_self _ _ _ hj hj']
  · rw [updateSectionContent_getElem_ne _ _ _ _ hj hje hj']

/-- `findUniqueTypeIdx` is preserved when the update at `i` has the
    same type as the original (same-constructor update). -/
theorem ElfFile.updateSectionContent_findUniqueTypeIdx (e : ElfFile)
    (i : Nat) (c : SectionContent) (ty : Layout.ShType)
    (hTypeEq : ∀ (hi : i < e.sections.size),
        c.type = (e.sections[i]'hi).type) :
    (e.updateSectionContent i c).findUniqueTypeIdx ty = e.findUniqueTypeIdx ty :=
  firstIdxWhereIn_congr _ _ _ (updateSectionContent_sections_size e i c)
    (fun k ha hb => by
      -- Goal: decide ((updated[k]).type = ty) = decide ((e[k]).type = ty)
      -- Show the types are equal, then the decides are equal.
      have hTy : ((e.updateSectionContent i c).sections[k]'ha).type
               = (e.sections[k]'hb).type := by
        by_cases hki : k = i
        · subst hki
          rw [updateSectionContent_type_self _ _ _ hb ha]
          exact hTypeEq hb
        · exact updateSectionContent_type _ _ _ _ hb hki ha
      simp [hTy])

/-- `dynamicIdx` is preserved when updating with same-type content.
    Callers providing `.dynamic newDyn` satisfy `c.type = SHT_DYNAMIC
    = original.type` (when the original section has `.dynamic` content). -/
theorem ElfFile.updateSectionContent_dynamicIdx (e : ElfFile)
    (i : Nat) (c : SectionContent)
    (hTypeEq : ∀ (hi : i < e.sections.size), c.type = (e.sections[i]'hi).type) :
    (e.updateSectionContent i c).dynamicIdx = e.dynamicIdx :=
  updateSectionContent_findUniqueTypeIdx e i c _ hTypeEq

/-- The shstrtab section is unchanged when we update a *different* index.
    `shstrtab` reads the content at `shstrndx`; if the update index is
    elsewhere, the content there is unaffected. -/
theorem ElfFile.updateSectionContent_shstrtab (e : ElfFile)
    (i : Nat) (c : SectionContent) (hNe : i ≠ e.header.shstrndx.toNat) :
    (e.updateSectionContent i c).shstrtab = e.shstrtab := by
  unfold shstrtab
  -- Header is preserved, so shstrndx and the comparison are unchanged.
  simp only [updateSectionContent_header, updateSectionContent_sections_size]
  by_cases h : e.header.shstrndx.toNat < e.sections.size
  · rw [dif_pos h, dif_pos h]
    have h' : e.header.shstrndx.toNat < (e.updateSectionContent i c).sections.size := by
      rw [updateSectionContent_sections_size]; exact h
    rw [updateSectionContent_getElem_ne e i c e.header.shstrndx.toNat h
          (Ne.symm hNe) h']
  · rw [dif_neg h, dif_neg h]

/-- `findIdxByName` (which uses `shstrtab` + name lookups) is preserved
    when the updated index is not the shstrndx index. -/
theorem ElfFile.updateSectionContent_findIdxByName (e : ElfFile)
    (i : Nat) (c : SectionContent) (name : ByteArray)
    (hNe : i ≠ e.header.shstrndx.toNat) :
    (e.updateSectionContent i c).findIdxByName name = e.findIdxByName name := by
  unfold findIdxByName
  rw [updateSectionContent_shstrtab _ _ _ hNe]
  split
  · rfl
  · -- The name lookup walks sections; names are preserved.  Reuse the
    -- generic congruence helper with the name-equality fact.
    exact firstIdxWhereIn_congr _ _ _ (updateSectionContent_sections_size e i c)
      (fun k ha hb => by rw [updateSectionContent_name e i c k hb ha])

/-- `dynstrIdx` is preserved when not updating shstrtab. -/
theorem ElfFile.updateSectionContent_dynstrIdx (e : ElfFile)
    (i : Nat) (c : SectionContent) (hNe : i ≠ e.header.shstrndx.toNat) :
    (e.updateSectionContent i c).dynstrIdx = e.dynstrIdx :=
  updateSectionContent_findIdxByName e i c _ hNe

/-! ## `contentAt` preservation under disjoint-index updates -/

/-- `contentAt` at index `j` is preserved when the update happens at a
    different index (`j ≠ i`).  This is the key building block for
    proving that `dynsym` / `dynstr` / `interp` / etc. accessors agree
    across an update at an unrelated index. -/
theorem ElfFile.updateSectionContent_contentAt_some_ne (e : ElfFile)
    (i : Nat) (c : SectionContent) (j : Nat) (hNe : j ≠ i) :
    (e.updateSectionContent i c).contentAt (some j) = e.contentAt (some j) := by
  unfold contentAt
  simp only [Option.bind_some]
  by_cases hj : j < e.sections.size
  · have hj' : j < (e.updateSectionContent i c).sections.size := by
      rw [updateSectionContent_sections_size]; exact hj
    rw [dif_pos hj, dif_pos hj']
    rw [updateSectionContent_getElem_ne e i c j hj hNe hj']
  · have hj' : ¬ j < (e.updateSectionContent i c).sections.size := by
      rw [updateSectionContent_sections_size]; exact hj
    rw [dif_neg hj, dif_neg hj']

/-! ## Typed-accessor preservation under content-disjoint updates

    Each `section_content_accessor` projection (`dynamic`, `dynstr`,
    `dynsym`, `versym`, `interp`) returns `some _` only when (a) its
    index lookup succeeds and (b) the matching content constructor
    fires.  When the update is at a *different* index from the one the
    accessor reads, the accessor's value is unchanged. -/

/-- `dynsym` accessor preserved when:
    (1) i ≠ dynsymIdx-target,
    (2) c.type ≠ SHT_DYNSYM (update doesn't introduce a new DYNSYM), AND
    (3) original content at i also has type ≠ SHT_DYNSYM.
    All practical callers update `.dynamic` content, satisfying (2) and (3). -/
theorem ElfFile.updateSectionContent_dynsym_eq (e : ElfFile)
    (i : Nat) (c : SectionContent)
    (hNotDynsym : c.type ≠ Layout.ShType.SHT_DYNSYM)
    (hOrigNotDynsym : ∀ (hi : i < e.sections.size),
        (e.sections[i]'hi).type ≠ Layout.ShType.SHT_DYNSYM)
    (hNeIdx : ∀ iSym, e.dynsymIdx = some iSym → i ≠ iSym) :
    (e.updateSectionContent i c).dynsym = e.dynsym := by
  unfold dynsym
  have hUpdIdx : (e.updateSectionContent i c).dynsymIdx = e.dynsymIdx := by
    unfold ElfFile.dynsymIdx ElfFile.findUniqueTypeIdx
    by_cases hi : i < e.sections.size
    · -- Rewrite the updated sections array.
      rw [show (e.updateSectionContent i c).sections =
              e.sections.set i { e.sections[i]'hi with content := c } hi from
            updateSectionContent_sections e i c hi]
      apply firstIdxWhereIn_update_both_false _ _ i hi
      · -- new element at i has c.type ≠ SHT_DYNSYM
        simp [Section.type, hNotDynsym]
      · -- original at i has type ≠ SHT_DYNSYM
        exact decide_eq_false_iff_not.mpr (hOrigNotDynsym hi)
    · simp [updateSectionContent, dif_neg hi]
  rw [hUpdIdx]
  cases hDsi : e.dynsymIdx with
  | none   => rfl
  | some iSym =>
      rw [updateSectionContent_contentAt_some_ne _ _ _ _ (Ne.symm (hNeIdx iSym hDsi))]

/-- `dynstr` accessor preserved when iDyn ≠ shstrndx and iDyn ≠ dynstrIdx-target. -/
theorem ElfFile.updateSectionContent_dynstr_eq (e : ElfFile)
    (i : Nat) (c : SectionContent)
    (hShstrNe : i ≠ e.header.shstrndx.toNat)
    (hNeIdx : ∀ iStr, e.dynstrIdx = some iStr → i ≠ iStr) :
    (e.updateSectionContent i c).dynstr = e.dynstr := by
  unfold dynstr
  rw [updateSectionContent_dynstrIdx _ _ _ hShstrNe]
  cases hDsi : e.dynstrIdx with
  | none   => rfl
  | some iStr =>
      rw [updateSectionContent_contentAt_some_ne _ _ _ _ (Ne.symm (hNeIdx iStr hDsi))]

/-! ## Disjoint-index facts derived from typed accessors

    When `e.X = some _` for a typed accessor X, the content at X's
    index is forced to X's constructor.  If a *different* index
    (`iDyn`) has a content constructor that's not X's, the two
    indices cannot coincide.  These shorthands package the
    contradiction. -/

/-- If `e.dynstr = some ds` and the section at `iDyn` has content
    `.dynamic dyn`, then iDyn ≠ dynstr's index. -/
theorem ElfFile.dynstrIdx_target_ne_of_content_dynamic
    (e : ElfFile) {iDyn : Nat} (hBound : iDyn < e.sections.size)
    {dyn : Array DynEntry}
    (hContent : (e.sections[iDyn]'hBound).content = .dynamic dyn)
    {ds : StringTable} (hDs : e.dynstr = some ds)
    {iStr : Nat} (hStr : e.dynstrIdx = some iStr) :
    iStr ≠ iDyn := by
  intro hEq
  unfold dynstr at hDs
  rw [hStr] at hDs
  unfold contentAt at hDs
  simp only [Option.bind_some] at hDs
  rw [hEq] at hDs
  rw [dif_pos hBound] at hDs
  rw [hContent] at hDs
  cases hDs

/-- If `e.dynstr = some ds`, then iDyn (with `.dynamic` content) is
    not the shstrndx index — `dynstrIdx` would otherwise be `none`
    via a none-shstrtab cascade. -/
theorem ElfFile.shstrndx_ne_of_content_dynamic_of_dynstr
    (e : ElfFile) {iDyn : Nat} (hBound : iDyn < e.sections.size)
    {dyn : Array DynEntry}
    (hContent : (e.sections[iDyn]'hBound).content = .dynamic dyn)
    {ds : StringTable} (hDs : e.dynstr = some ds) :
    iDyn ≠ e.header.shstrndx.toNat := by
  intro hEq
  -- iDyn = shstrndx ⇒ shstrtab pattern-matches `.dynamic _`, returns
  -- none ⇒ findIdxByName returns none ⇒ dynstrIdx = none ⇒ dynstr = none.
  have hShstrNone : e.shstrtab = none := by
    unfold shstrtab
    rw [← hEq]
    rw [dif_pos hBound]
    rw [hContent]
  unfold dynstr at hDs
  unfold contentAt at hDs
  unfold dynstrIdx findIdxByName at hDs
  rw [hShstrNone] at hDs
  cases hDs
