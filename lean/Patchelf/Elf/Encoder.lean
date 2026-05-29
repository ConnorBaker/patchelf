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
public import Patchelf.Elf.GrowEOF

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
  | .raw _ _ bs  => bs
  | .strtab st   => st.bytes
  | .dynamic ds  => writeArray Patchelf.Elf.DynEntry.write ds
  | .dynsym syms => writeArray Patchelf.Elf.Symbol.write syms
  | .versym vs   => writeArray writeU16 vs
  | .nobits _    => ByteArray.empty

/-- Project a byte-layer Section to a SectionHeader for the encoded shdr
    table (content is dropped; size comes from `shdrSize`, which differs
    from `encodedSize` only for NOBITS — NOBITS file size is 0 but the
    shdr's `sh_size` records the runtime allocation). -/
def toShdr (s : Section) : SectionHeader :=
  { name := s.name, type := s.type, flags := s.flags, addr := s.addr,
    offset := s.offset, size := ⟨s.shdrSize⟩,
    link := s.link, info := s.info,
    addralign := s.addralign, entsize := s.entsize }

/-- `(toShdr s).type = s.type = s.content.type`. Used to bridge the
    `decodeSectionContent` if-guards (which check `sh.type`) with
    `Section.content`'s type information. -/
@[simp] theorem toShdr_type (s : Section) : (toShdr s).type = s.content.type := rfl

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
    Backed by `Array.replicate`, which is `@[extern "lean_mk_array"]` —
    one C call rather than an iterated `push` over `List.range`. -/
def zeroBytes (n : Nat) : ByteArray :=
  ⟨Array.replicate n (0 : UInt8)⟩

@[simp] theorem zeroBytes_size (n : Nat) : (zeroBytes n).size = n := by
  unfold zeroBytes; simp [ByteArray.size]

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

/-! ## `syncDtStrszInFile` preserves byte-layer `IsValid` -/

/-- `syncDtStrsz` preserves `Array.back?.any (·.tag = DT_NULL)`. -/
private theorem syncDtStrsz_back_null (dyn : Array DynEntry) (newSize : UInt64) :
    (syncDtStrsz dyn newSize).back?.any (fun e => decide (e.tag = DynTag.null)) =
      dyn.back?.any (fun e => decide (e.tag = DynTag.null)) := by
  unfold syncDtStrsz
  rw [Array.back?_map]
  cases hb : dyn.back? with
  | none   => simp
  | some d => simp [syncDtStrszEntry_tag]

/-- `syncDtStrsz` preserves the SectionContent.WellFormed of `.dynamic`. -/
private theorem syncDtStrsz_content_wf (dyn : Array DynEntry) (newSize : UInt64)
    (h : (SectionContent.dynamic dyn).WellFormed) :
    (SectionContent.dynamic (syncDtStrsz dyn newSize)).WellFormed := by
  show Option.any _ (syncDtStrsz dyn newSize).back? = true
  rw [syncDtStrsz_back_null]
  exact h

/-- Worker: under the active-branch preconditions of `syncDtStrszInFile`,
    show that the post-update `ElfFile` satisfies `IsValid`.

    The key facts:
      * `updateSectionContent` only changes the content at index iDyn.
      * `syncDtStrsz` preserves entry tags and `isStringRef`.
      * The dynamic content's `WellFormed` is preserved (back? entry's
        tag is unchanged).
      * Every other section's `Section` value (name, type, content) is
        unchanged.
    From these, all 8 IsValid clauses follow by inspection. -/
private theorem syncDtStrszInFile_aux_preserves_valid (e : ElfFile)
    (hVal : e.IsValid) (ds : StringTable) (dyn : Array DynEntry) (iDyn : Nat)
    (hDs : e.dynstr = some ds) (hDyn : e.dynamic = some dyn)
    (hIdx : e.dynamicIdx = some iDyn) (hBound : iDyn < e.sections.size) :
    (e.updateSectionContent iDyn
      (SectionContent.dynamic (syncDtStrsz dyn ds.bytes.size.toUInt64))).IsValid := by
  -- e.dynamic = some dyn unfolds to: e.contentAt e.dynamicIdx matches
  -- (.dynamic dyn).  Combined with hIdx, that gives the section content.
  have hContent : (e.sections[iDyn]'hBound).content = .dynamic dyn := by
    -- Step 1: e.contentAt e.dynamicIdx must be some (.dynamic dyn).
    -- The `dynamic` accessor returns `some dyn` only when the matched
    -- contentAt arg is `some (.dynamic dyn)`.
    have hCa : e.contentAt e.dynamicIdx = some (.dynamic dyn) := by
      unfold ElfFile.dynamic at hDyn
      -- unfold reveals: match e.contentAt e.dynamicIdx with | some (.dynamic d) => some d | _ => none
      split at hDyn <;> first | (cases hDyn; assumption) | cases hDyn
    -- Step 2: combine with hIdx.
    rw [hIdx] at hCa
    -- Step 3: contentAt at a known index reduces.
    unfold ElfFile.contentAt at hCa
    simp only [Option.bind_some, dif_pos hBound] at hCa
    exact Option.some.inj hCa
  -- Define e' as the post-update file (notation only; not a generalization).
  let e' := e.updateSectionContent iDyn
    (SectionContent.dynamic (syncDtStrsz dyn ds.bytes.size.toUInt64))
  show e'.IsValid
  -- Header / phdrs / size-of-sections preserved.
  have hHeader : e'.header = e.header := by simp [e']
  have hPhdrs : e'.phdrs = e.phdrs := by simp [e']
  have hSecSize : e'.sections.size = e.sections.size := by simp [e']
  -- Bound transferred.
  have hBound' : iDyn < e'.sections.size := by simp [hSecSize, hBound]
  -- Per-index facts.
  have hOther : ∀ (j : Nat) (hj : j < e.sections.size) (_ : j ≠ iDyn)
      (hj' : j < e'.sections.size),
      e'.sections[j]'hj' = e.sections[j]'hj :=
    fun j hj hne hj' =>
      ElfFile.updateSectionContent_getElem_ne e _ _ _ hj hne hj'
  have hSelf : ∀ (h' : iDyn < e'.sections.size),
      e'.sections[iDyn]'h' = { e.sections[iDyn]'hBound with
        content := .dynamic (syncDtStrsz dyn ds.bytes.size.toUInt64) } :=
    fun h' => ElfFile.updateSectionContent_getElem_self e _ _ hBound h'
  -- iDyn has SHT_DYNAMIC content; derive early since hType/hDsymEq' need it.
  have hType_iDyn : (e.sections[iDyn]'hBound).type = ShType.SHT_DYNAMIC := by
    obtain ⟨_, hT⟩ := ElfFile.findUniqueTypeIdx_section_type e _ _ hIdx
    exact hT
  -- Pointwise equality of `Section` types and names.
  -- At iDyn: original = .dynamic dyn, update = .dynamic (syncDtStrsz ...) → both SHT_DYNAMIC.
  -- At j ≠ iDyn: content unchanged → type unchanged.
  have hType : ∀ (j : Nat) (hj : j < e.sections.size)
      (hj' : j < e'.sections.size),
      (e'.sections[j]'hj').type = (e.sections[j]'hj).type := by
    intro j hj hj'
    by_cases hji : j = iDyn
    · subst hji
      rw [ElfFile.updateSectionContent_type_self _ _ _ hj hj']
      -- c = .dynamic (syncDtStrsz ...) → c.type = SHT_DYNAMIC
      -- original = .dynamic dyn → original.type = SHT_DYNAMIC
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
    · -- c.type = SHT_DYNAMIC ≠ SHT_DYNSYM
      simp [SectionContent.type]; decide
    · -- original at iDyn: SHT_DYNAMIC ≠ SHT_DYNSYM
      intro hi
      simp only [Section.type, hContent, SectionContent.type]; decide
    · intro iSym hSym hEq
      subst hEq
      obtain ⟨_, hT⟩ := ElfFile.findUniqueTypeIdx_section_type e _ _ hSym
      rw [hType_iDyn] at hT
      cases hT
  -- Pointwise equality of `Section.contentWellFormedB`: at index iDyn it
  -- changes from `.dynamic dyn` to `.dynamic (syncDtStrsz ...)`, but
  -- WellFormed is preserved via syncDtStrsz_content_wf.
  have hContentWFB : ∀ (j : Nat) (hj : j < e.sections.size)
      (hj' : j < e'.sections.size),
      ElfFile.Section.contentWellFormedB (e'.sections[j]'hj') =
        ElfFile.Section.contentWellFormedB (e.sections[j]'hj) := by
    intros j hj hj'
    by_cases hjEq : j = iDyn
    · subst hjEq; rw [hSelf hj']
      unfold ElfFile.Section.contentWellFormedB
      simp only [hContent]
      -- both sides reduce to the same Bool: dynamic-back?-null check.
      have hWF : (SectionContent.dynamic dyn).WellFormed ↔
          (SectionContent.dynamic (syncDtStrsz dyn ds.bytes.size.toUInt64)).WellFormed := by
        constructor
        · exact syncDtStrsz_content_wf _ _
        · intro h
          show Option.any _ dyn.back? = true
          rw [← syncDtStrsz_back_null _ ds.bytes.size.toUInt64]; exact h
      simp [hWF]
    · rw [hOther j hj hjEq hj']
  have hStrtabWFB : ∀ (j : Nat) (hj : j < e.sections.size)
      (hj' : j < e'.sections.size),
      ElfFile.Section.strtabWellFormedB (e'.sections[j]'hj') =
        ElfFile.Section.strtabWellFormedB (e.sections[j]'hj) := by
    intros j hj hj'
    by_cases hjEq : j = iDyn
    · subst hjEq; rw [hSelf hj']
      -- Both sides: `.dynamic _` → strtabWellFormedB matches `_ => true`.
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
  -- strtabs_wf — pointwise via hStrtabWFB
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
  · -- e'.dynamic = some (syncDtStrsz dyn _).  Reduce both clauses.
    have hIdx' : e'.dynamicIdx = some iDyn := by
      rw [ElfFile.updateSectionContent_dynamicIdx e iDyn _
        (fun _ => by simp [Section.type, hContent, SectionContent.type])]; exact hIdx
    have hDyn' : e'.dynamic = some (syncDtStrsz dyn ds.bytes.size.toUInt64) := by
      unfold ElfFile.dynamic
      rw [hIdx']
      simp only [ElfFile.contentAt, Option.bind_some, dif_pos hBound']
      rw [hSelf hBound']
    refine ⟨?_, ?_⟩
    · -- dynamicTerminated: rewrite to use the original dyn's properties.
      intro d hd
      rw [hDyn'] at hd
      cases hd
      have ⟨hSize, hBack, hUnique⟩ := hVal.dynamic_wf.1 dyn hDyn
      have hSizeEq : (syncDtStrsz dyn ds.bytes.size.toUInt64).size = dyn.size :=
        syncDtStrsz_size _ _
      refine ⟨hSizeEq ▸ hSize, ?_, ?_⟩
      · -- (syncDtStrsz dyn _)[size - 1].tag = .null
        unfold syncDtStrsz
        simp only [Array.size_map]
        rw [Array.getElem_map, syncDtStrszEntry_tag]
        exact hBack
      · -- uniqueness of DT_NULL position
        intros i hi hT
        rw [hSizeEq] at hi
        unfold syncDtStrsz at hT
        rw [Array.getElem_map, syncDtStrszEntry_tag] at hT
        rw [hSizeEq]
        exact hUnique i hi hT
    · -- dynamicStringRefsValid: e'.dynstr = e.dynstr (via hDsEq'); the
      -- string-ref check reduces to the original via tag/value preservation.
      intro d ds' hd hds'
      rw [hDyn'] at hd
      cases hd
      rw [hDsEq'] at hds'
      rw [hDs] at hds'
      cases hds'
      have hOrig := hVal.dynamic_wf.2 dyn ds hDyn hDs
      intros i hi hSR
      rw [show (syncDtStrsz dyn ds.bytes.size.toUInt64).size
            = dyn.size from syncDtStrsz_size _ _] at hi
      unfold syncDtStrsz
      rw [Array.getElem_map]
      unfold syncDtStrsz at hSR
      rw [Array.getElem_map] at hSR
      rw [syncDtStrszEntry_isStringRef] at hSR
      -- syncDtStrszEntry preserves `.value` on string-ref entries (DT_STRSZ
      -- is the only tag whose value it touches, and DT_STRSZ has
      -- `isStringRef = false`).
      have hValue : (syncDtStrszEntry ds.bytes.size.toUInt64 (dyn[i]'hi)).value
                  = (dyn[i]'hi).value := by
        unfold syncDtStrszEntry
        split
        · rename_i hT
          exfalso
          rw [DynEntry.isStringRef_iff] at hSR
          rcases hSR with h | h | h | h <;> rw [hT] at h <;> cases h
        · rfl
      rw [hValue]
      exact hOrig i hi hSR
  ----------------------------------------
  -- dynsym_wf — both accessors are preserved (dynsym by type
  -- distinctness, dynstr because shstrndx ≠ iDyn).
  ----------------------------------------
  · intros syms ds' hSyms hDs'
    have hOrigSyms : e.dynsym = some syms := hDsymEq' ▸ hSyms
    have hOrigDs   : e.dynstr = some ds'  := hDsEq'   ▸ hDs'
    exact hVal.dynsym_wf syms ds' hOrigSyms hOrigDs
  ----------------------------------------
  -- content_wf — pointwise via hContentWFB
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
  -- names_unique — shstrtab preserved (since iDyn ≠ shstrndx via hShstrNe);
  -- the name-unique-at relation reduces pointwise via hName.
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
        -- `nameUniqueAt` quantifies over indices, comparing name fields
        -- via `st.lookup`.  Names at every index are preserved, so the
        -- predicate transfers from `e` to `e'`.
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

/-- `syncDtStrszInFile` preserves the byte-layer `IsValid` invariant. -/
theorem syncDtStrszInFile_preserves_valid (e : ElfFile) (hVal : e.IsValid) :
    (syncDtStrszInFile e).IsValid := by
  -- The match has 4 dead branches (returning `e`) and 1 active branch.
  -- Use a single rewrite that exposes the structure once the
  -- discriminants are stable.
  show (match e.dynstr, e.dynamic, e.dynamicIdx with
    | some ds, some dyn, some iDyn =>
        if _h : iDyn < e.sections.size then
          e.updateSectionContent iDyn
            (.dynamic (syncDtStrsz dyn ds.bytes.size.toUInt64))
        else e
    | _, _, _ => e).IsValid
  cases hDs : e.dynstr with
  | none => exact hVal
  | some ds =>
    cases hDyn : e.dynamic with
    | none => exact hVal
    | some dyn =>
      cases hIdx : e.dynamicIdx with
      | none => exact hVal
      | some iDyn =>
        -- Reduce the match to the if-then-else.
        show (if _h : iDyn < e.sections.size then
          e.updateSectionContent iDyn
            (.dynamic (syncDtStrsz dyn ds.bytes.size.toUInt64))
        else e).IsValid
        by_cases hBound : iDyn < e.sections.size
        · rw [dif_pos hBound]
          exact syncDtStrszInFile_aux_preserves_valid
            e hVal ds dyn iDyn hDs hDyn hIdx hBound
        · rw [dif_neg hBound]; exact hVal

/-! ## `syncDtStrszInFile` preserves `IsLoadable`

    The FIRST pre-encode pass (`encode = encodeBody ∘ prepLayoutForEncode
    ∘ syncDtStrszInFile`).  Structurally identical to
    `syncDtAddrTagsInFile`: either a no-op or a same-size `Array.map` of
    the `.dynamic` section's entries (`syncDtStrsz = dyn.map
    (syncDtStrszEntry _)`).  So it preserves `phdrs` verbatim and
    per-section `(type, offset, encodedSize)` everywhere; the four
    `IsLoadable` clauses transport directly.  Combined with
    `prepLayoutForEncodeWith_preserves_loadable`, this gives end-to-end
    loadability of the IR fed to `encodeBody`. -/

/-- No-op-or-update disjunction for `syncDtStrszInFile` (companion to
    `syncDtAddrTagsInFile_cases`).  Parameterized by the new DT_STRSZ
    value `newSize` rather than the `StringTable`, so the existential's
    `e.dynstr` discriminant doesn't clash with the active-branch `cases`. -/
theorem syncDtStrszInFile_cases (e : ElfFile) :
    syncDtStrszInFile e = e ∨
    ∃ (iDyn : Nat) (h : iDyn < e.sections.size) (dyn : Array DynEntry) (newSize : UInt64),
      (e.sections[iDyn]'h).content = .dynamic dyn ∧
      syncDtStrszInFile e =
        e.updateSectionContent iDyn (.dynamic (syncDtStrsz dyn newSize)) := by
  rw [show syncDtStrszInFile e = (match e.dynstr, e.dynamic, e.dynamicIdx with
    | some ds, some dyn, some iDyn =>
        if _h : iDyn < e.sections.size then
          e.updateSectionContent iDyn (.dynamic (syncDtStrsz dyn ds.bytes.size.toUInt64))
        else e
    | _, _, _ => e) from rfl]
  cases hDs : e.dynstr with
  | none => exact Or.inl rfl
  | some ds =>
    cases hDyn : e.dynamic with
    | none => exact Or.inl rfl
    | some dyn =>
      cases hIdx : e.dynamicIdx with
      | none => exact Or.inl rfl
      | some iDyn =>
        by_cases hLt : iDyn < e.sections.size
        · have hContent : (e.sections[iDyn]'hLt).content = .dynamic dyn := by
            unfold ElfFile.dynamic at hDyn
            rw [hIdx] at hDyn
            unfold ElfFile.contentAt at hDyn
            simp only [Option.bind_some] at hDyn
            rw [dif_pos hLt] at hDyn
            generalize hC : (e.sections[iDyn]'hLt).content = c at hDyn
            cases c with
            | dynamic dyn' => simp at hDyn; rw [hDyn]
            | raw _ => simp at hDyn
            | strtab _ => simp at hDyn
            | dynsym _ => simp at hDyn
            | versym _ => simp at hDyn
            | nobits _ => simp at hDyn
          refine Or.inr ⟨iDyn, hLt, dyn, ds.bytes.size.toUInt64, hContent, ?_⟩
          simp only [dif_pos hLt]
        · exact Or.inl (by simp only [dif_neg hLt])

@[simp] theorem syncDtStrszInFile_phdrs (e : ElfFile) :
    (syncDtStrszInFile e).phdrs = e.phdrs := by
  rcases syncDtStrszInFile_cases e with hEq | ⟨iDyn, hLt, dyn, nz, hContent, hEq⟩
  · rw [hEq]
  · rw [hEq]; simp

@[simp] theorem syncDtStrszInFile_sections_size (e : ElfFile) :
    (syncDtStrszInFile e).sections.size = e.sections.size := by
  rcases syncDtStrszInFile_cases e with hEq | ⟨iDyn, hLt, dyn, nz, hContent, hEq⟩
  · rw [hEq]
  · rw [hEq]; simp

/-- Per-section `offset` preserved (every index). -/
theorem syncDtStrszInFile_sections_offset (e : ElfFile) (j : Nat)
    (hj : j < (syncDtStrszInFile e).sections.size) (hjE : j < e.sections.size) :
    ((syncDtStrszInFile e).sections[j]'hj).offset = (e.sections[j]'hjE).offset := by
  rcases syncDtStrszInFile_cases e with hEq | ⟨iDyn, hLt, dyn, nz, hContent, hEq⟩
  · simp only [hEq]
  · simp only [hEq] at hj ⊢
    exact ElfFile.updateSectionContent_offset e iDyn _ j hjE hj

/-- Per-section `type` preserved (the map keeps `.dynamic`). -/
theorem syncDtStrszInFile_sections_type (e : ElfFile) (j : Nat)
    (hj : j < (syncDtStrszInFile e).sections.size) (hjE : j < e.sections.size) :
    ((syncDtStrszInFile e).sections[j]'hj).type = (e.sections[j]'hjE).type := by
  rcases syncDtStrszInFile_cases e with hEq | ⟨iDyn, hLt, dyn, nz, hContent, hEq⟩
  · simp only [hEq]
  · simp only [hEq] at hj ⊢
    by_cases hji : j = iDyn
    · subst hji
      rw [ElfFile.updateSectionContent_type_self e j _ hjE hj]
      simp [SectionContent.type, Section.type, hContent]
    · exact ElfFile.updateSectionContent_type e iDyn _ j hjE hji hj

/-- Per-section `encodedSize` preserved (same-size `Array.map`). -/
theorem syncDtStrszInFile_sections_encodedSize (e : ElfFile) (j : Nat)
    (hj : j < (syncDtStrszInFile e).sections.size) (hjE : j < e.sections.size) :
    ((syncDtStrszInFile e).sections[j]'hj).encodedSize = (e.sections[j]'hjE).encodedSize := by
  rcases syncDtStrszInFile_cases e with hEq | ⟨iDyn, hLt, dyn, nz, hContent, hEq⟩
  · simp only [hEq]
  · simp only [hEq] at hj ⊢
    show ((e.updateSectionContent iDyn (.dynamic (dyn.map (syncDtStrszEntry nz)))).sections[j]'hj).encodedSize = _
    exact updateSectionContent_dynamic_map_encodedSize_eq e iDyn hLt dyn hContent
      (syncDtStrszEntry nz) j hjE hj

/-- `dynamicIdx` preserved (the updated content is still `.dynamic`). -/
theorem syncDtStrszInFile_dynamicIdx (e : ElfFile) :
    (syncDtStrszInFile e).dynamicIdx = e.dynamicIdx := by
  rcases syncDtStrszInFile_cases e with hEq | ⟨iDyn, hLt, dyn, nz, hContent, hEq⟩
  · rw [hEq]
  · rw [hEq]
    exact ElfFile.updateSectionContent_dynamicIdx e iDyn _ (by
      intro hi; simp [SectionContent.type, Section.type, hContent])

/-- `interpIdx` preserved (needs `iDyn ≠ shstrndx` from the dynstr witness). -/
theorem syncDtStrszInFile_interpIdx (e : ElfFile)
    {ds : StringTable} (hDs : e.dynstr = some ds) :
    (syncDtStrszInFile e).interpIdx = e.interpIdx := by
  rcases syncDtStrszInFile_cases e with hEq | ⟨iDyn, hLt, dyn, nz, hContent, hEq⟩
  · rw [hEq]
  · rw [hEq]
    have hShstrNe : iDyn ≠ e.header.shstrndx.toNat :=
      ElfFile.shstrndx_ne_of_content_dynamic_of_dynstr e hLt hContent hDs
    exact ElfFile.updateSectionContent_findIdxByName e iDyn _ _ hShstrNe

/-- `syncDtStrszInFile` preserves `IsLoadable`.  Same `dynstr`
    precondition as `_preserves_valid`/`syncDtAddrTagsInFile`
    (yields `iDyn ≠ shstrndx`). -/
theorem syncDtStrszInFile_preserves_loadable (e : ElfFile) (hLoad : e.IsLoadable)
    {ds : StringTable} (hDs : e.dynstr = some ds) :
    (syncDtStrszInFile e).IsLoadable := by
  have hPhdrs := syncDtStrszInFile_phdrs e
  have hSecSz := syncDtStrszInFile_sections_size e
  refine
    { toIsValid := syncDtStrszInFile_preserves_valid e hLoad.toIsValid
      sections_nonoverlapping := ?_
      pt_interp_agrees := ?_
      pt_dynamic_agrees := ?_
      segment_congruent := ?_ }
  · intro i hi j hj hNe
    have hiE : i < e.sections.size := by rw [hSecSz] at hi; exact hi
    have hjE : j < e.sections.size := by rw [hSecSz] at hj; exact hj
    have hTi := syncDtStrszInFile_sections_type e i hi hiE
    have hTj := syncDtStrszInFile_sections_type e j hj hjE
    have hOi := syncDtStrszInFile_sections_offset e i hi hiE
    have hOj := syncDtStrszInFile_sections_offset e j hj hjE
    have hSi := syncDtStrszInFile_sections_encodedSize e i hi hiE
    have hSj := syncDtStrszInFile_sections_encodedSize e j hj hjE
    have hBase := hLoad.sections_nonoverlapping i hiE j hjE hNe
    simp only [hTi, hTj, hOi, hOj, hSi, hSj]
    exact hBase
  · unfold ElfFile.ptInterpAgreement
    rw [syncDtStrszInFile_interpIdx e hDs]
    cases hI : e.interpIdx with
    | none => trivial
    | some iS =>
      intro hLt iPh hPh hPhT
      simp only [hPhdrs] at hPh hPhT ⊢
      have hSecLtE : iS < e.sections.size := by rw [hSecSz] at hLt; exact hLt
      rw [syncDtStrszInFile_sections_offset e iS hLt hSecLtE]
      have hBase := hLoad.pt_interp_agrees
      unfold ElfFile.ptInterpAgreement at hBase
      rw [hI] at hBase
      exact hBase hSecLtE iPh hPh hPhT
  · unfold ElfFile.ptDynamicAgreement
    rw [syncDtStrszInFile_dynamicIdx e]
    cases hD : e.dynamicIdx with
    | none => trivial
    | some iS =>
      intro hLt iPh hPh hPhT
      simp only [hPhdrs] at hPh hPhT ⊢
      have hSecLtE : iS < e.sections.size := by rw [hSecSz] at hLt; exact hLt
      rw [syncDtStrszInFile_sections_offset e iS hLt hSecLtE]
      have hBase := hLoad.pt_dynamic_agrees
      unfold ElfFile.ptDynamicAgreement at hBase
      rw [hD] at hBase
      exact hBase hSecLtE iPh hPh hPhT
  · unfold ElfFile.segmentCongruence
    intro iPh hPh hPhT
    simp only [hPhdrs] at hPh hPhT ⊢
    exact hLoad.segment_congruent iPh hPh hPhT

/-! ## `syncDtStrszInFile` preserves the structural disjointness inputs

    These lift the `prepLayoutForEncode_preserves_loadable` preconditions
    through the first pre-encode pass, so the two passes compose into the
    end-to-end `prepLayout_syncDtStrsz_preserves_loadable` below. -/

@[simp] theorem syncDtStrszInFile_header (e : ElfFile) :
    (syncDtStrszInFile e).header = e.header := by
  rcases syncDtStrszInFile_cases e with hEq | ⟨iDyn, hLt, dyn, nz, hContent, hEq⟩
  · rw [hEq]
  · rw [hEq]; simp

/-- `dynstr` preserved (needs the dynstr witness for the disjoint-index facts). -/
theorem syncDtStrszInFile_dynstr (e : ElfFile)
    {ds : StringTable} (hDs : e.dynstr = some ds) :
    (syncDtStrszInFile e).dynstr = e.dynstr := by
  rcases syncDtStrszInFile_cases e with hEq | ⟨iDyn, hLt, dyn, nz, hContent, hEq⟩
  · rw [hEq]
  · rw [hEq]
    have hShstrNe : iDyn ≠ e.header.shstrndx.toNat :=
      ElfFile.shstrndx_ne_of_content_dynamic_of_dynstr e hLt hContent hDs
    apply ElfFile.updateSectionContent_dynstr_eq _ _ _ hShstrNe
    intro iStr hStr
    exact (ElfFile.dynstrIdx_target_ne_of_content_dynamic e hLt hContent hDs hStr).symm

theorem syncDtStrszInFile_headerPhdrDisjoint (e : ElfFile)
    (h : e.headerPhdrDisjoint) : (syncDtStrszInFile e).headerPhdrDisjoint := by
  unfold ElfFile.headerPhdrDisjoint at h ⊢
  simp only [syncDtStrszInFile_header, syncDtStrszInFile_phdrs]
  exact h

theorem syncDtStrszInFile_headerSectionDisjoint (e : ElfFile)
    (h : e.headerSectionDisjoint) : (syncDtStrszInFile e).headerSectionDisjoint := by
  unfold ElfFile.headerSectionDisjoint at h ⊢
  intro i hi
  have hiE : i < e.sections.size := by rw [syncDtStrszInFile_sections_size] at hi; exact hi
  have hT := syncDtStrszInFile_sections_type e i hi hiE
  have hO := syncDtStrszInFile_sections_offset e i hi hiE
  have hS := syncDtStrszInFile_sections_encodedSize e i hi hiE
  simp only [hT, hO, hS]
  exact h i hiE

theorem syncDtStrszInFile_phdrSectionDisjoint (e : ElfFile)
    (h : e.phdrSectionDisjoint) : (syncDtStrszInFile e).phdrSectionDisjoint := by
  unfold ElfFile.phdrSectionDisjoint at h ⊢
  intro i hi
  have hiE : i < e.sections.size := by rw [syncDtStrszInFile_sections_size] at hi; exact hi
  have hT := syncDtStrszInFile_sections_type e i hi hiE
  have hO := syncDtStrszInFile_sections_offset e i hi hiE
  have hS := syncDtStrszInFile_sections_encodedSize e i hi hiE
  simp only [syncDtStrszInFile_header, syncDtStrszInFile_phdrs, hT, hO, hS]
  exact h i hiE

theorem syncDtStrszInFile_section0Null (e : ElfFile)
    (h : ∀ (h : 0 < e.sections.size), (e.sections[0]'h).type = ShType.SHT_NULL) :
    ∀ (h0 : 0 < (syncDtStrszInFile e).sections.size),
      ((syncDtStrszInFile e).sections[0]'h0).type = ShType.SHT_NULL := by
  intro h0
  have h0E : 0 < e.sections.size := by rw [syncDtStrszInFile_sections_size] at h0; exact h0
  rw [syncDtStrszInFile_sections_type e 0 h0 h0E]
  exact h h0E

/-! ## `syncDtStrszInFile` establishes `dynStrszCoherent` (§5.1 Obligation A)

    The first pre-encode pass rewrites every DT_STRSZ entry's value to
    `dynstr.bytes.size.toUInt64`, so its output is `dynStrszCoherent` by
    construction — provided the dynstr byte length fits in UInt64 (so the
    `toNat ∘ toUInt64` round-trip is exact).  Composed with the layout
    pre-pass's preservation (`growEOFWith` + `syncDtAddrTagsInFile`, both
    leave DT_STRSZ alone), this gives `dynStrszCoherent` of the normalized
    form — the hypothesis `syncDtStrszInFile_eq_id` needs for
    `EncodePreconditions.syncOk`. -/

/-- `(syncDtStrszInFile e).dynstr = e.dynstr`, unconditionally (the
    witness-form `syncDtStrszInFile_dynstr` plus the no-`dynstr` no-op). -/
theorem syncDtStrszInFile_dynstr_eq (e : ElfFile) :
    (syncDtStrszInFile e).dynstr = e.dynstr := by
  cases hDs : e.dynstr with
  | none =>
    have : syncDtStrszInFile e = e := by unfold syncDtStrszInFile; rw [hDs]
    rw [this]; exact hDs
  | some ds => rw [syncDtStrszInFile_dynstr e hDs]; exact hDs

/-- In the active branch, `(syncDtStrszInFile e).dynamic` is the synced
    array `syncDtStrsz dyn ds.bytes.size.toUInt64`. -/
theorem syncDtStrszInFile_dynamic_synced (e : ElfFile) (ds : StringTable)
    (dyn : Array DynEntry) (hDs : e.dynstr = some ds) (hDyn : e.dynamic = some dyn) :
    (syncDtStrszInFile e).dynamic = some (syncDtStrsz dyn ds.bytes.size.toUInt64) := by
  obtain ⟨iDyn, hIdx, hLt, hContent⟩ := ElfFile.dynamic_eq_some_elim e dyn hDyn
  have hSync : syncDtStrszInFile e
      = e.updateSectionContent iDyn (.dynamic (syncDtStrsz dyn ds.bytes.size.toUInt64)) := by
    unfold syncDtStrszInFile
    rw [hDs, hDyn, hIdx]
    simp only [dif_pos hLt]
  rw [hSync]
  unfold ElfFile.dynamic
  rw [ElfFile.updateSectionContent_dynamicIdx e iDyn _ (by
        intro hi; simp [SectionContent.type, Section.type, hContent]), hIdx]
  unfold ElfFile.contentAt
  have hLt' : iDyn < (e.updateSectionContent iDyn
      (.dynamic (syncDtStrsz dyn ds.bytes.size.toUInt64))).sections.size := by
    rw [ElfFile.updateSectionContent_sections_size]; exact hLt
  simp only [Option.bind_some, dif_pos hLt']
  rw [ElfFile.updateSectionContent_getElem_self e iDyn _ hLt hLt']

/-- `e.dynamic = none → (syncDtStrszInFile e).dynamic = none`. -/
theorem syncDtStrszInFile_dynamic_none (e : ElfFile) (hDyn : e.dynamic = none) :
    (syncDtStrszInFile e).dynamic = none := by
  cases hDs : e.dynstr with
  | none =>
    have : syncDtStrszInFile e = e := by unfold syncDtStrszInFile; rw [hDs]
    rw [this]; exact hDyn
  | some ds =>
    have : syncDtStrszInFile e = e := by unfold syncDtStrszInFile; rw [hDs, hDyn]
    rw [this]; exact hDyn

/-- Establishment: `syncDtStrszInFile e` is `dynStrszCoherent`, given the
    dynstr byte length fits in UInt64.  No-`dynamic` case is vacuous. -/
theorem syncDtStrszInFile_establishes_dynStrszCoherent (e : ElfFile)
    (hFit : ∀ ds, e.dynstr = some ds → ds.bytes.size < UInt64.size) :
    (syncDtStrszInFile e).dynStrszCoherent := by
  intro dyn' ds' hD hS i hi hT
  rw [syncDtStrszInFile_dynstr_eq] at hS
  have hFit' := hFit ds' hS
  cases hDyn0 : e.dynamic with
  | none =>
    rw [syncDtStrszInFile_dynamic_none e hDyn0] at hD
    exact absurd hD (by simp)
  | some dyn0 =>
    rw [syncDtStrszInFile_dynamic_synced e ds' dyn0 hS hDyn0] at hD
    have hEqArr : syncDtStrsz dyn0 ds'.bytes.size.toUInt64 = dyn' := Option.some.inj hD
    subst hEqArr
    unfold syncDtStrsz at hi hT ⊢
    rw [Array.getElem_map] at hT ⊢
    rw [syncDtStrszEntry_tag] at hT
    show (syncDtStrszEntry ds'.bytes.size.toUInt64 (dyn0[i]'_)).value.toNat = ds'.bytes.size
    unfold syncDtStrszEntry
    rw [if_pos hT]
    show (ds'.bytes.size.toUInt64).toNat = ds'.bytes.size
    exact UInt64.toNat_ofNat_of_lt' hFit'

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

/-- Layout pre-pass for the encoder.  When the input is already laid out
    (`layoutAlreadyValid e = true`), this is the identity — preserving
    byte-for-byte stability for parser-derived inputs.  Otherwise:

      1. `growEOFWith pageSize? e` — append stale sections to a new
         region at file end (aligned to `pageSize? ⊔ maxPtLoadAlign`),
         extend the last PT_LOAD to cover it, update PT_INTERP /
         PT_DYNAMIC / shoff.
      2. `syncDtAddrTagsInFile e` — rewrite `.dynamic`'s DT_STRTAB /
         DT_SYMTAB / DT_HASH / DT_GNU_HASH / DT_VERNEED / DT_VERSYM /
         DT_JMPREL / DT_REL / DT_RELA tags to point at the moved
         sections' new addresses. -/
def prepLayoutForEncodeWith (pageSize? : Option Nat) (e : ElfFile) : ElfFile :=
  if layoutAlreadyValid e then e
  else syncDtAddrTagsInFile (growEOFWith pageSize? e)

/-- `prepLayoutForEncodeWith none` — auto-detected page size. -/
def prepLayoutForEncode (e : ElfFile) : ElfFile :=
  prepLayoutForEncodeWith none e

/-- Encode a pure-IR ElfFile to bytes.

    Pipeline:
      0. Sync DT_STRSZ entries to match `.dynstr.bytes.size`.
      1. Conditional layout pre-pass via `prepLayoutForEncode`.
      2. `encodeBody` — the splice cascade.

    Marked `@[irreducible]`; use `encode_eq` for propositional
    unfolding. -/
@[irreducible] def encode (e : ElfFile) : ByteArray :=
  let e := syncDtStrszInFile e
  let e := prepLayoutForEncode e
  encodeBody e

/-- `encode` with an explicit page-size override.  When provided, the
    layout pre-pass uses `max pageSize (maxPtLoadAlign e.phdrs)` for
    appended-region alignment.  See `growEOFWith` for context. -/
def encodeWith (pageSize? : Option Nat) (e : ElfFile) : ByteArray :=
  let e := syncDtStrszInFile e
  let e := prepLayoutForEncodeWith pageSize? e
  encodeBody e

theorem encode_eq (e : ElfFile) :
    encode e =
      encodeBody (prepLayoutForEncode (syncDtStrszInFile e)) := by
  unfold encode; rfl

/-- When the input is already laid out, `prepLayoutForEncode` is the
    identity.  This is the master-theorem path. -/
@[simp] theorem prepLayoutForEncode_of_layoutAlreadyValid
    {e : ElfFile} (hLay : layoutAlreadyValid e = true) :
    prepLayoutForEncode e = e := by
  unfold prepLayoutForEncode prepLayoutForEncodeWith
  simp [hLay]

/-- The encoder's layout pre-pass produces a layout where all 7 splice
    regions are pairwise disjoint, given the structural input invariants.

    Composition of `growEOFWith_produces_spliceRegionsDisjoint` and
    `syncDtAddrTagsInFile_preserves_spliceRegionsDisjoint` for the
    non-trivial branch; for the fast-path branch, derives the missing
    `sectionsNonOverlapping ∧ shdrSectionDisjoint` from
    `layoutAlreadyValid`.  This is the form downstream callers (op-level
    Tier D) want to consume. -/
theorem prepLayoutForEncodeWith_produces_spliceRegionsDisjoint
    (pageSize? : Option Nat) (e : ElfFile)
    (hSection0Null : ∀ (h : 0 < e.sections.size),
      (e.sections[0]'h).type = ShType.SHT_NULL)
    (hHeaderPhdr : e.headerPhdrDisjoint)
    (hHeaderShdr : e.headerShdrDisjoint)
    (hPhdrShdr   : e.phdrShdrDisjoint)
    (hHeaderSec  : e.headerSectionDisjoint)
    (hPhdrSec    : e.phdrSectionDisjoint) :
    (prepLayoutForEncodeWith pageSize? e).spliceRegionsDisjoint := by
  unfold prepLayoutForEncodeWith
  by_cases hLay : layoutAlreadyValid e = true
  · -- Fast path: output = e.  layoutAlreadyValid gives the 2 missing clauses.
    simp only [hLay, ↓reduceIte]
    obtain ⟨hSec, hShdrSec⟩ := (layoutAlreadyValid_iff e).mp hLay
    exact
      { sections_disjoint := hSec
        hdr_phdr_disjoint := hHeaderPhdr
        hdr_shdr_disjoint := hHeaderShdr
        phdr_shdr_disjoint := hPhdrShdr
        hdr_sec_disjoint := hHeaderSec
        phdr_sec_disjoint := hPhdrSec
        shdr_sec_disjoint := hShdrSec }
  · -- Non-trivial path: compose growEOFWith + syncDtAddrTagsInFile.
    simp only [hLay]
    have hGrow := growEOFWith_produces_spliceRegionsDisjoint pageSize? e
      hSection0Null hHeaderPhdr hHeaderShdr hPhdrShdr hHeaderSec hPhdrSec
    exact syncDtAddrTagsInFile_preserves_spliceRegionsDisjoint _ hGrow

/-- `prepLayoutForEncode` (auto-detected page size) produces a layout
    where all 7 splice regions are pairwise disjoint.  Specialization of
    `prepLayoutForEncodeWith_produces_spliceRegionsDisjoint` with
    `pageSize? = none`. -/
theorem prepLayoutForEncode_produces_spliceRegionsDisjoint (e : ElfFile)
    (hSection0Null : ∀ (h : 0 < e.sections.size),
      (e.sections[0]'h).type = ShType.SHT_NULL)
    (hHeaderPhdr : e.headerPhdrDisjoint)
    (hHeaderShdr : e.headerShdrDisjoint)
    (hPhdrShdr   : e.phdrShdrDisjoint)
    (hHeaderSec  : e.headerSectionDisjoint)
    (hPhdrSec    : e.phdrSectionDisjoint) :
    (prepLayoutForEncode e).spliceRegionsDisjoint :=
  prepLayoutForEncodeWith_produces_spliceRegionsDisjoint none e
    hSection0Null hHeaderPhdr hHeaderShdr hPhdrShdr hHeaderSec hPhdrSec

/-- The encoder's layout pre-pass preserves `IsLoadable`.

    Composition of `growEOFWith_preserves_loadable` (the layout move) and
    `syncDtAddrTagsInFile_preserves_loadable` (the DT_* address rewrite)
    for the non-trivial branch; the fast-path branch is the identity.
    Completes the §1.2 `_preserves_loadable` ladder at the pipeline level:
    the encoder's full layout pre-pass takes a loadable input to a loadable
    output.

    Preconditions: `hLoad` (input loadability) + `(e.phdrs.size + 1) <
    UInt16.size` (fresh-PT_LOAD phnum bump) + the structural disjointness
    invariants (feed each `growEOFWith` branch's `sections_nonoverlapping`)
    + `e.dynstr = some ds` (yields `iDyn ≠ shstrndx` for the
    `syncDtAddrTagsInFile` post-pass).  All parser-derivable for real
    ELFs. -/
theorem prepLayoutForEncodeWith_preserves_loadable
    (pageSize? : Option Nat) (e : ElfFile)
    (hLoad : e.IsLoadable)
    (hPhdrFit : (e.phdrs.size + 1) < UInt16.size)
    (hSection0Null : ∀ (h : 0 < e.sections.size),
      (e.sections[0]'h).type = ShType.SHT_NULL)
    (hHeaderPhdr : e.headerPhdrDisjoint)
    (hHeaderSec  : e.headerSectionDisjoint)
    (hPhdrSec    : e.phdrSectionDisjoint)
    {ds : StringTable} (hDs : e.dynstr = some ds) :
    (prepLayoutForEncodeWith pageSize? e).IsLoadable := by
  unfold prepLayoutForEncodeWith
  by_cases hLay : layoutAlreadyValid e = true
  · simp only [hLay, ↓reduceIte]; exact hLoad
  · simp only [hLay]
    have hGrow : (growEOFWith pageSize? e).IsLoadable :=
      growEOFWith_preserves_loadable pageSize? e hLoad hPhdrFit
        hSection0Null hHeaderPhdr hHeaderSec hPhdrSec
    have hGrowDs : (growEOFWith pageSize? e).dynstr = some ds := by
      rw [growEOFWith_dynstr]; exact hDs
    exact syncDtAddrTagsInFile_preserves_loadable _ hGrow hGrowDs

/-- `prepLayoutForEncode` (auto-detected page size) preserves `IsLoadable`.
    Specialization of `prepLayoutForEncodeWith_preserves_loadable` with
    `pageSize? = none`. -/
theorem prepLayoutForEncode_preserves_loadable (e : ElfFile)
    (hLoad : e.IsLoadable)
    (hPhdrFit : (e.phdrs.size + 1) < UInt16.size)
    (hSection0Null : ∀ (h : 0 < e.sections.size),
      (e.sections[0]'h).type = ShType.SHT_NULL)
    (hHeaderPhdr : e.headerPhdrDisjoint)
    (hHeaderSec  : e.headerSectionDisjoint)
    (hPhdrSec    : e.phdrSectionDisjoint)
    {ds : StringTable} (hDs : e.dynstr = some ds) :
    (prepLayoutForEncode e).IsLoadable :=
  prepLayoutForEncodeWith_preserves_loadable none e hLoad hPhdrFit
    hSection0Null hHeaderPhdr hHeaderSec hPhdrSec hDs

/-- End-to-end: the IR the encoder actually feeds to `encodeBody`
    (`prepLayoutForEncode (syncDtStrszInFile e)`) is `IsLoadable`,
    given a loadable input + the parser-derivable structural invariants.

    This is the full composition of both pre-encode passes — the
    DT_STRSZ resync (`syncDtStrszInFile`) then the layout pre-pass
    (`prepLayoutForEncode`).  `syncDtStrszInFile` preserves every
    precondition the second pass needs (loadability, the phnum bound, the
    section-0-NULL and disjointness invariants, and `dynstr`), so the two
    `_preserves_loadable` theorems chain.  Note `encode_eq` shows
    `encode e = encodeBody (prepLayoutForEncode (syncDtStrszInFile e))`,
    so this is loadability of exactly the structure `encodeBody` serializes. -/
theorem prepLayout_syncDtStrsz_preserves_loadable (e : ElfFile)
    (hLoad : e.IsLoadable)
    (hPhdrFit : (e.phdrs.size + 1) < UInt16.size)
    (hSection0Null : ∀ (h : 0 < e.sections.size),
      (e.sections[0]'h).type = ShType.SHT_NULL)
    (hHeaderPhdr : e.headerPhdrDisjoint)
    (hHeaderSec  : e.headerSectionDisjoint)
    (hPhdrSec    : e.phdrSectionDisjoint)
    {ds : StringTable} (hDs : e.dynstr = some ds) :
    (prepLayoutForEncode (syncDtStrszInFile e)).IsLoadable := by
  have hLoad' := syncDtStrszInFile_preserves_loadable e hLoad hDs
  have hDs' : (syncDtStrszInFile e).dynstr = some ds := by
    rw [syncDtStrszInFile_dynstr e hDs]; exact hDs
  exact prepLayoutForEncode_preserves_loadable (syncDtStrszInFile e) hLoad'
    (by rw [syncDtStrszInFile_phdrs]; exact hPhdrFit)
    (syncDtStrszInFile_section0Null e hSection0Null)
    (syncDtStrszInFile_headerPhdrDisjoint e hHeaderPhdr)
    (syncDtStrszInFile_headerSectionDisjoint e hHeaderSec)
    (syncDtStrszInFile_phdrSectionDisjoint e hPhdrSec)
    hDs'

/-- `prepLayoutForEncode` preserves `dynStrszCoherent`.  Fast path is the
    identity; the layout path composes `growEOFWith` (preserves both
    `.dynamic`/`.dynstr`) with `syncDtAddrTagsInFile` (identity on
    DT_STRSZ).  Needs `e.dynstr = some ds` for the `syncDtAddrTagsInFile`
    post-pass.  (§5.1 Obligation A.) -/
theorem prepLayoutForEncode_preserves_dynStrszCoherent (e : ElfFile)
    {ds : StringTable} (hDs : e.dynstr = some ds) (hCoh : e.dynStrszCoherent) :
    (prepLayoutForEncode e).dynStrszCoherent := by
  unfold prepLayoutForEncode prepLayoutForEncodeWith
  by_cases hLay : layoutAlreadyValid e = true
  · simp only [hLay, ↓reduceIte]; exact hCoh
  · simp only [hLay, Bool.false_eq_true, ↓reduceIte]
    have hGrow := growEOFWith_preserves_dynStrszCoherent none e hCoh
    have hGrowDs : (growEOFWith none e).dynstr = some ds := by
      rw [growEOFWith_dynstr]; exact hDs
    exact syncDtAddrTagsInFile_preserves_dynStrszCoherent _ hGrowDs hGrow

/-- The encoder's normalized form `prepLayoutForEncode (syncDtStrszInFile e)`
    is `dynStrszCoherent`: the first pass establishes it (DT_STRSZ rewritten
    to `dynstr.bytes.size`), the layout pass preserves it.  Stated with the
    `.dynstr` witness (the layout pass's `syncDtAddrTagsInFile` post-pass
    needs it; every `.dynamic`-mutating op has `.dynstr`).  This is exactly
    what `syncDtStrszInFile_eq_id` needs to discharge
    `EncodePreconditions.syncOk` on the normalized form (§5.1 Obligation A
    capstone). -/
theorem prepLayout_syncDtStrsz_dynStrszCoherent (e : ElfFile)
    {ds : StringTable} (hDs : e.dynstr = some ds)
    (hFit : ds.bytes.size < UInt64.size) :
    (prepLayoutForEncode (syncDtStrszInFile e)).dynStrszCoherent := by
  have hCoh : (syncDtStrszInFile e).dynStrszCoherent :=
    syncDtStrszInFile_establishes_dynStrszCoherent e
      (fun ds' hDs' => by rw [hDs'] at hDs; cases hDs; exact hFit)
  have hDs' : (syncDtStrszInFile e).dynstr = some ds := by
    rw [syncDtStrszInFile_dynstr_eq]; exact hDs
  exact prepLayoutForEncode_preserves_dynStrszCoherent (syncDtStrszInFile e) hDs' hCoh

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
  | .raw _ _ _ => simp
  | .strtab _ => simp
  | .dynamic ds =>
    exact writeArray_size_of_uniform DynEntry.write Layout.dynEntrySize
            DynEntry.write_size ds
  | .dynsym syms =>
    exact writeArray_size_of_uniform Symbol.write Layout.symEntrySize
            Symbol.write_size syms
  | .versym vs =>
    exact writeArray_size_of_uniform Writer.writeU16 2 (fun _ => writeU16_size _) vs
  | .nobits _ => simp

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
