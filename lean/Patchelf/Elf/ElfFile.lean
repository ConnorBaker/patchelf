/-
  ElfFile: pure-IR byte-layer model with typed section content.

  An ELF file is modeled as `{ header, phdrs, sections }` where each
  section carries typed content via `SectionContent` (raw, strtab,
  dynamic, dynsym, versym, nobits).  `.verneed`, `.hash`, and
  `.gnu.hash` are stored as `.raw` at the byte layer; the
  typed-section algebra's `Adapter.ofElfFile` decodes them on demand.
  There is no `bytes` field on ElfFile; raw bytes only exist at the
  parse/encode boundary. Section sizes are derived from `content`
  via `encodedSize` — no stored `sh_size` to go stale.

  Validity invariants (`IsValid`, `IsLoadable`, `IsFullyValid`) are
  decidable. Byte-layer mutating ops preserve `IsValid`.

  Architecture and invariant details: see `lean/STATUS.md` and
  `research/REWRITE-ABI.md`.
-/
module

public import Patchelf.Elf.Basic
public import Patchelf.Elf.Layout
public import Patchelf.Elf.Schemas
public meta import Lean

@[expose] public section

namespace Patchelf.Elf

open Layout
open Patchelf.Elf (ElfHeader ProgramHeader DynEntry DynTag Symbol Verneed
                     SysVHashTable GnuHashTable StringTable)

/-! ## SectionContent

    One inductive discriminating every section payload we model
    structurally at the byte layer.  `.raw` covers everything else:
    every unmodeled section (PROGBITS text/data, NOTE, REL/RELA,
    SYMTAB with no struct model, …) plus `.interp` (bytes) plus
    `.gnu.version_r` / SysV hash / GNU hash (typed materialization
    happens in the typed-section algebra via `Adapter.ofElfFile`,
    not at the byte layer — these sections are byte-verbatim
    through the byte-level encode/parse roundtrip).  `.nobits` is
    the tag for SHT_NOBITS (`.bss`) — no payload because those
    sections occupy zero file bytes. -/

inductive SectionContent
  /-- Any section type not modeled structurally.  Carries the ELF
      `sh_type` and a proof that it is not one of the five structural
      types (`SHT_NOBITS`, `SHT_STRTAB`, `SHT_DYNAMIC`, `SHT_DYNSYM`,
      `SHT_GNU_VERSYM`) that have dedicated constructors below.
      This constraint makes `typeContentMatchesB` vacuously true by
      construction — every `SectionContent` value is "correctly typed"
      without any external predicate. -/
  | raw      (type  : ShType)
             (hOk   : type.isStructural = false)
             (bytes : ByteArray)
  | strtab   (st : StringTable)
  | dynamic  (entries : Array DynEntry)
  | dynsym   (syms : Array Symbol)
  | versym   (entries : Array UInt16)
  /-- SHT_NOBITS section (`.bss`, `.tbss`).  `memSize` records the
      runtime allocation size from the original `sh_size` — not used
      for file encoding (NOBITS contributes 0 file bytes), but the
      shdr table's `sh_size` field needs this value so the loader
      knows how many zero-filled bytes to allocate at `sh_addr`. -/
  | nobits   (memSize : Nat)
  deriving Repr

namespace SectionContent

/-- The ELF `sh_type` of this content.  By construction, the type
    is always consistent with the constructor — no external predicate
    required. -/
def type : SectionContent → ShType
  | raw ty _ _  => ty
  | strtab _    => ShType.SHT_STRTAB
  | dynamic _   => ShType.SHT_DYNAMIC
  | dynsym _    => ShType.SHT_DYNSYM
  | versym _    => ShType.SHT_GNU_VERSYM
  | nobits _    => ShType.SHT_NOBITS

/-- Well-formedness of the content itself (payload-intrinsic). -/
def WellFormed : SectionContent → Prop
  | raw _ _ _          => True
  | strtab st          => st.WellFormed
  | dynamic entries    =>
      entries.back?.any (fun e => decide (e.tag = DynTag.null)) = true
  | dynsym _           => True
  | versym _           => True
  | nobits _           => True

instance : ∀ (c : SectionContent), Decidable c.WellFormed := by
  intro c
  cases c <;> unfold WellFormed <;> exact inferInstance

end SectionContent

/-! ## Section

    Section metadata + typed content. Name, type, flags, addr, link,
    info, addralign, entsize come directly from the ELF shdr.  `offset`
    is stored (parser fills, encoder validates, layout engine can
    rewrite).  Size is NOT stored — it's derived from `content` via
    `encodedSize`, which eliminates a staleness bug class by
    construction. -/

structure Section where
  name      : UInt32       -- shstrtab offset of section name
  flags     : UInt64
  addr      : VirtualAddr
  offset    : FileOffset
  link      : UInt32
  info      : UInt32
  addralign : Alignment
  entsize   : ByteSize
  content   : SectionContent
  deriving Repr

namespace Section

/-- The ELF `sh_type` of this section.  Computed from `content`
    via `SectionContent.type`; never stored separately.  This
    guarantees the type↔content invariant holds by construction. -/
@[inline] def type (s : Section) : ShType := s.content.type

/-- File-encoded byte length of a section's content.  Zero for NOBITS
    (no file bytes), `bs.size` for raw, etc.  -/
def encodedSize (s : Section) : Nat :=
  match s.content with
  | .raw _ _ bs     => bs.size
  | .strtab st      => st.bytes.size
  | .dynamic ds     => ds.size * Layout.dynEntrySize
  | .dynsym syms    => syms.size * Layout.symEntrySize
  | .versym vs      => vs.size * 2
  | .nobits _       => 0

/-- Shdr-table `sh_size` value: matches `encodedSize` for file-resident
    sections, but for NOBITS uses the declared memory allocation size
    (so the loader knows how many zero-filled bytes to allocate). -/
def shdrSize (s : Section) : Nat :=
  match s.content with
  | .nobits memSize => memSize
  | _               => s.encodedSize

end Section

/-! ## ElfFile

    No `bytes`.  No broken-out optional sections.  No `*ShdrIdx`. -/

structure ElfFile where
  header   : ElfHeader
  phdrs    : Array ProgramHeader
  sections : Array Section
  deriving Repr

namespace ElfFile

/-! ## Section lookup -/

/-- Linear scan: first index where predicate holds, or `none`.
    Takes the section array directly so rewrites on `e.sections`
    transparently propagate. -/
def firstIdxWhereIn (sections : Array Section) (p : Section → Bool) :
    Option Nat :=
  go 0
where go (i : Nat) : Option Nat :=
  if h : i < sections.size then
    if p (sections[i]'h) then some i
    else go (i + 1)
  else none
  decreasing_by exact Nat.sub_lt_sub_left h (Nat.lt_succ_self i)

/-- ElfFile convenience: first section index matching predicate. -/
def firstIdxWhere (e : ElfFile) (p : Section → Bool) : Option Nat :=
  firstIdxWhereIn e.sections p

/-- Index of the unique section of the given `SHT_*` type, if any.
    If multiple sections share this type, returns the first one.
    Validity clause `sectionsAtDistinctTypes` rules out the
    "multiple" case for structural types. -/
def findUniqueTypeIdx (e : ElfFile) (ty : ShType) : Option Nat :=
  firstIdxWhereIn e.sections (fun s => s.type = ty)

/-- `.shstrtab` contents (if the shstrndx points at a strtab). -/
def shstrtab (e : ElfFile) : Option StringTable :=
  if h : e.header.shstrndx.toNat < e.sections.size then
    match (e.sections[e.header.shstrndx.toNat]'h).content with
    | .strtab st => some st
    | _          => none
  else none

/-- Section index by name (looked up via shstrtab). Used for named
    sections whose `SHT_*` type is not unique: `.dynstr` (STRTAB),
    `.interp` (PROGBITS).  For unique-by-type sections use
    `findUniqueTypeIdx` directly. -/
def findIdxByName (e : ElfFile) (name : ByteArray) : Option Nat :=
  match e.shstrtab with
  | none    => none
  | some st =>
      firstIdxWhereIn e.sections fun s =>
        match st.lookup s.name.toNat with
        | some b => b = name
        | none   => false

/-- Shorthand indices for the 6 structural + 2 named broken-out
    sections. -/
def dynamicIdx  (e : ElfFile) : Option Nat := e.findUniqueTypeIdx ShType.SHT_DYNAMIC
def dynsymIdx   (e : ElfFile) : Option Nat := e.findUniqueTypeIdx ShType.SHT_DYNSYM
def sysvHashIdx (e : ElfFile) : Option Nat := e.findUniqueTypeIdx ShType.SHT_HASH
def verneedIdx  (e : ElfFile) : Option Nat := e.findUniqueTypeIdx ShType.SHT_GNU_VERNEED
def versymIdx   (e : ElfFile) : Option Nat := e.findUniqueTypeIdx ShType.SHT_GNU_VERSYM
def gnuHashIdx  (e : ElfFile) : Option Nat := e.findUniqueTypeIdx ShType.SHT_GNU_HASH
def dynstrIdx   (e : ElfFile) : Option Nat := e.findIdxByName ".dynstr".toUTF8
def interpIdx   (e : ElfFile) : Option Nat := e.findIdxByName ".interp".toUTF8

/-! ## Content accessors -/

def contentAt (e : ElfFile) (i : Option Nat) : Option SectionContent :=
  i.bind fun j =>
    if h : j < e.sections.size then some ((e.sections[j]'h).content)
    else none

/-- Emit a content accessor for single-field constructors. -/
local elab "section_content_accessor"
    name:ident idxName:ident ctor:ident ":" ty:term : command => do
  let cmd ← `(command|
    def $name (e : ElfFile) : Option $ty :=
      match e.contentAt e.$idxName:ident with
      | some (.$ctor x) => some x
      | _               => none)
  Lean.Elab.Command.elabCommand cmd

/-- Emit a content accessor for the `.raw _ _ bytes` constructor
    (three-argument form with type + proof + bytes). -/
local elab "section_content_accessor_raw"
    name:ident idxName:ident : command => do
  let cmd ← `(command|
    def $name (e : ElfFile) : Option ByteArray :=
      match e.contentAt e.$idxName:ident with
      | some (.raw _ _ bs) => some bs
      | _                  => none)
  Lean.Elab.Command.elabCommand cmd

section_content_accessor dynamic  dynamicIdx  dynamic  : Array DynEntry
section_content_accessor dynstr   dynstrIdx   strtab   : StringTable
section_content_accessor dynsym   dynsymIdx   dynsym   : Array Symbol
section_content_accessor_raw interp   interpIdx
section_content_accessor versym   versymIdx   versym   : Array UInt16
-- verneed / sysvHash / gnuHash are stored as `.raw` at the byte
-- layer (no typed materialization).  The typed-section algebra's
-- `Adapter.ofElfFile` decodes them on demand.
section_content_accessor_raw verneedRaw  verneedIdx
section_content_accessor_raw sysvHashRaw sysvHashIdx
section_content_accessor_raw gnuHashRaw  gnuHashIdx

/-- `e.dynamic = some dyn` exposes the witnessing index, its bound, and
    the section content there.  Packages the inline `unfold dynamic` /
    `contentAt` case-analysis that several proofs (`syncDtStrszInFile`,
    `syncDtAddrTagsInFile` accessors) would otherwise repeat. -/
theorem dynamic_eq_some_elim (e : ElfFile) (dyn : Array DynEntry)
    (hDyn : e.dynamic = some dyn) :
    ∃ iDyn, e.dynamicIdx = some iDyn ∧ ∃ (h : iDyn < e.sections.size),
      (e.sections[iDyn]'h).content = .dynamic dyn := by
  unfold ElfFile.dynamic at hDyn
  cases hIdx : e.dynamicIdx with
  | none =>
    rw [hIdx] at hDyn
    simp only [ElfFile.contentAt, Option.bind_none] at hDyn
    exact absurd hDyn (by simp)
  | some iDyn =>
    rw [hIdx] at hDyn
    unfold ElfFile.contentAt at hDyn
    simp only [Option.bind_some] at hDyn
    by_cases hLt : iDyn < e.sections.size
    · rw [dif_pos hLt] at hDyn
      generalize hC : (e.sections[iDyn]'hLt).content = c at hDyn
      cases c with
      | dynamic dyn' => simp at hDyn; exact ⟨iDyn, rfl, hLt, by rw [hC, hDyn]⟩
      | raw _ => simp at hDyn
      | strtab _ => simp at hDyn
      | dynsym _ => simp at hDyn
      | versym _ => simp at hDyn
      | nobits _ => simp at hDyn
    · rw [dif_neg hLt] at hDyn; simp at hDyn

/-! ## IsValid -/

/-- Header fields match structural counts.  No reference to `bytes`. -/
def headerCountsConsistent (e : ElfFile) : Prop :=
  e.header.phnum.toNat = e.phdrs.size ∧
  e.header.shnum.toNat = e.sections.size ∧
  e.header.phentsize.toNat = Layout.phdrSize ∧
  e.header.shentsize.toNat = Layout.shdrSize ∧
  e.header.shstrndx.toNat < e.sections.size

instance (e : ElfFile) : Decidable e.headerCountsConsistent := by
  unfold headerCountsConsistent; exact inferInstance

/-- `sections[0]` is SHT_NULL (standard ELF convention). -/
def sectionsWellFormed (e : ElfFile) : Prop :=
  ∀ h : 0 < e.sections.size, (e.sections[0]'h).type = ShType.SHT_NULL

instance (e : ElfFile) : Decidable e.sectionsWellFormed := by
  unfold sectionsWellFormed; exact inferInstance

/-- Section-level strtab wellformedness as a Bool (for decidability
    via `Array.all`).  -/
def Section.strtabWellFormedB (s : Section) : Bool :=
  match s.content with
  | .strtab st => decide st.WellFormed
  | _          => true

/-- Every `strtab`-content section is WellFormed.  This subsumes
    a separate `.shstrtab`/`.dynstr` null-termination clause: the
    `WellFormed` field already covers it. -/
def strtabsWellFormed (e : ElfFile) : Prop :=
  e.sections.all Section.strtabWellFormedB = true

instance (e : ElfFile) : Decidable e.strtabsWellFormed := by
  unfold strtabsWellFormed; exact inferInstance

/-- Content-level well-formedness as a Bool. -/
def Section.contentWellFormedB (s : Section) : Bool :=
  decide s.content.WellFormed

/-- Content-level well-formedness across all sections. -/
def sectionsContentWellFormed (e : ElfFile) : Prop :=
  e.sections.all Section.contentWellFormedB = true

instance (e : ElfFile) : Decidable e.sectionsContentWellFormed := by
  unfold sectionsContentWellFormed; exact inferInstance

-- `typeContentMatchesB` and `sectionsTypeContentMatch` are deleted.
-- `SectionContent.raw` now carries `hOk : type.isStructural = false`,
-- so every `Section.type = Section.content.type` is correct by
-- construction.  The `typesMatch` field in `EncodePreconditions` is
-- gone; `section_decode_encode` needs no external type-match predicate.

/-- `.dynamic` (if any) terminates in DT_NULL with no earlier null
    entry.  Independent of `.dynstr`'s presence — required for the
    `decodeDynamic` forward roundtrip (DT_NULL early-exit must coincide
    with array end). -/
def dynamicTerminated (e : ElfFile) : Prop :=
  ∀ dyn, e.dynamic = some dyn →
    ∃ (hSize : 0 < dyn.size),
      (dyn[dyn.size - 1]'(by omega)).tag = DynTag.null ∧
      (∀ (i : Nat) (h : i < dyn.size),
         (dyn[i]'h).tag = DynTag.null → i = dyn.size - 1)

instance (e : ElfFile) : Decidable e.dynamicTerminated := by
  unfold dynamicTerminated
  match hDyn : e.dynamic with
  | none     => exact .isTrue (fun _ hEq => by cases hEq)
  | some dyn =>
    by_cases hSize : 0 < dyn.size
    · refine decidable_of_iff
        ((dyn[dyn.size - 1]'(by omega)).tag = DynTag.null ∧
         (∀ (i : Nat) (h : i < dyn.size),
           (dyn[i]'h).tag = DynTag.null → i = dyn.size - 1)) ?_
      refine ⟨fun ⟨h1, h2⟩ dyn' hD' => ?_, fun h => ?_⟩
      · cases hD'; exact ⟨hSize, h1, h2⟩
      · obtain ⟨_, h1, h2⟩ := h dyn rfl
        exact ⟨h1, h2⟩
    · exact .isFalse fun h => hSize (h dyn rfl).1

/-- `.dynamic` (if any) has every stringref entry's value in-bounds of
    `.dynstr`. -/
def dynamicStringRefsValid (e : ElfFile) : Prop :=
  ∀ dyn ds, e.dynamic = some dyn → e.dynstr = some ds →
    ∀ (i : Nat) (h : i < dyn.size), (dyn[i]'h).isStringRef = true →
       (dyn[i]'h).value.toNat < ds.bytes.size

instance (e : ElfFile) : Decidable e.dynamicStringRefsValid := by
  unfold dynamicStringRefsValid
  match hDyn : e.dynamic with
  | none     => exact .isTrue (fun _ _ hEq => by cases hEq)
  | some dyn =>
    match hDs : e.dynstr with
    | none    => exact .isTrue (fun _ _ _ hEq => by cases hEq)
    | some ds =>
        refine decidable_of_iff
          (∀ (i : Nat) (h : i < dyn.size), (dyn[i]'h).isStringRef = true →
             (dyn[i]'h).value.toNat < ds.bytes.size) ?_
        refine ⟨fun h dyn' ds' hD' hS' => ?_, fun h => h dyn ds rfl rfl⟩
        cases hD'; cases hS'; exact h

/-- Combined predicate kept for callers; bundles termination and
    stringref validity. -/
def dynamicWellFormed (e : ElfFile) : Prop :=
  e.dynamicTerminated ∧ e.dynamicStringRefsValid

instance (e : ElfFile) : Decidable e.dynamicWellFormed := by
  unfold dynamicWellFormed; exact inferInstance

/-- Every `.dynsym` entry's `st_name` offset is in-bounds of `.dynstr`. -/
def dynsymNamesInBounds (e : ElfFile) : Prop :=
  ∀ syms ds, e.dynsym = some syms → e.dynstr = some ds →
    ∀ (i : Nat) (h : i < syms.size), (syms[i]'h).st_name.toNat < ds.bytes.size

instance (e : ElfFile) : Decidable e.dynsymNamesInBounds := by
  unfold dynsymNamesInBounds
  match hSyms : e.dynsym with
  | none      => exact .isTrue (fun _ _ hEq => by cases hEq)
  | some syms =>
    match hDs : e.dynstr with
    | none    => exact .isTrue (fun _ _ _ hEq => by cases hEq)
    | some ds =>
        refine decidable_of_iff
          (∀ (i : Nat) (h : i < syms.size), (syms[i]'h).st_name.toNat < ds.bytes.size) ?_
        refine ⟨fun h syms' ds' hS' hD' => ?_, fun h => h syms ds rfl rfl⟩
        cases hS'; cases hD'; exact h

/-- Predicate: at most one section in `sections` has type `ty`. -/
def typeUniqueAt (e : ElfFile) (ty : ShType) : Prop :=
  ∀ (i : Nat) (hi : i < e.sections.size)
    (j : Nat) (hj : j < e.sections.size),
      (e.sections[i]'hi).type = ty →
      (e.sections[j]'hj).type = ty → i = j

instance (e : ElfFile) (ty : ShType) : Decidable (e.typeUniqueAt ty) := by
  unfold typeUniqueAt; exact inferInstance

/-- If section `i` is the unique section with type `ty`, then
    `findUniqueTypeIdx e ty = some i`.  Used to bridge per-section
    properties to bundle-level `e.dynamic` etc. -/
theorem findUniqueTypeIdx_eq_some (e : ElfFile) (ty : ShType)
    (i : Nat) (hi : i < e.sections.size)
    (hType : (e.sections[i]'hi).type = ty)
    (hUnique : e.typeUniqueAt ty) :
    e.findUniqueTypeIdx ty = some i := by
  unfold findUniqueTypeIdx firstIdxWhereIn
  -- firstIdxWhereIn.go starts at 0; walk to i, all earlier indices
  -- fail the predicate (uniqueness), index i succeeds.
  suffices h : ∀ (k : Nat) (hk : k ≤ i),
      firstIdxWhereIn.go e.sections (fun s => decide (s.type = ty)) k = some i by
    exact h 0 (Nat.zero_le _)
  intro k hk
  -- Induction on `i - k`.
  let n := i - k
  have hn : i - k = n := rfl
  clear_value n
  induction n generalizing k with
  | zero =>
    have hkEq : k = i := by omega
    rw [hkEq]
    unfold firstIdxWhereIn.go
    rw [dif_pos hi]
    rw [if_pos (by show decide ((e.sections[i]'hi).type = ty) = true; rw [hType, decide_eq_true_eq])]
  | succ m ih =>
    have hkLt : k < i := by omega
    have hkBound : k < e.sections.size := by omega
    unfold firstIdxWhereIn.go
    rw [dif_pos hkBound]
    have hKType : (e.sections[k]'hkBound).type ≠ ty := by
      intro hEq
      have := hUnique k hkBound i hi hEq hType
      omega
    rw [if_neg]
    · have hnNext : i - (k + 1) = m := by omega
      have hkNext : k + 1 ≤ i := by omega
      exact ih (k + 1) hkNext hnNext
    · show ¬ decide ((e.sections[k]'hkBound).type = ty) = true
      simp [hKType]

/-- The structural types we rely on being unique actually are. -/
def sectionsAtDistinctTypes (e : ElfFile) : Prop :=
  e.typeUniqueAt ShType.SHT_DYNAMIC ∧
  e.typeUniqueAt ShType.SHT_DYNSYM ∧
  e.typeUniqueAt ShType.SHT_HASH ∧
  e.typeUniqueAt ShType.SHT_GNU_HASH ∧
  e.typeUniqueAt ShType.SHT_GNU_VERNEED ∧
  e.typeUniqueAt ShType.SHT_GNU_VERSYM

instance (e : ElfFile) : Decidable e.sectionsAtDistinctTypes := by
  unfold sectionsAtDistinctTypes; exact inferInstance

/-- Predicate: at most one section has this name (via shstrtab). -/
def nameUniqueAt (e : ElfFile) (st : StringTable)
    (nm : ByteArray) : Prop :=
  ∀ (i : Nat) (hi : i < e.sections.size)
    (j : Nat) (hj : j < e.sections.size),
      st.lookup (e.sections[i]'hi).name.toNat = some nm →
      st.lookup (e.sections[j]'hj).name.toNat = some nm → i = j

instance (e : ElfFile) (st : StringTable) (nm : ByteArray) :
    Decidable (e.nameUniqueAt st nm) := by
  unfold nameUniqueAt; exact inferInstance

/-- Named sections that share a non-unique `SHT_*` type (STRTAB is the
    only such type in our model) resolve uniquely by name. -/
def namedSectionsUnique (e : ElfFile) : Prop :=
  match e.shstrtab with
  | none    => True
  | some st =>
      e.nameUniqueAt st ".dynstr".toUTF8 ∧
      e.nameUniqueAt st ".interp".toUTF8

instance (e : ElfFile) : Decidable e.namedSectionsUnique := by
  unfold namedSectionsUnique
  split <;> exact inferInstance

/-- Eight named fields, none referencing `bytes` (raw bytes only
    exist at the parse/encode boundary). -/
structure IsValid (e : ElfFile) : Prop where
  header_counts   : headerCountsConsistent e
  sections_wf     : sectionsWellFormed e
  strtabs_wf      : strtabsWellFormed e
  dynamic_wf      : dynamicWellFormed e
  dynsym_wf       : dynsymNamesInBounds e
  content_wf      : sectionsContentWellFormed e
  types_distinct  : sectionsAtDistinctTypes e
  names_unique    : namedSectionsUnique e

instance (e : ElfFile) : Decidable e.IsValid :=
  decidable_of_iff
    (headerCountsConsistent e ∧ sectionsWellFormed e ∧
     strtabsWellFormed e ∧ dynamicWellFormed e ∧
     dynsymNamesInBounds e ∧ sectionsContentWellFormed e ∧
     sectionsAtDistinctTypes e ∧ namedSectionsUnique e)
    ⟨fun ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ =>
        { header_counts := h1, sections_wf := h2, strtabs_wf := h3,
          dynamic_wf := h4, dynsym_wf := h5, content_wf := h6,
          types_distinct := h7, names_unique := h8 },
     fun h => ⟨h.header_counts, h.sections_wf, h.strtabs_wf,
               h.dynamic_wf, h.dynsym_wf, h.content_wf,
               h.types_distinct, h.names_unique⟩⟩

/-! ## IsLoadable

    Loader-level coherence on top of `IsValid`: non-overlapping
    sections + PT_INTERP/PT_DYNAMIC offset agreement + PT_LOAD
    alignment congruence.  No `*SlotsFit` clauses are needed
    because `ElfFile` carries no `bytes` field that could
    overflow. -/

end ElfFile

/-- Two half-open intervals `[a₁, a₂)` and `[b₁, b₂)` over the
    natural numbers are disjoint iff one ends at or before the other
    begins.  The OR-form is the shape that composes with byte-level
    splice-preservation lemmas: each disjunct says "this region is
    entirely to the left/right of that one", which is the precondition
    of `splice_disjoint_*` lemmas in `Splice.lean`.

    Used as the primitive shared by all 7 region-pair disjointness
    predicates in the splice-region invariant family. -/
def IntervalDisjoint (a₁ a₂ b₁ b₂ : Nat) : Prop :=
  a₂ ≤ b₁ ∨ b₂ ≤ a₁

instance : Decidable (IntervalDisjoint a₁ a₂ b₁ b₂) := by
  unfold IntervalDisjoint; exact inferInstance

namespace ElfFile

/-- Two sections' file byte ranges are disjoint, or at least one of
    them contributes zero file bytes. -/
def sectionsNonOverlapping (e : ElfFile) : Prop :=
  ∀ (i : Nat) (hi : i < e.sections.size)
    (j : Nat) (hj : j < e.sections.size), i ≠ j →
    let si := e.sections[i]'hi
    let sj := e.sections[j]'hj
    si.type = ShType.SHT_NOBITS ∨ sj.type = ShType.SHT_NOBITS ∨
    si.type = ShType.SHT_NULL   ∨ sj.type = ShType.SHT_NULL   ∨
    IntervalDisjoint
      si.offset.val (si.offset.val + si.encodedSize)
      sj.offset.val (sj.offset.val + sj.encodedSize)

instance (e : ElfFile) : Decidable e.sectionsNonOverlapping := by
  unfold sectionsNonOverlapping; exact inferInstance

/-- PT_INTERP phdr.offset agrees with `.interp` section's offset. -/
def ptInterpAgreement (e : ElfFile) : Prop :=
  match e.interpIdx with
  | none    => True
  | some iS =>
      ∀ h : iS < e.sections.size,
      ∀ (iPh : Nat) (hPh : iPh < e.phdrs.size),
        (e.phdrs[iPh]'hPh).type = PhType.PT_INTERP →
        (e.phdrs[iPh]'hPh).offset = (e.sections[iS]'h).offset

instance (e : ElfFile) : Decidable e.ptInterpAgreement := by
  unfold ptInterpAgreement; split <;> exact inferInstance

/-- PT_DYNAMIC phdr.offset agrees with `.dynamic` section's offset. -/
def ptDynamicAgreement (e : ElfFile) : Prop :=
  match e.dynamicIdx with
  | none    => True
  | some iS =>
      ∀ h : iS < e.sections.size,
      ∀ (iPh : Nat) (hPh : iPh < e.phdrs.size),
        (e.phdrs[iPh]'hPh).type = PhType.PT_DYNAMIC →
        (e.phdrs[iPh]'hPh).offset = (e.sections[iS]'h).offset

instance (e : ElfFile) : Decidable e.ptDynamicAgreement := by
  unfold ptDynamicAgreement; split <;> exact inferInstance

/-- PT_LOAD: `p_vaddr ≡ p_offset  (mod p_align)`. -/
def segmentCongruence (e : ElfFile) : Prop :=
  ∀ (i : Nat) (h : i < e.phdrs.size),
    (e.phdrs[i]'h).type = PhType.PT_LOAD →
    (e.phdrs[i]'h).align.val ≤ 1 ∨
    (e.phdrs[i]'h).offset.val % (e.phdrs[i]'h).align.val
      = (e.phdrs[i]'h).vaddr.val % (e.phdrs[i]'h).align.val

instance (e : ElfFile) : Decidable e.segmentCongruence := by
  unfold segmentCongruence; exact inferInstance

/-! ## Splice-region disjointness

    The encoder writes 4 kinds of regions: ELF header at `[0, ehdrSize)`;
    program-header table at `[phoff, phoff + phnum * phdrSize)`;
    section-header table at `[shoff, shoff + shnum * shdrSize)`;
    each non-NOBITS, non-NULL section at `[s.offset, s.offset + s.encodedSize)`.
    For `parse (encode e) = .ok e`, these regions must be pairwise
    disjoint — otherwise a later splice clobbers an earlier one.

    `sectionsNonOverlapping` covers section-section pairs.  This
    predicate covers the (header, phdr-table), (header, shdr-table),
    (phdr-table, shdr-table), (header, section-i), (phdr-table,
    section-i), (shdr-table, section-i) pairs. -/

/-- Header byte range and the phdr table don't overlap. -/
def headerPhdrDisjoint (e : ElfFile) : Prop :=
  IntervalDisjoint
    0 Layout.ehdrSize
    e.header.phoff.val (e.header.phoff.val + e.phdrs.size * Layout.phdrSize)

instance (e : ElfFile) : Decidable e.headerPhdrDisjoint := by
  unfold headerPhdrDisjoint; exact inferInstance

/-- Header byte range and the shdr table don't overlap. -/
def headerShdrDisjoint (e : ElfFile) : Prop :=
  IntervalDisjoint
    0 Layout.ehdrSize
    e.header.shoff.val (e.header.shoff.val + e.sections.size * Layout.shdrSize)

instance (e : ElfFile) : Decidable e.headerShdrDisjoint := by
  unfold headerShdrDisjoint; exact inferInstance

/-- Phdr table and shdr table don't overlap. -/
def phdrShdrDisjoint (e : ElfFile) : Prop :=
  IntervalDisjoint
    e.header.phoff.val (e.header.phoff.val + e.phdrs.size * Layout.phdrSize)
    e.header.shoff.val (e.header.shoff.val + e.sections.size * Layout.shdrSize)

instance (e : ElfFile) : Decidable e.phdrShdrDisjoint := by
  unfold phdrShdrDisjoint; exact inferInstance

/-- Header byte range and section i don't overlap (skipping NOBITS/NULL). -/
def headerSectionDisjoint (e : ElfFile) : Prop :=
  ∀ (i : Nat) (hi : i < e.sections.size),
    let s := e.sections[i]'hi
    s.type = ShType.SHT_NOBITS ∨ s.type = ShType.SHT_NULL ∨
    IntervalDisjoint
      0 Layout.ehdrSize
      s.offset.val (s.offset.val + s.encodedSize)

instance (e : ElfFile) : Decidable e.headerSectionDisjoint := by
  unfold headerSectionDisjoint; exact inferInstance

/-- Phdr table and section i don't overlap. -/
def phdrSectionDisjoint (e : ElfFile) : Prop :=
  ∀ (i : Nat) (hi : i < e.sections.size),
    let s := e.sections[i]'hi
    s.type = ShType.SHT_NOBITS ∨ s.type = ShType.SHT_NULL ∨
    IntervalDisjoint
      e.header.phoff.val (e.header.phoff.val + e.phdrs.size * Layout.phdrSize)
      s.offset.val (s.offset.val + s.encodedSize)

instance (e : ElfFile) : Decidable e.phdrSectionDisjoint := by
  unfold phdrSectionDisjoint; exact inferInstance

/-- Shdr table and section i don't overlap. -/
def shdrSectionDisjoint (e : ElfFile) : Prop :=
  ∀ (i : Nat) (hi : i < e.sections.size),
    let s := e.sections[i]'hi
    s.type = ShType.SHT_NOBITS ∨ s.type = ShType.SHT_NULL ∨
    IntervalDisjoint
      e.header.shoff.val (e.header.shoff.val + e.sections.size * Layout.shdrSize)
      s.offset.val (s.offset.val + s.encodedSize)

instance (e : ElfFile) : Decidable e.shdrSectionDisjoint := by
  unfold shdrSectionDisjoint; exact inferInstance

/-- All splice regions are pairwise disjoint.  Bundles
    `sectionsNonOverlapping` (covered by `IsLoadable`) with the six
    region-pair predicates above.

    This is the structural backbone for unconditional Tier D: under
    `spliceRegionsDisjoint`, every byte the encoder splices into the
    output buffer is at a region uniquely owned by that splice, so no
    later splice can clobber it. -/
structure spliceRegionsDisjoint (e : ElfFile) : Prop where
  sections_disjoint   : e.sectionsNonOverlapping
  hdr_phdr_disjoint   : e.headerPhdrDisjoint
  hdr_shdr_disjoint   : e.headerShdrDisjoint
  phdr_shdr_disjoint  : e.phdrShdrDisjoint
  hdr_sec_disjoint    : e.headerSectionDisjoint
  phdr_sec_disjoint   : e.phdrSectionDisjoint
  shdr_sec_disjoint   : e.shdrSectionDisjoint

instance (e : ElfFile) : Decidable e.spliceRegionsDisjoint :=
  decidable_of_iff
    (e.sectionsNonOverlapping ∧ e.headerPhdrDisjoint ∧ e.headerShdrDisjoint ∧
     e.phdrShdrDisjoint ∧ e.headerSectionDisjoint ∧ e.phdrSectionDisjoint ∧
     e.shdrSectionDisjoint)
    ⟨fun ⟨h1, h2, h3, h4, h5, h6, h7⟩ =>
        { sections_disjoint := h1, hdr_phdr_disjoint := h2,
          hdr_shdr_disjoint := h3, phdr_shdr_disjoint := h4,
          hdr_sec_disjoint := h5, phdr_sec_disjoint := h6,
          shdr_sec_disjoint := h7 },
     fun h => ⟨h.sections_disjoint, h.hdr_phdr_disjoint, h.hdr_shdr_disjoint,
               h.phdr_shdr_disjoint, h.hdr_sec_disjoint, h.phdr_sec_disjoint,
               h.shdr_sec_disjoint⟩⟩

structure IsLoadable (e : ElfFile) : Prop extends IsValid e where
  sections_nonoverlapping : sectionsNonOverlapping e
  pt_interp_agrees        : ptInterpAgreement e
  pt_dynamic_agrees       : ptDynamicAgreement e
  segment_congruent       : segmentCongruence e

instance (e : ElfFile) : Decidable e.IsLoadable :=
  decidable_of_iff
    (e.IsValid ∧ sectionsNonOverlapping e ∧
     ptInterpAgreement e ∧ ptDynamicAgreement e ∧ segmentCongruence e)
    ⟨fun ⟨hv, h1, h2, h3, h4⟩ =>
        { toIsValid := hv, sections_nonoverlapping := h1,
          pt_interp_agrees := h2, pt_dynamic_agrees := h3,
          segment_congruent := h4 },
     fun h => ⟨h.toIsValid, h.sections_nonoverlapping,
               h.pt_interp_agrees, h.pt_dynamic_agrees,
               h.segment_congruent⟩⟩

/-! ## IsFullyValid

    DT_* dynamic entries reference section virtual addresses that
    actually match the sections they point to.  Structural
    property over the typed section index. -/

def dynAddressCoherentForTag (e : ElfFile) (tag : DynTag)
    (sectionIdx : Option Nat) : Prop :=
  match sectionIdx with
  | none    => True
  | some iS =>
      ∀ h : iS < e.sections.size,
      ∀ dyn, e.dynamic = some dyn →
      ∀ (i : Nat) (hi : i < dyn.size),
        (dyn[i]'hi).tag = tag →
        (dyn[i]'hi).value.toNat = (e.sections[iS]'h).addr.val

instance (e : ElfFile) (tag : DynTag) (idx : Option Nat) :
    Decidable (dynAddressCoherentForTag e tag idx) := by
  unfold dynAddressCoherentForTag
  match idx with
  | none    => exact inferInstance
  | some iS =>
    match hDyn : e.dynamic with
    | none     =>
        refine .isTrue ?_
        intro _ dyn' hEq
        cases hEq
    | some dyn =>
        refine decidable_of_iff
          (∀ (h : iS < e.sections.size) (i : Nat) (hi : i < dyn.size),
            (dyn[i]'hi).tag = tag →
            (dyn[i]'hi).value.toNat = (e.sections[iS]'h).addr.val) ?_
        refine ⟨fun h h' dyn' hD' => ?_, fun h h' => h h' dyn rfl⟩
        cases hD'; exact h h'

/-- DT_STRSZ matches `.dynstr.bytes.size`.  Cannot go stale because
    both sides derive from the same section's content. -/
def dynStrszCoherent (e : ElfFile) : Prop :=
  ∀ dyn ds, e.dynamic = some dyn → e.dynstr = some ds →
    ∀ (i : Nat) (h : i < dyn.size), (dyn[i]'h).tag = DynTag.strsz →
      (dyn[i]'h).value.toNat = ds.bytes.size

instance (e : ElfFile) : Decidable e.dynStrszCoherent := by
  unfold dynStrszCoherent
  match hDyn : e.dynamic with
  | none     => exact .isTrue (fun _ _ hEq => by cases hEq)
  | some dyn =>
    match hDs : e.dynstr with
    | none    => exact .isTrue (fun _ _ _ hEq => by cases hEq)
    | some ds =>
        refine decidable_of_iff
          (∀ (i : Nat) (h : i < dyn.size), (dyn[i]'h).tag = DynTag.strsz →
            (dyn[i]'h).value.toNat = ds.bytes.size) ?_
        refine ⟨fun h dyn' ds' hD' hS' => ?_, fun h => h dyn ds rfl rfl⟩
        cases hD'; cases hS'; exact h

/-- `dynStrszCoherent` reads only the `.dynamic` and `.dynstr` accessors,
    so any transformation that preserves both preserves coherence. -/
theorem dynStrszCoherent_of_accessors_eq (e e' : ElfFile)
    (hDyn : e'.dynamic = e.dynamic) (hDs : e'.dynstr = e.dynstr)
    (hCoh : e.dynStrszCoherent) : e'.dynStrszCoherent := by
  intro dyn ds hD hS i hi hT
  rw [hDyn] at hD; rw [hDs] at hS
  exact hCoh dyn ds hD hS i hi hT

structure dynamicAddressCoherent (e : ElfFile) : Prop where
  strtab_addr  : dynAddressCoherentForTag e DynTag.strtab  e.dynstrIdx
  symtab_addr  : dynAddressCoherentForTag e DynTag.symtab  e.dynsymIdx
  hash_addr    : dynAddressCoherentForTag e DynTag.hash    e.sysvHashIdx
  gnuHash_addr : dynAddressCoherentForTag e DynTag.gnuHash e.gnuHashIdx
  verneed_addr : dynAddressCoherentForTag e DynTag.verneed e.verneedIdx
  strsz_size   : dynStrszCoherent e

instance (e : ElfFile) : Decidable e.dynamicAddressCoherent :=
  decidable_of_iff
    (dynAddressCoherentForTag e DynTag.strtab  e.dynstrIdx ∧
     dynAddressCoherentForTag e DynTag.symtab  e.dynsymIdx ∧
     dynAddressCoherentForTag e DynTag.hash    e.sysvHashIdx ∧
     dynAddressCoherentForTag e DynTag.gnuHash e.gnuHashIdx ∧
     dynAddressCoherentForTag e DynTag.verneed e.verneedIdx ∧
     dynStrszCoherent e)
    ⟨fun ⟨h1, h2, h3, h4, h5, h6⟩ =>
        { strtab_addr := h1, symtab_addr := h2, hash_addr := h3,
          gnuHash_addr := h4, verneed_addr := h5, strsz_size := h6 },
     fun h => ⟨h.strtab_addr, h.symtab_addr, h.hash_addr,
               h.gnuHash_addr, h.verneed_addr, h.strsz_size⟩⟩

structure IsFullyValid (e : ElfFile) : Prop extends IsLoadable e where
  dyn_addrs_coherent : dynamicAddressCoherent e

instance (e : ElfFile) : Decidable e.IsFullyValid :=
  decidable_of_iff
    (e.IsLoadable ∧ e.dynamicAddressCoherent)
    ⟨fun ⟨hl, hd⟩ => { toIsLoadable := hl, dyn_addrs_coherent := hd },
     fun h => ⟨h.toIsLoadable, h.dyn_addrs_coherent⟩⟩

/-! ## PT_LOAD coverage

    The kernel's `load_elf_binary` mmaps each PT_LOAD segment from
    `[p_offset, p_offset + p_filesz)`.  For a section to be readable
    at runtime, its file range must be inside *some* PT_LOAD's file
    range — but ONLY for sections marked SHF_ALLOC.  Non-allocatable
    sections (`.symtab`, `.strtab`, `.shstrtab`, `.comment`,
    `.debug_*`) are tooling-only and never mmaped at exec; they live
    outside every PT_LOAD by design.  `layoutForEncoding`'s reflow
    may move SHF_ALLOC sections out of any PT_LOAD's window — that
    produces structurally well-formed bytes but a binary that
    SIGSEGVs at exec.  This predicate detects that case. -/

/-- SHF_ALLOC: section occupies memory at runtime. -/
def SHF_ALLOC : UInt64 := 0x2

/-- One section's file range is inside some PT_LOAD's file range,
    OR the section contributes no file bytes (NOBITS / NULL),
    OR the section isn't SHF_ALLOC (so the kernel never mmaps it). -/
def sectionInSomePtLoad (e : ElfFile) (i : Nat) (h : i < e.sections.size) : Prop :=
  let s := e.sections[i]'h
  s.type = ShType.SHT_NOBITS ∨ s.type = ShType.SHT_NULL ∨
  s.flags &&& SHF_ALLOC = 0 ∨
  ∃ (j : Nat) (hj : j < e.phdrs.size),
    let ph := e.phdrs[j]'hj
    ph.type = PhType.PT_LOAD ∧
    ph.offset.val ≤ s.offset.val ∧
    s.offset.val + s.encodedSize ≤ ph.offset.val + ph.filesz.val

instance (e : ElfFile) (i : Nat) (h : i < e.sections.size) :
    Decidable (sectionInSomePtLoad e i h) := by
  unfold sectionInSomePtLoad; exact inferInstance

/-- Every SHF_ALLOC section's file range is inside some PT_LOAD's
    file range.  This is the missing clause that
    `layoutForEncoding` violates on real binaries. -/
def sectionFileInSomePtLoad (e : ElfFile) : Prop :=
  ∀ (i : Nat) (h : i < e.sections.size), sectionInSomePtLoad e i h

instance (e : ElfFile) : Decidable e.sectionFileInSomePtLoad := by
  unfold sectionFileInSomePtLoad; exact inferInstance

end ElfFile
end Patchelf.Elf
