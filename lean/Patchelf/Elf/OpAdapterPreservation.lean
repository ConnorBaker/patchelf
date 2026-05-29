/-
  Op-level adapter preservation (ROADMAP §5.1).

  After the `Adapter.toElfFile` un-bundling refactor, each typed op's
  byte-level effect through the adapter is characterized by a
  `toElfFile_<op>_eq` commutation lemma: the byte-layer output of
  `toElfFile template (op typed)` equals a small, explicit edit of
  `toElfFile template typed` (the no-op adapter output).  For
  section-trivial ops these commutation lemmas hold by `rfl` (the whole
  point of the refactor); preservation corollaries then transport
  `IsValid` / `IsLoadable` clause-by-clause.

  Tier 1 (header/phdr-only): `setOsAbi`, `modifyExecstack`.  The adapter
  output's `sections` are definitionally those of the no-op output, so
  every section-driven invariant transports immediately, and the changed
  header/phdr fields (`osAbi`, PT_GNU_STACK `flags`) aren't read by any
  `IsValid`/`IsLoadable` clause.

  Higher tiers (same-size `.dynamic` rewrites; dynstr-growing ops) are
  tracked in ROADMAP §5.1 — they require reasoning about
  `patchDynamicEntries`'s output size and, for growing ops, the full
  `growEOFWith` layout pass (the §1.2 `_preserves_loadable` ladder).
-/
module

public import Patchelf.Elf.AdapterRoundtrip
public import Patchelf.Elf.Ops.OsAbi
public import Patchelf.Elf.Ops.Execstack
public import Patchelf.Elf.ByteRoundtrip

@[expose] public section

namespace Patchelf.Elf.Adapter

open Patchelf.Elf (ElfFile OsAbi ProgramHeader EncodePreconditions ParsedElf
                     parse encode prepLayoutForEncode syncDtStrszInFile
                     parse_encode_roundtrip prepLayoutForEncode_produces_spliceRegionsDisjoint)
open Patchelf.Elf.Layout (PhType ShType)

/-! ## Generic phdrs-map preservation

    A phdrs `Array.map` that preserves each phdr's `type`/`offset`/`vaddr`/
    `align` (changing only fields no invariant reads, e.g. `flags`)
    preserves both `IsValid` and `IsLoadable`.  Reused by `modifyExecstack`
    and available for any future flags-only phdr op (e.g. a PT_GNU_STACK
    synthesizer). -/

/-- A flags-only phdrs map preserves `IsValid`: only `header_counts`
    inspects phdrs (via `phnum = phdrs.size`), and `map` preserves size. -/
theorem isValid_of_phdrs_map (e : ElfFile) (f : ProgramHeader → ProgramHeader)
    (hVal : e.IsValid) :
    ({ e with phdrs := e.phdrs.map f }).IsValid := by
  obtain ⟨hc, hsw, hst, hdw, hdsw, hcw, htd, hnu⟩ := hVal
  refine ⟨?_, hsw, hst, hdw, hdsw, hcw, htd, hnu⟩
  unfold ElfFile.headerCountsConsistent at hc ⊢
  simpa using hc

/-- A phdrs map preserving per-phdr `type`/`offset`/`vaddr`/`align`
    preserves `IsLoadable`.  Sections, header, `interpIdx`, `dynamicIdx`
    are untouched (the record update only replaces `phdrs`), so the two
    agreement clauses and `segmentCongruence` transport via the preserved
    phdr fields. -/
theorem isLoadable_of_phdrs_map (e : ElfFile) (f : ProgramHeader → ProgramHeader)
    (hType : ∀ ph, (f ph).type = ph.type)
    (hOff : ∀ ph, (f ph).offset = ph.offset)
    (hVad : ∀ ph, (f ph).vaddr = ph.vaddr)
    (hAlign : ∀ ph, (f ph).align = ph.align)
    (hLoad : e.IsLoadable) :
    ({ e with phdrs := e.phdrs.map f }).IsLoadable := by
  have hSz : (e.phdrs.map f).size = e.phdrs.size := by simp
  refine ⟨isValid_of_phdrs_map e f hLoad.toIsValid, hLoad.sections_nonoverlapping, ?_, ?_, ?_⟩
  · have hIdx : ({ e with phdrs := e.phdrs.map f } : ElfFile).interpIdx = e.interpIdx := rfl
    unfold ElfFile.ptInterpAgreement
    rw [hIdx]
    cases hI : e.interpIdx with
    | none => trivial
    | some iS =>
      intro hLt iPh hPh hPhT
      have hPhE : iPh < e.phdrs.size := by rw [hSz] at hPh; exact hPh
      rw [Array.getElem_map] at hPhT ⊢
      rw [hType] at hPhT
      rw [hOff]
      have hBase := hLoad.pt_interp_agrees
      unfold ElfFile.ptInterpAgreement at hBase
      rw [hI] at hBase
      exact hBase hLt iPh hPhE hPhT
  · have hIdx : ({ e with phdrs := e.phdrs.map f } : ElfFile).dynamicIdx = e.dynamicIdx := rfl
    unfold ElfFile.ptDynamicAgreement
    rw [hIdx]
    cases hD : e.dynamicIdx with
    | none => trivial
    | some iS =>
      intro hLt iPh hPh hPhT
      have hPhE : iPh < e.phdrs.size := by rw [hSz] at hPh; exact hPh
      rw [Array.getElem_map] at hPhT ⊢
      rw [hType] at hPhT
      rw [hOff]
      have hBase := hLoad.pt_dynamic_agrees
      unfold ElfFile.ptDynamicAgreement at hBase
      rw [hD] at hBase
      exact hBase hLt iPh hPhE hPhT
  · unfold ElfFile.segmentCongruence
    intro iPh hPh hPhT
    have hPhE : iPh < e.phdrs.size := by rw [hSz] at hPh; exact hPh
    rw [Array.getElem_map] at hPhT ⊢
    rw [hType] at hPhT
    rw [hOff, hVad, hAlign]
    exact hLoad.segment_congruent iPh hPhE hPhT

/-! ## `setOsAbi` (Tier 1: header ident byte) -/

/-- `setOsAbi` commutes with the adapter: its byte output is the no-op
    adapter output with only `header.ident.osAbi` changed.  Holds by `rfl`
    thanks to the un-bundled `toElfFile` (the section-building helpers no
    longer see `typed.header`, so the `setOsAbi` record update doesn't
    block the dependent matches). -/
theorem toElfFile_setOsAbi_eq (template : ElfFile) (typed : ValidElfFile) (abi : OsAbi) :
    toElfFile template (ValidElfFile.setOsAbi typed abi)
      = { toElfFile template typed with
            header := { typed.header with
              ident := { typed.header.ident with osAbi := abi } } } :=
  rfl

/-- `setOsAbi`'s adapter output has the same `sections` as the no-op. -/
theorem toElfFile_setOsAbi_sections (template : ElfFile) (typed : ValidElfFile) (abi : OsAbi) :
    (toElfFile template (ValidElfFile.setOsAbi typed abi)).sections
      = (toElfFile template typed).sections := by
  rw [toElfFile_setOsAbi_eq]

/-- … and the same `phdrs`. -/
theorem toElfFile_setOsAbi_phdrs (template : ElfFile) (typed : ValidElfFile) (abi : OsAbi) :
    (toElfFile template (ValidElfFile.setOsAbi typed abi)).phdrs
      = (toElfFile template typed).phdrs := by
  rw [toElfFile_setOsAbi_eq]

/-- `setOsAbi` preserves byte-layer `IsValid` of the adapter output.
    `osAbi` is an ELF ident byte; no `IsValid` clause inspects it and
    `sections` are unchanged. -/
theorem toElfFile_setOsAbi_preserves_valid (template : ElfFile) (typed : ValidElfFile)
    (abi : OsAbi) (hVal : (toElfFile template typed).IsValid) :
    (toElfFile template (ValidElfFile.setOsAbi typed abi)).IsValid := by
  rw [toElfFile_setOsAbi_eq]
  obtain ⟨hc, hsw, hst, hdw, hdsw, hcw, htd, hnu⟩ := hVal
  exact ⟨hc, hsw, hst, hdw, hdsw, hcw, htd, hnu⟩

/-- `setOsAbi` preserves `IsLoadable` of the adapter output.  Both
    `sections` and `phdrs` are unchanged, so all four loader-coherence
    clauses transport directly. -/
theorem toElfFile_setOsAbi_preserves_loadable (template : ElfFile) (typed : ValidElfFile)
    (abi : OsAbi) (hLoad : (toElfFile template typed).IsLoadable) :
    (toElfFile template (ValidElfFile.setOsAbi typed abi)).IsLoadable := by
  rw [toElfFile_setOsAbi_eq]
  obtain ⟨hVal, hNov, hInt, hDyn, hCong⟩ := hLoad
  obtain ⟨hc, hsw, hst, hdw, hdsw, hcw, htd, hnu⟩ := hVal
  exact ⟨⟨hc, hsw, hst, hdw, hdsw, hcw, htd, hnu⟩, hNov, hInt, hDyn, hCong⟩

/-! ## `modifyExecstack` (Tier 1: PT_GNU_STACK phdr flags) -/

/-- `modifyExecstack` commutes with the adapter: its byte output is the
    no-op output with the PT_GNU_STACK phdrs' `flags` toggled.  Holds by
    `rfl` (only `phdrs` change; sections are built identically). -/
theorem toElfFile_modifyExecstack_eq (template : ElfFile) (typed : ValidElfFile)
    (m : ExecstackMode) :
    toElfFile template (modifyExecstack typed m)
      = { toElfFile template typed with
            phdrs := (toElfFile template typed).phdrs.map fun ph =>
              if ph.type = PhType.PT_GNU_STACK then
                match m with
                | .set => { ph with flags := ph.flags ||| ExecstackFlags.PF_X }
                | .clear => { ph with flags := ph.flags &&& (Complement.complement ExecstackFlags.PF_X) }
              else ph } :=
  rfl

/-- `modifyExecstack` preserves `IsLoadable` of the adapter output.  The
    phdr map toggles only `flags`; `type`/`offset`/`vaddr`/`align` are
    preserved, so `isLoadable_of_phdrs_map` applies. -/
theorem toElfFile_modifyExecstack_preserves_loadable (template : ElfFile)
    (typed : ValidElfFile) (m : ExecstackMode)
    (hLoad : (toElfFile template typed).IsLoadable) :
    (toElfFile template (modifyExecstack typed m)).IsLoadable := by
  rw [toElfFile_modifyExecstack_eq]
  refine isLoadable_of_phdrs_map _ _ ?_ ?_ ?_ ?_ hLoad <;>
    (intro ph; split <;> first | rfl | (cases m <;> rfl))

/-! ## Shared per-op Tier D scaffold (Tier 2/3 ops)

    Tier 2/3 ops change byte-level section sizes (via `patchDynamicEntries`),
    so their raw `toElfFile` output is NOT laid out — `encode` re-lays it out
    through `prepLayoutForEncode ∘ syncDtStrszInFile`.  The meaningful claim
    is therefore the full byte round-trip on the *normalized* form
    `en := prepLayoutForEncode (syncDtStrszInFile eo)`, the structure
    `encodeBody` actually serializes (`encode_eq`).

    `encode_roundtrip_via_normalized` is the reusable spine: it reduces any
    op's Tier D to three obligations on `en`, two of which are largely
    landed:

    * `hPreEn.spliceDisjoint` — discharged by
      `spliceRegionsDisjoint_of_structural` below from the 5 structural input
      invariants on `syncDtStrszInFile eo` (§1.3a's
      `prepLayoutForEncode_produces_spliceRegionsDisjoint`).
    * `hValEn` — `en.IsValid`, from the §1.2 `_preserves_valid` ladder
      (`prepLayoutForEncode` + `syncDtStrszInFile` both preserve `IsValid`).
    * `hIdem : encode eo = encode en` — the genuine remaining gap: the
      pre-passes must be idempotent on `en` (so re-normalizing `en` is a
      no-op and `encodeBody en` round-trips).  This + the residual
      `EncodePreconditions` fields (`syncOk`/`identValid`/`sizeFit`/
      `nullEmpty`/the `*Fit` bounds on the normalized form) are the open
      core of ROADMAP §1.3/§5.1.  They are NOT parser-derivable here because
      `en` is an encoder output, not a parse result. -/

/-- The reusable Tier-D reduction: a byte round-trip for an arbitrary op
    output `eo`, routed through its encoder-normalized form
    `prepLayoutForEncode (syncDtStrszInFile eo)`.  Each op discharges
    `hValEn` (§1.2), `hPreEn` (§1.3a + residual fields), and `hIdem`
    (pre-pass idempotence). -/
theorem encode_roundtrip_via_normalized (eo : ElfFile)
    (hValEn : (prepLayoutForEncode (syncDtStrszInFile eo)).IsValid)
    (hPreEn : EncodePreconditions (prepLayoutForEncode (syncDtStrszInFile eo)))
    (hIdem : encode eo = encode (prepLayoutForEncode (syncDtStrszInFile eo))) :
    parse (encode eo) = .ok ⟨prepLayoutForEncode (syncDtStrszInFile eo), hValEn⟩ := by
  rw [hIdem]
  exact parse_encode_roundtrip ⟨_, hValEn⟩ hPreEn

/-- The hardest `EncodePreconditions` clause (`spliceDisjoint`) for the
    normalized form, discharged from the 5 structural input invariants on
    `syncDtStrszInFile eo` plus `hSection0Null`.  This is the §1.3a composed
    API specialized to the encoder's normalized form; an op supplies these 6
    facts about `syncDtStrszInFile eo` (parser-derivable for any op that
    doesn't widen the file past `currentFileEnd`). -/
theorem spliceRegionsDisjoint_of_structural (eo : ElfFile)
    (hS0 : ∀ (h : 0 < (syncDtStrszInFile eo).sections.size),
      ((syncDtStrszInFile eo).sections[0]'h).type = ShType.SHT_NULL)
    (hHP : (syncDtStrszInFile eo).headerPhdrDisjoint)
    (hHS : (syncDtStrszInFile eo).headerShdrDisjoint)
    (hPS : (syncDtStrszInFile eo).phdrShdrDisjoint)
    (hHSec : (syncDtStrszInFile eo).headerSectionDisjoint)
    (hPSec : (syncDtStrszInFile eo).phdrSectionDisjoint) :
    (prepLayoutForEncode (syncDtStrszInFile eo)).spliceRegionsDisjoint :=
  prepLayoutForEncode_produces_spliceRegionsDisjoint (syncDtStrszInFile eo)
    hS0 hHP hHS hPS hHSec hPSec

end Patchelf.Elf.Adapter
