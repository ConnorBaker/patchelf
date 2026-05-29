/-
  Normalized-form splice disjointness for GROWING dynamic ops, DERIVED from the
  no-op base (ROADMAP §5.1 / PLAN-GROWING-OPS §3 Commit 3).

  The grow-tolerant Tier-D driver `tierD_roundtrip_of_grown_eo`
  (`OpToElfFactorGrow.lean`) currently HYPOTHESIZES the normalized form's
  disjointness `hSplice : (prepLayoutForEncode (syncDtStrszInFile eo))
  .spliceRegionsDisjoint` for the grown op output `eo`.  This file promotes that
  to a THEOREM, derived from the NO-OP base `base := toElfFile template typed`
  (whose 6 structural invariants are parser-derivable).

  ## Why a grow-specific derivation is needed

  A `mapDynamicOp` grower widens ONE section — the dynamic section — at its
  original file offset: `eo = base.updateSectionContent iDyn (.dynamic newDyn)`
  with `newDyn.size ≥ oldDyn.size`, and `updateSectionContent` PRESERVES the
  section's `.offset` (only `encodedSize` grows).  Of the 6 structural
  invariants `prepLayoutForEncode_produces_spliceRegionsDisjoint` consumes:

  * **section-0-NULL, `headerPhdrDisjoint`, `headerShdrDisjoint`,
    `phdrShdrDisjoint`** are size-INDEPENDENT (they read `header.{phoff,shoff}`,
    `phdrs.size`, `sections.size`, all preserved) → transport verbatim via the
    existing `updateSectionContent_*` lemmas (no size hypothesis).
  * **`headerSectionDisjoint` / `phdrSectionDisjoint`** are per-section interval
    facts.  The shrink path uses `IntervalDisjoint_shrink_right`
    (needs `newDyn.size ≤ oldDyn.size`); under growth that is unavailable.  The
    fix: for a section at offset `b₁` disjoint from a region `[a₁,a₂)` via the
    LEFT disjunct (`a₂ ≤ b₁` — the section sits AFTER the region), disjointness
    is offset-only and hence size-stable.  So growth survives PROVIDED the
    (widened) dynamic section starts after the header (`ehdrSize ≤ off`) and
    after the phdr table (`phoff + phnum·phdrSize ≤ off`).  Both hold for every
    real ELF (the dynamic section never overlaps the header or program-header
    table); we take them as explicit, honest side conditions.

  (`shdrSectionDisjoint` and `sectionsNonOverlapping` genuinely break under
  growth, but `prepLayoutForEncode`/`growEOFWith` RE-ESTABLISHES exactly those
  two — it flags the grown section stale and relocates it — so they are NOT in
  the precondition set; that is the whole point of routing through the layout
  pass.  See `prepLayoutForEncode_produces_spliceRegionsDisjoint`.)

  The 6 transported invariants feed
  `Adapter.spliceRegionsDisjoint_of_structural_eo` (which threads them through
  the `syncDtStrszInFile` pre-pass and `prepLayoutForEncode`), yielding the
  normalized form's disjointness — the exact `hSplice` type the grow driver
  wants.  This file's `example` at the bottom build-verifies that match by
  feeding the headline lemma straight into `tierD_roundtrip_of_grown_eo`.
-/
module
public import Patchelf.Elf.OpToElfFactor
public import Patchelf.Elf.OpAdapterPreservation
public import Patchelf.Elf.OpToElfFactorGrow
public import Patchelf.Elf.Ops.AddDebugTag
public import Patchelf.Elf.Ops.NoDefaultLib
@[expose] public section

namespace Patchelf.Elf

open Patchelf.Elf.Layout (ShType)

/-- `IntervalDisjoint` is GROW-stable in the second interval's upper bound
    PROVIDED the section sits at/after the end of the first interval
    (`a₂ ≤ b₁`, the LEFT disjunct).  Unlike the shrink case
    (`IntervalDisjoint_shrink_right`), growth at a fixed offset cannot be derived
    from disjointness alone — the degenerate zero-width-at-offset-0 right
    disjunct breaks — so we require the LEFT disjunct explicitly. -/
theorem IntervalDisjoint_grow_right_of_le (a₁ a₂ b₁ s' : Nat) (hle : a₂ ≤ b₁) :
    IntervalDisjoint a₁ a₂ b₁ (b₁ + s') := by
  unfold IntervalDisjoint; exact Or.inl hle

/-- Generic per-section-interval disjointness GROW-preservation, abstracted over
    the first interval `(a₁,a₂)`.  Mirror of
    `ElfFile.updateSectionContent_sectionInterval_shrink` but for an arbitrary
    `newDyn` (growth allowed): the side hypothesis `hOffGe` supplies the
    LEFT-disjunct fact `a₂ ≤ off_iDyn` for the grown (dynamic) section, which is
    offset-only and hence size-stable.  Untouched sections transport their base
    disjointness verbatim. -/
theorem ElfFile.updateSectionContent_sectionInterval_grow
    (e : ElfFile) (iDyn : Nat) (hLt : iDyn < e.sections.size)
    (newDyn oldDyn : Array DynEntry)
    (hContent : (e.sections[iDyn]'hLt).content = .dynamic oldDyn)
    (a₁ a₂ : Nat)
    (hOffGe : a₂ ≤ (e.sections[iDyn]'hLt).offset.val)
    (h : ∀ (i : Nat) (hi : i < e.sections.size),
      (e.sections[i]'hi).type = ShType.SHT_NOBITS ∨
      (e.sections[i]'hi).type = ShType.SHT_NULL ∨
      IntervalDisjoint a₁ a₂ (e.sections[i]'hi).offset.val
        ((e.sections[i]'hi).offset.val + (e.sections[i]'hi).encodedSize)) :
    ∀ (i : Nat) (hi : i < (e.updateSectionContent iDyn (.dynamic newDyn)).sections.size),
      ((e.updateSectionContent iDyn (.dynamic newDyn)).sections[i]'hi).type = ShType.SHT_NOBITS ∨
      ((e.updateSectionContent iDyn (.dynamic newDyn)).sections[i]'hi).type = ShType.SHT_NULL ∨
      IntervalDisjoint a₁ a₂
        ((e.updateSectionContent iDyn (.dynamic newDyn)).sections[i]'hi).offset.val
        (((e.updateSectionContent iDyn (.dynamic newDyn)).sections[i]'hi).offset.val
          + ((e.updateSectionContent iDyn (.dynamic newDyn)).sections[i]'hi).encodedSize) := by
  intro i hi
  have hiE : i < e.sections.size := by rwa [ElfFile.updateSectionContent_sections_size] at hi
  by_cases hje : i = iDyn
  · subst hje
    rw [ElfFile.updateSectionContent_getElem_self e i _ hLt hi]
    refine Or.inr (Or.inr ?_)
    have hOff : ({ e.sections[i]'hLt with content := .dynamic newDyn } : Section).offset
        = (e.sections[i]'hLt).offset := rfl
    rw [hOff]
    exact IntervalDisjoint_grow_right_of_le _ _ _ _ hOffGe
  · rw [ElfFile.updateSectionContent_getElem_ne e iDyn _ i hiE hje hi]
    exact h i hiE

/-- `headerSectionDisjoint` survives a `.dynamic` GROW at the dynamic index,
    given the dynamic section starts at/after the ELF header
    (`ehdrSize ≤ off_iDyn`, true for every real ELF). -/
theorem ElfFile.updateSectionContent_headerSectionDisjoint_grow
    (e : ElfFile) (iDyn : Nat) (hLt : iDyn < e.sections.size)
    (newDyn oldDyn : Array DynEntry)
    (hContent : (e.sections[iDyn]'hLt).content = .dynamic oldDyn)
    (hOffGe : Layout.ehdrSize ≤ (e.sections[iDyn]'hLt).offset.val)
    (h : e.headerSectionDisjoint) :
    (e.updateSectionContent iDyn (.dynamic newDyn)).headerSectionDisjoint :=
  ElfFile.updateSectionContent_sectionInterval_grow e iDyn hLt newDyn oldDyn hContent
    0 Layout.ehdrSize hOffGe h

/-- `phdrSectionDisjoint` survives a `.dynamic` GROW at the dynamic index, given
    the dynamic section starts at/after the END of the phdr table
    (`phoff + phnum·phdrSize ≤ off_iDyn` — the "phdr table precedes the dynamic
    section" orientation, the normal one for real ELFs). -/
theorem ElfFile.updateSectionContent_phdrSectionDisjoint_grow
    (e : ElfFile) (iDyn : Nat) (hLt : iDyn < e.sections.size)
    (newDyn oldDyn : Array DynEntry)
    (hContent : (e.sections[iDyn]'hLt).content = .dynamic oldDyn)
    (hOffGe : e.header.phoff.val + e.phdrs.size * Layout.phdrSize
        ≤ (e.sections[iDyn]'hLt).offset.val)
    (h : e.phdrSectionDisjoint) :
    (e.updateSectionContent iDyn (.dynamic newDyn)).phdrSectionDisjoint := by
  have hpre := ElfFile.updateSectionContent_sectionInterval_grow e iDyn hLt newDyn oldDyn
    hContent e.header.phoff.val (e.header.phoff.val + e.phdrs.size * Layout.phdrSize) hOffGe h
  unfold ElfFile.phdrSectionDisjoint
  intro i hi
  simp only [ElfFile.updateSectionContent_header, ElfFile.updateSectionContent_phdrs]
  exact hpre i hi

/-! ## Headline: normalized-form splice disjointness for a GROWN dynamic op

    The grow-tolerant analogue of the shrink path's
    `Adapter.spliceRegionsDisjoint_of_structural_eo`-from-base derivation
    (`Adapter.mapDynamicOp_structural_transport`).  From the NO-OP base's 6
    structural invariants + the factoring `eo = base.updateSectionContent iDyn
    (.dynamic newDyn)` (any `newDyn`, growth allowed) + two honest LEFT-disjunct
    side conditions on the dynamic section's file offset, we conclude exactly the
    `hSplice` the grow driver (`tierD_roundtrip_of_grown_eo`) hypothesizes. -/

/-- Normalized-form `spliceRegionsDisjoint` for a grown dynamic op, derived from
    the no-op base.

    `base`'s 6 structural invariants (all parser-derivable) transport to `eo`:
    section-0-NULL and the three header/table clauses are size-independent; the
    two per-section clauses survive growth because the (only) widened section —
    the dynamic section — sits after the ELF header and after the phdr table
    (`hDynAfterHeader`, `hDynAfterPhdr`; both true for every real ELF).  Feeding
    those 6 into `Adapter.spliceRegionsDisjoint_of_structural_eo` (which routes
    through `syncDtStrszInFile` + `prepLayoutForEncode`) yields the normalized
    form's disjointness.

    Conclusion type is byte-for-byte the driver's `hSplice` (build-verified by
    the `example` at the bottom of this file). -/
theorem spliceRegionsDisjoint_of_grown_base
    (base : ElfFile) (iDyn : Nat) (hLt : iDyn < base.sections.size)
    (newDyn oldDyn : Array DynEntry)
    (hContent : (base.sections[iDyn]'hLt).content = .dynamic oldDyn)
    (eo : ElfFile)
    (hFactor : eo = base.updateSectionContent iDyn (.dynamic newDyn))
    -- the no-op base's 6 structural invariants (parser-derivable):
    (hS0 : ∀ (h : 0 < base.sections.size), (base.sections[0]'h).type = ShType.SHT_NULL)
    (hHP : base.headerPhdrDisjoint)
    (hHS : base.headerShdrDisjoint)
    (hPS : base.phdrShdrDisjoint)
    (hHSec : base.headerSectionDisjoint)
    (hPSec : base.phdrSectionDisjoint)
    -- honest side conditions: the dynamic section is after the header / phdr table:
    (hDynAfterHeader : Layout.ehdrSize ≤ (base.sections[iDyn]'hLt).offset.val)
    (hDynAfterPhdr : base.header.phoff.val + base.phdrs.size * Layout.phdrSize
        ≤ (base.sections[iDyn]'hLt).offset.val) :
    (prepLayoutForEncode (syncDtStrszInFile eo)).spliceRegionsDisjoint := by
  subst hFactor
  exact Adapter.spliceRegionsDisjoint_of_structural_eo
    (base.updateSectionContent iDyn (.dynamic newDyn))
    (ElfFile.updateSectionContent_section0Null base iDyn hLt oldDyn newDyn hContent hS0)
    (ElfFile.updateSectionContent_headerPhdrDisjoint base iDyn _ hHP)
    (ElfFile.updateSectionContent_headerShdrDisjoint base iDyn _ hHS)
    (ElfFile.updateSectionContent_phdrShdrDisjoint base iDyn _ hPS)
    (ElfFile.updateSectionContent_headerSectionDisjoint_grow base iDyn hLt newDyn oldDyn
      hContent hDynAfterHeader hHSec)
    (ElfFile.updateSectionContent_phdrSectionDisjoint_grow base iDyn hLt newDyn oldDyn
      hContent hDynAfterPhdr hPSec)

end Patchelf.Elf

namespace Patchelf.Elf.Adapter
open Patchelf.Elf (ElfFile StringTable DynEntry SectionContent prepLayoutForEncode syncDtStrszInFile)
open Patchelf.Elf.Layout (ShType)

/-! ## `mapDynamicOp`-level corollary (drop-in `hSplice` for the grow capstones)

    The grow analogue of `mapDynamicOp_structural_transport`: from the
    `RemoveRpathFactorData` bundle (`f`-agnostic; describes the no-op chain) +
    the no-op base's 6 structural invariants + the two offset side conditions on
    the base's dynamic section, conclude the normalized-form splice disjointness
    of the GROWN op output `toElfFile template (mapDynamicOp typed f)`.  This is
    exactly the `hSplice` the grow driver wants — no size bound needed (growth
    allowed).  The `addDebugTag`/`noDefaultLib` capstones can build their
    `RemoveRpathFactorData` (they already do, for the factoring) + supply the two
    offset facts to discharge `hSplice` via this lemma. -/
theorem mapDynamicOp_spliceRegionsDisjoint_of_base
    (template : ElfFile) (typed : ValidElfFile) (h : typed.dynamic.isSome)
    (f : {ds : StringSection} → DynamicSection ds → DynamicSection ds)
    (D : RemoveRpathFactorData template typed h)
    (hHP : (toElfFile template typed).headerPhdrDisjoint)
    (hHS : (toElfFile template typed).headerShdrDisjoint)
    (hPS : (toElfFile template typed).phdrShdrDisjoint)
    (hHSec : (toElfFile template typed).headerSectionDisjoint)
    (hPSec : (toElfFile template typed).phdrSectionDisjoint)
    (hS0 : ∀ (h0 : 0 < (toElfFile template typed).sections.size),
      ((toElfFile template typed).sections[0]'h0).type = ShType.SHT_NULL)
    (hDynAfterHeader : ∀ (hLt : D.iDyn < (toElfFile template typed).sections.size),
      Layout.ehdrSize ≤ ((toElfFile template typed).sections[D.iDyn]'hLt).offset.val)
    (hDynAfterPhdr : ∀ (hLt : D.iDyn < (toElfFile template typed).sections.size),
      (toElfFile template typed).header.phoff.val
        + (toElfFile template typed).phdrs.size * Layout.phdrSize
        ≤ ((toElfFile template typed).sections[D.iDyn]'hLt).offset.val) :
    (prepLayoutForEncode (syncDtStrszInFile (toElfFile template (mapDynamicOp typed f)))).spliceRegionsDisjoint := by
  have hFactor := toElfFile_mapDynamicOp_factor template typed f h D.td D.hTd D.iDyn D.hIdx0 D.bd D.hByte0 D.hbN D.dynN D.hContentN D.hDsN D.hInterpNe
  have hLtBase : D.iDyn < (toElfFile template typed).sections.size := by
    rw [toElfFile_expand]; simpa using D.hbN
  have hChainBound : D.iDyn < (applyInterp (applyVerneed (applyGnuHash (applySysvHash (applyVersym (applyDynamic (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym) (ds := typed.dynstr) (some D.td)) typed.versym) typed.sysvHash) typed.gnuHash) typed.verneed) typed.interp).sections.size := by
    simpa using D.hbN
  have hContentChain := toElfFile_content_at_dynamicIdx template typed D.td D.iDyn D.hIdx0 D.bd D.hByte0 D.hInterpNe hChainBound
  have hSecEq : (toElfFile template typed).sections = (applyInterp (applyVerneed (applyGnuHash (applySysvHash (applyVersym (applyDynamic (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym) (ds := typed.dynstr) (some D.td)) typed.versym) typed.sysvHash) typed.gnuHash) typed.verneed) typed.interp).sections := by
    rw [toElfFile_expand, D.hTd]
  have hOld : ((toElfFile template typed).sections[D.iDyn]'hLtBase).content
      = .dynamic (patchDynamicEntries D.bd D.td) := by
    rw [ElfFile.getElem_content_congr_sections (toElfFile template typed) _ D.iDyn hSecEq hLtBase]
    exact hContentChain
  exact Patchelf.Elf.spliceRegionsDisjoint_of_grown_base (toElfFile template typed) D.iDyn hLtBase
    (patchDynamicEntries D.bd (f D.td)) (patchDynamicEntries D.bd D.td) hOld
    (toElfFile template (mapDynamicOp typed f)) hFactor
    hS0 hHP hHS hPS hHSec hPSec (hDynAfterHeader hLtBase) (hDynAfterPhdr hLtBase)

end Patchelf.Elf.Adapter

namespace Patchelf.Elf.Adapter
open Patchelf.Elf (ElfFile StringTable IdentBytesValid parse encode prepLayoutForEncode
                     syncDtStrszInFile prepLayout_syncDtStrsz_preserves_valid)
open Patchelf.Elf.Layout (ShType)

/-! ## §A — `addDebugTag` Tier-D round-trip, `hSplice` DERIVED

    `addDebugTag e h` is definitionally `mapDynamicOp e (·.addDebugTag)` (dynstr
    UNCHANGED, `.dynamic` +≤1).  Unlike the first-cut capstone (which
    hypothesized `hSplice`), this DERIVES the normalized form's disjointness via
    `mapDynamicOp_spliceRegionsDisjoint_of_base` — so the surface is the no-op
    base's 6 structural invariants (parser-derivable, the same surface the SHRINK
    capstones use) + two honest offset side conditions (the dynamic section sits
    after the header / phdr table — true for every real ELF, weaker than the
    shrink path's `hSizeBound`).  The `RemoveRpathFactorData` bundle `D` is
    `f`-agnostic (describes the no-op chain). -/
theorem toElfFile_addDebugTag_tierD_roundtrip_derived (template : ElfFile) (typed : ValidElfFile)
    (h : typed.dynamic.isSome) (D : RemoveRpathFactorData template typed h)
    (hVal : (toElfFile template (addDebugTag typed h)).IsValid)
    (hPhdrFit : ((toElfFile template (addDebugTag typed h)).phdrs.size + 1) < UInt16.size)
    {ds : StringTable} (hDs : (toElfFile template (addDebugTag typed h)).dynstr = some ds)
    (hFit : ds.bytes.size < UInt64.size)
    -- no-op base's 6 structural invariants (parser-derivable):
    (hHP : (toElfFile template typed).headerPhdrDisjoint)
    (hHS : (toElfFile template typed).headerShdrDisjoint)
    (hPS : (toElfFile template typed).phdrShdrDisjoint)
    (hHSec : (toElfFile template typed).headerSectionDisjoint)
    (hPSec : (toElfFile template typed).phdrSectionDisjoint)
    (hS0 : ∀ (h0 : 0 < (toElfFile template typed).sections.size),
      ((toElfFile template typed).sections[0]'h0).type = ShType.SHT_NULL)
    -- honest offset side conditions on the base's dynamic section:
    (hDynAfterHeader : ∀ (hLt : D.iDyn < (toElfFile template typed).sections.size),
      Layout.ehdrSize ≤ ((toElfFile template typed).sections[D.iDyn]'hLt).offset.val)
    (hDynAfterPhdr : ∀ (hLt : D.iDyn < (toElfFile template typed).sections.size),
      (toElfFile template typed).header.phoff.val
        + (toElfFile template typed).phdrs.size * Layout.phdrSize
        ≤ ((toElfFile template typed).sections[D.iDyn]'hLt).offset.val)
    (hIdentEo : IdentBytesValid (toElfFile template (addDebugTag typed h)))
    (hSizeFitEo : ∀ (i : Nat) (hi : i < (toElfFile template (addDebugTag typed h)).sections.size),
      ((toElfFile template (addDebugTag typed h)).sections[i]'hi).shdrSize < UInt64.size)
    (hNullEmptyEo : ∀ (i : Nat) (hi : i < (toElfFile template (addDebugTag typed h)).sections.size),
      ((toElfFile template (addDebugTag typed h)).sections[i]'hi).type = ShType.SHT_NULL →
      ∃ ty hOk bs, ((toElfFile template (addDebugTag typed h)).sections[i]'hi).content = .raw ty hOk bs ∧ bs.size = 0)
    (hHdrEntryEo : (toElfFile template (addDebugTag typed h)).header.entry.val < UInt64.size)
    (hHdrPhoff : (prepLayoutForEncode (syncDtStrszInFile (toElfFile template (addDebugTag typed h)))).header.phoff.val < UInt64.size)
    (hHdrShoff : (prepLayoutForEncode (syncDtStrszInFile (toElfFile template (addDebugTag typed h)))).header.shoff.val < UInt64.size)
    (hPhdrFitEn : ∀ (i : Nat) (hi : i < (prepLayoutForEncode (syncDtStrszInFile (toElfFile template (addDebugTag typed h)))).phdrs.size),
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (addDebugTag typed h)))).phdrs[i]'hi).offset.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (addDebugTag typed h)))).phdrs[i]'hi).vaddr.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (addDebugTag typed h)))).phdrs[i]'hi).paddr.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (addDebugTag typed h)))).phdrs[i]'hi).filesz.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (addDebugTag typed h)))).phdrs[i]'hi).memsz.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (addDebugTag typed h)))).phdrs[i]'hi).align.val < UInt64.size)
    (hShdrFitEn : ∀ (i : Nat) (hi : i < (prepLayoutForEncode (syncDtStrszInFile (toElfFile template (addDebugTag typed h)))).sections.size),
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (addDebugTag typed h)))).sections[i]'hi).addr.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (addDebugTag typed h)))).sections[i]'hi).offset.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (addDebugTag typed h)))).sections[i]'hi).addralign.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (addDebugTag typed h)))).sections[i]'hi).entsize.val < UInt64.size) :
    parse (encode (toElfFile template (addDebugTag typed h)))
      = .ok ⟨prepLayoutForEncode (syncDtStrszInFile (toElfFile template (addDebugTag typed h))),
             prepLayout_syncDtStrsz_preserves_valid _ hVal hPhdrFit hDs⟩ :=
  tierD_roundtrip_of_grown_eo (toElfFile template (addDebugTag typed h))
    hVal hPhdrFit hDs hFit
    (mapDynamicOp_spliceRegionsDisjoint_of_base template typed h (fun d => d.addDebugTag) D
      hHP hHS hPS hHSec hPSec hS0 hDynAfterHeader hDynAfterPhdr)
    hIdentEo hSizeFitEo hNullEmptyEo hHdrEntryEo hHdrPhoff hHdrShoff hPhdrFitEn hShdrFitEn

/-! ## §B — `noDefaultLib` Tier-D round-trip, `hSplice` DERIVED

    `noDefaultLib e h` is definitionally `mapDynamicOp e (·.setNoDefaultLib)`.
    Identical shape to `addDebugTag` — `hSplice` derived via the same corollary. -/
theorem toElfFile_noDefaultLib_tierD_roundtrip_derived (template : ElfFile) (typed : ValidElfFile)
    (h : typed.dynamic.isSome) (D : RemoveRpathFactorData template typed h)
    (hVal : (toElfFile template (noDefaultLib typed h)).IsValid)
    (hPhdrFit : ((toElfFile template (noDefaultLib typed h)).phdrs.size + 1) < UInt16.size)
    {ds : StringTable} (hDs : (toElfFile template (noDefaultLib typed h)).dynstr = some ds)
    (hFit : ds.bytes.size < UInt64.size)
    (hHP : (toElfFile template typed).headerPhdrDisjoint)
    (hHS : (toElfFile template typed).headerShdrDisjoint)
    (hPS : (toElfFile template typed).phdrShdrDisjoint)
    (hHSec : (toElfFile template typed).headerSectionDisjoint)
    (hPSec : (toElfFile template typed).phdrSectionDisjoint)
    (hS0 : ∀ (h0 : 0 < (toElfFile template typed).sections.size),
      ((toElfFile template typed).sections[0]'h0).type = ShType.SHT_NULL)
    (hDynAfterHeader : ∀ (hLt : D.iDyn < (toElfFile template typed).sections.size),
      Layout.ehdrSize ≤ ((toElfFile template typed).sections[D.iDyn]'hLt).offset.val)
    (hDynAfterPhdr : ∀ (hLt : D.iDyn < (toElfFile template typed).sections.size),
      (toElfFile template typed).header.phoff.val
        + (toElfFile template typed).phdrs.size * Layout.phdrSize
        ≤ ((toElfFile template typed).sections[D.iDyn]'hLt).offset.val)
    (hIdentEo : IdentBytesValid (toElfFile template (noDefaultLib typed h)))
    (hSizeFitEo : ∀ (i : Nat) (hi : i < (toElfFile template (noDefaultLib typed h)).sections.size),
      ((toElfFile template (noDefaultLib typed h)).sections[i]'hi).shdrSize < UInt64.size)
    (hNullEmptyEo : ∀ (i : Nat) (hi : i < (toElfFile template (noDefaultLib typed h)).sections.size),
      ((toElfFile template (noDefaultLib typed h)).sections[i]'hi).type = ShType.SHT_NULL →
      ∃ ty hOk bs, ((toElfFile template (noDefaultLib typed h)).sections[i]'hi).content = .raw ty hOk bs ∧ bs.size = 0)
    (hHdrEntryEo : (toElfFile template (noDefaultLib typed h)).header.entry.val < UInt64.size)
    (hHdrPhoff : (prepLayoutForEncode (syncDtStrszInFile (toElfFile template (noDefaultLib typed h)))).header.phoff.val < UInt64.size)
    (hHdrShoff : (prepLayoutForEncode (syncDtStrszInFile (toElfFile template (noDefaultLib typed h)))).header.shoff.val < UInt64.size)
    (hPhdrFitEn : ∀ (i : Nat) (hi : i < (prepLayoutForEncode (syncDtStrszInFile (toElfFile template (noDefaultLib typed h)))).phdrs.size),
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (noDefaultLib typed h)))).phdrs[i]'hi).offset.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (noDefaultLib typed h)))).phdrs[i]'hi).vaddr.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (noDefaultLib typed h)))).phdrs[i]'hi).paddr.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (noDefaultLib typed h)))).phdrs[i]'hi).filesz.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (noDefaultLib typed h)))).phdrs[i]'hi).memsz.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (noDefaultLib typed h)))).phdrs[i]'hi).align.val < UInt64.size)
    (hShdrFitEn : ∀ (i : Nat) (hi : i < (prepLayoutForEncode (syncDtStrszInFile (toElfFile template (noDefaultLib typed h)))).sections.size),
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (noDefaultLib typed h)))).sections[i]'hi).addr.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (noDefaultLib typed h)))).sections[i]'hi).offset.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (noDefaultLib typed h)))).sections[i]'hi).addralign.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (noDefaultLib typed h)))).sections[i]'hi).entsize.val < UInt64.size) :
    parse (encode (toElfFile template (noDefaultLib typed h)))
      = .ok ⟨prepLayoutForEncode (syncDtStrszInFile (toElfFile template (noDefaultLib typed h))),
             prepLayout_syncDtStrsz_preserves_valid _ hVal hPhdrFit hDs⟩ :=
  tierD_roundtrip_of_grown_eo (toElfFile template (noDefaultLib typed h))
    hVal hPhdrFit hDs hFit
    (mapDynamicOp_spliceRegionsDisjoint_of_base template typed h (fun d => d.setNoDefaultLib) D
      hHP hHS hPS hHSec hPSec hS0 hDynAfterHeader hDynAfterPhdr)
    hIdentEo hSizeFitEo hNullEmptyEo hHdrEntryEo hHdrPhoff hHdrShoff hPhdrFitEn hShdrFitEn

end Patchelf.Elf.Adapter
