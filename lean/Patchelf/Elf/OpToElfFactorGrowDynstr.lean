/-
  OpToElfFactorGrowDynstr.lean

  Two-field (dynstr + dynamic) factoring + Tier-D round-trip for the
  `growDynstrDynamicOp` growers (ROADMAP §5.1 / PLAN-GROWING-OPS §3 Commit 5):
  `addNeeded`, `modifyRPath .set`, `modifySoname .set`.

  Integration: add `public import Patchelf.Elf.OpToElfFactorGrowDynstr` to
  `Patchelf.lean` after `OpToElfFactorGrow`.

  Companion to `OpToElfFactor.lean` (single-`.dynamic`-field shrink factoring)
  and `OpToElfFactorGrow.lean` (the `mapDynamicOp` growers `addDebugTag` /
  `noDefaultLib` + the grow-tolerant Tier-D driver `tierD_roundtrip_of_grown_eo`).

  Unlike the `mapDynamicOp` growers (which change ONLY `.dynamic`), a
  `growDynstrDynamicOp` grower changes TWO sections: it appends `name` to
  `.dynstr` (the `.dynstr` section's bytes grow) AND maps a mutator over
  `.dynamic`.  `growDynstr` also produces a DIFFERENT `StringSection` (the
  dependent index changes) and rebases `.dynsym` / `.dynamic`.

  ## The factoring (§A) — the genuinely-new artifact

  The key observation that collapses the "two-field" problem to ONE field:

      addNeeded typed lib h
        = { tg with dynamic := tg.dynamic.map (·.pushNeeded off) }      (rfl)

  where `tg := (typed.growDynstr lib).1` is `typed` with its dynstr grown and
  `.dynsym` / `.dynamic` rebased, and `off := typed.dynstr.appendOffset lib`.
  The ENTIRE `.dynstr` growth (+ rebases) is absorbed into the base
  `toElfFile template tg`; the only delta from that base is the `.dynamic`
  `pushNeeded` patch — a single `.dynamic`-update at `iDyn`.  So:

      toElfFile template (addNeeded typed lib h)
        = (toElfFile template tg).updateSectionContent iDyn
            (.dynamic (patchDynamicEntries bd (td.pushNeeded off)))

  i.e. exactly the `(toElfFile template typed_with_grown_dynstr).updateSection-
  Content iDyn (.dynamic …)` shape (Strategy A).

  The existing single-`.dynamic` factoring `toElfFile_mapDynamicOp_factor` wants a
  `{ds}`-polymorphic `f`, but a grow-dynstr mutator is `ds`-MONOMORPHIC (tied to
  `off : Fin tg.dynstr.size`).  The factoring proof, however, only ever touches
  `.dynamic` as an `Option.map`, so it generalizes to a monomorphic
  `g : DynamicSection tg.dynstr → DynamicSection tg.dynstr` verbatim
  (`toElfFile_dynamicMapMono_factor`); the three growers then differ only in `g`.

  ## The capstones (§B/§C)

  A grow op widens a section, so `eo`'s per-section disjointness genuinely
  BREAKS and the shrink-monotonicity core does not apply — the grow-tolerant
  driver `tierD_roundtrip_of_grown_eo` (OpToElfFactorGrow.lean) instead routes
  through the layout pass, taking the NORMALIZED form's `spliceRegionsDisjoint`
  (`hSplice`) — the sanctioned "the layout engine produced disjoint output"
  surface.  The capstones below are thin instantiations of that driver on the
  concrete op outputs, HYPOTHESIZING `hSplice` (first-cut caliber).

  NOTE: unlike the `mapDynamicOp` growers (`addDebugTag`/`noDefaultLib`), whose
  `hSplice` is now DERIVED from the no-op base
  (`GrowEOFDisjointOfBase.mapDynamicOp_spliceRegionsDisjoint_of_base`), these
  dynstr growers still hypothesize it — deriving it needs a TWO-grown-section
  analogue of that establisher (the `.dynstr` section grows too).  The §A
  factoring + `toElfFile_addNeeded_content_at_dynamicIdx` corollary are the
  building blocks for that future derivation; see PLAN-GROWING-OPS §3 Commit 3.
-/
module
public import Patchelf.Elf.OpToElfFactorGrow
public import Patchelf.Elf.Ops.AddNeeded
public import Patchelf.Elf.Ops.Rpath
public import Patchelf.Elf.Ops.Soname
@[expose] public section

namespace Patchelf.Elf.Adapter
open Patchelf.Elf (ElfFile StringTable StringSection DynamicSection DynEntry
                     IdentBytesValid parse encode prepLayoutForEncode
                     syncDtStrszInFile prepLayout_syncDtStrsz_preserves_valid
                     growDynstrDynamicOp addNeeded modifyRPath modifySoname)
open Patchelf.Elf.Layout (ShType)

/-! ## §A — Two-field factoring via a MONOMORPHIC-`g` master factoring -/

/-- Master factoring over a MONOMORPHIC `g` on `.dynamic`: mirrors
    `toElfFile_mapDynamicOp_factor`, but `g : DynamicSection typed.dynstr →
    DynamicSection typed.dynstr` need not be `{ds}`-polymorphic (the proof only
    touches `.dynamic` as an `Option.map`).  This is the single keystone the
    three `growDynstrDynamicOp` growers share — applied with `typed := tg` (the
    grown base) and `g` the per-op mutator (`pushNeeded off` / `setRpathTag fr
    off` / `setSonameOff off`).  The per-op facts (`hIdx0` … `hInterpNe`) are the
    `RemoveRpathFactorData`-style witnesses about the no-op chain on the base. -/
theorem toElfFile_dynamicMapMono_factor (template : ElfFile) (typed : ValidElfFile)
    (g : DynamicSection typed.dynstr → DynamicSection typed.dynstr)
    (td : DynamicSection typed.dynstr) (hTd : typed.dynamic = some td)
    (iDyn : Nat)
    (hIdx0 : (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym).dynamicIdx = some iDyn)
    (bd : Array DynEntry)
    (hByte0 : (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym).dynamic = some bd)
    (hbN : iDyn < (applyVerneed (applyGnuHash (applySysvHash (applyVersym (applyDynamic (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym) (ds := typed.dynstr) (some td)) typed.versym) typed.sysvHash) typed.gnuHash) typed.verneed).sections.size)
    (dynN : Array DynEntry)
    (hContentN : ((applyVerneed (applyGnuHash (applySysvHash (applyVersym (applyDynamic (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym) (ds := typed.dynstr) (some td)) typed.versym) typed.sysvHash) typed.gnuHash) typed.verneed).sections[iDyn]'hbN).content = .dynamic dynN)
    {dsN : StringTable}
    (hDsN : (applyVerneed (applyGnuHash (applySysvHash (applyVersym (applyDynamic (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym) (ds := typed.dynstr) (some td)) typed.versym) typed.sysvHash) typed.gnuHash) typed.verneed).dynstr = some dsN)
    (hInterpNe : ∀ i, (applyVerneed (applyGnuHash (applySysvHash (applyVersym (applyDynamic (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym) (ds := typed.dynstr) (some td)) typed.versym) typed.sysvHash) typed.gnuHash) typed.verneed).interpIdx = some i → i ≠ iDyn) :
    toElfFile template { typed with dynamic := typed.dynamic.map g }
      = (toElfFile template typed).updateSectionContent iDyn (.dynamic (patchDynamicEntries bd (g td))) := by
  have hKey : ∀ (a b : ElfFile), a.header = b.header → a.phdrs = b.phdrs → a.sections = b.sections → a = b := by
    intro a b h1 h2 h3; cases a; cases b; simp_all
  apply hKey
  · rw [toElfFile_header, ElfFile.updateSectionContent_header, toElfFile_header]
  · rw [toElfFile_phdrs, ElfFile.updateSectionContent_phdrs, toElfFile_phdrs]
  · rw [toElfFile_expand, toElfFile_expand]
    show (applyInterp (applyVerneed (applyGnuHash (applySysvHash (applyVersym (applyDynamic (applyDynsym (applyDynstr template typed.dynstr) (ds := typed.dynstr) typed.dynsym) (ds := typed.dynstr) (typed.dynamic.map g)) typed.versym) typed.sysvHash) typed.gnuHash) typed.verneed) typed.interp).sections = _
    rw [hTd]; simp only [Option.map_some]
    rw [innerChain_factor_general template typed (g td) td iDyn hIdx0 bd hByte0 hbN dynN hContentN hDsN hInterpNe]
    exact ElfFile.updateSectionContent_sections_eq_of_sections _ _ iDyn _ rfl

/-! ### `addNeeded` two-field factoring -/

/-- `addNeeded typed lib h` is definitionally the dynamic-map of `pushNeeded off`
    on the grown base `tg := (typed.growDynstr lib).1`. -/
theorem addNeeded_eq_dynamicMapMono (typed : ValidElfFile) (lib : String) (h : typed.dynamic.isSome) :
    addNeeded typed lib h
      = { (typed.growDynstr lib).1 with
            dynamic := (typed.growDynstr lib).1.dynamic.map
              (fun d => d.pushNeeded (typed.dynstr.appendOffset lib)) } := rfl

/-- THE `addNeeded` factoring (Strategy A): the op output is the no-op output on
    the GROWN base `toElfFile template (typed.growDynstr lib).1` updated at `iDyn`
    with the `pushNeeded`-patched dynamic content.  The dynstr growth + dynsym/
    dynamic rebases are entirely inside the base. -/
theorem toElfFile_addNeeded_factor (template : ElfFile) (typed : ValidElfFile)
    (lib : String) (h : typed.dynamic.isSome)
    (td : DynamicSection (typed.growDynstr lib).1.dynstr)
    (hTd : (typed.growDynstr lib).1.dynamic = some td)
    (iDyn : Nat)
    (hIdx0 : (applyDynsym (applyDynstr template (typed.growDynstr lib).1.dynstr) (ds := (typed.growDynstr lib).1.dynstr) (typed.growDynstr lib).1.dynsym).dynamicIdx = some iDyn)
    (bd : Array DynEntry)
    (hByte0 : (applyDynsym (applyDynstr template (typed.growDynstr lib).1.dynstr) (ds := (typed.growDynstr lib).1.dynstr) (typed.growDynstr lib).1.dynsym).dynamic = some bd)
    (hbN : iDyn < (applyVerneed (applyGnuHash (applySysvHash (applyVersym (applyDynamic (applyDynsym (applyDynstr template (typed.growDynstr lib).1.dynstr) (ds := (typed.growDynstr lib).1.dynstr) (typed.growDynstr lib).1.dynsym) (ds := (typed.growDynstr lib).1.dynstr) (some td)) (typed.growDynstr lib).1.versym) (typed.growDynstr lib).1.sysvHash) (typed.growDynstr lib).1.gnuHash) (typed.growDynstr lib).1.verneed).sections.size)
    (dynN : Array DynEntry)
    (hContentN : ((applyVerneed (applyGnuHash (applySysvHash (applyVersym (applyDynamic (applyDynsym (applyDynstr template (typed.growDynstr lib).1.dynstr) (ds := (typed.growDynstr lib).1.dynstr) (typed.growDynstr lib).1.dynsym) (ds := (typed.growDynstr lib).1.dynstr) (some td)) (typed.growDynstr lib).1.versym) (typed.growDynstr lib).1.sysvHash) (typed.growDynstr lib).1.gnuHash) (typed.growDynstr lib).1.verneed).sections[iDyn]'hbN).content = .dynamic dynN)
    {dsN : StringTable}
    (hDsN : (applyVerneed (applyGnuHash (applySysvHash (applyVersym (applyDynamic (applyDynsym (applyDynstr template (typed.growDynstr lib).1.dynstr) (ds := (typed.growDynstr lib).1.dynstr) (typed.growDynstr lib).1.dynsym) (ds := (typed.growDynstr lib).1.dynstr) (some td)) (typed.growDynstr lib).1.versym) (typed.growDynstr lib).1.sysvHash) (typed.growDynstr lib).1.gnuHash) (typed.growDynstr lib).1.verneed).dynstr = some dsN)
    (hInterpNe : ∀ i, (applyVerneed (applyGnuHash (applySysvHash (applyVersym (applyDynamic (applyDynsym (applyDynstr template (typed.growDynstr lib).1.dynstr) (ds := (typed.growDynstr lib).1.dynstr) (typed.growDynstr lib).1.dynsym) (ds := (typed.growDynstr lib).1.dynstr) (some td)) (typed.growDynstr lib).1.versym) (typed.growDynstr lib).1.sysvHash) (typed.growDynstr lib).1.gnuHash) (typed.growDynstr lib).1.verneed).interpIdx = some i → i ≠ iDyn) :
    toElfFile template (addNeeded typed lib h)
      = (toElfFile template (typed.growDynstr lib).1).updateSectionContent iDyn
          (.dynamic (patchDynamicEntries bd (td.pushNeeded (typed.dynstr.appendOffset lib)))) := by
  rw [addNeeded_eq_dynamicMapMono]
  exact toElfFile_dynamicMapMono_factor template (typed.growDynstr lib).1
    (fun d => d.pushNeeded (typed.dynstr.appendOffset lib)) td hTd iDyn hIdx0 bd hByte0 hbN dynN hContentN hDsN hInterpNe

/-- The factored `addNeeded` output's content at `iDyn` is the `pushNeeded`-
    patched dynamic (a corollary of the factoring + `updateSectionContent_-
    content_self`).  This is the building block any future structural reasoning
    about `eo`'s grown section needs (e.g. a grow-tolerant `hSplice` derivation,
    PLAN-GROWING-OPS §3 Commit 3). -/
theorem toElfFile_addNeeded_content_at_dynamicIdx (template : ElfFile) (typed : ValidElfFile)
    (lib : String) (h : typed.dynamic.isSome)
    (td : DynamicSection (typed.growDynstr lib).1.dynstr)
    (hTd : (typed.growDynstr lib).1.dynamic = some td)
    (iDyn : Nat)
    (hIdx0 : (applyDynsym (applyDynstr template (typed.growDynstr lib).1.dynstr) (ds := (typed.growDynstr lib).1.dynstr) (typed.growDynstr lib).1.dynsym).dynamicIdx = some iDyn)
    (bd : Array DynEntry)
    (hByte0 : (applyDynsym (applyDynstr template (typed.growDynstr lib).1.dynstr) (ds := (typed.growDynstr lib).1.dynstr) (typed.growDynstr lib).1.dynsym).dynamic = some bd)
    (hbN : iDyn < (applyVerneed (applyGnuHash (applySysvHash (applyVersym (applyDynamic (applyDynsym (applyDynstr template (typed.growDynstr lib).1.dynstr) (ds := (typed.growDynstr lib).1.dynstr) (typed.growDynstr lib).1.dynsym) (ds := (typed.growDynstr lib).1.dynstr) (some td)) (typed.growDynstr lib).1.versym) (typed.growDynstr lib).1.sysvHash) (typed.growDynstr lib).1.gnuHash) (typed.growDynstr lib).1.verneed).sections.size)
    (dynN : Array DynEntry)
    (hContentN : ((applyVerneed (applyGnuHash (applySysvHash (applyVersym (applyDynamic (applyDynsym (applyDynstr template (typed.growDynstr lib).1.dynstr) (ds := (typed.growDynstr lib).1.dynstr) (typed.growDynstr lib).1.dynsym) (ds := (typed.growDynstr lib).1.dynstr) (some td)) (typed.growDynstr lib).1.versym) (typed.growDynstr lib).1.sysvHash) (typed.growDynstr lib).1.gnuHash) (typed.growDynstr lib).1.verneed).sections[iDyn]'hbN).content = .dynamic dynN)
    {dsN : StringTable}
    (hDsN : (applyVerneed (applyGnuHash (applySysvHash (applyVersym (applyDynamic (applyDynsym (applyDynstr template (typed.growDynstr lib).1.dynstr) (ds := (typed.growDynstr lib).1.dynstr) (typed.growDynstr lib).1.dynsym) (ds := (typed.growDynstr lib).1.dynstr) (some td)) (typed.growDynstr lib).1.versym) (typed.growDynstr lib).1.sysvHash) (typed.growDynstr lib).1.gnuHash) (typed.growDynstr lib).1.verneed).dynstr = some dsN)
    (hInterpNe : ∀ i, (applyVerneed (applyGnuHash (applySysvHash (applyVersym (applyDynamic (applyDynsym (applyDynstr template (typed.growDynstr lib).1.dynstr) (ds := (typed.growDynstr lib).1.dynstr) (typed.growDynstr lib).1.dynsym) (ds := (typed.growDynstr lib).1.dynstr) (some td)) (typed.growDynstr lib).1.versym) (typed.growDynstr lib).1.sysvHash) (typed.growDynstr lib).1.gnuHash) (typed.growDynstr lib).1.verneed).interpIdx = some i → i ≠ iDyn)
    (hLt : iDyn < (toElfFile template (addNeeded typed lib h)).sections.size) :
    ((toElfFile template (addNeeded typed lib h)).sections[iDyn]'hLt).content
      = .dynamic (patchDynamicEntries bd (td.pushNeeded (typed.dynstr.appendOffset lib))) := by
  have hFactor := toElfFile_addNeeded_factor template typed lib h td hTd iDyn hIdx0 bd hByte0
    hbN dynN hContentN hDsN hInterpNe
  rw [ElfFile.getElem_content_congr _ _ iDyn hFactor hLt]
  exact ElfFile.updateSectionContent_content_self _ iDyn _ _

/-! ### `modifyRPath .set` / `modifySoname .set` two-field factorings

    Same `growDynstrDynamicOp` shape as `addNeeded` (only the monomorphic `g`
    differs: `setRpathTag fr off` / `setSonameOff off`), so each factors through
    `toElfFile_dynamicMapMono_factor` at zero new proof cost. -/

theorem modifyRPath_set_eq_dynamicMapMono (typed : ValidElfFile) (fr : Bool) (newRpath : String)
    (h : typed.dynamic.isSome) :
    modifyRPath typed fr .set newRpath h
      = { (typed.growDynstr newRpath).1 with
            dynamic := (typed.growDynstr newRpath).1.dynamic.map
              (fun d => d.setRpathTag fr (typed.dynstr.appendOffset newRpath)) } := rfl

theorem modifySoname_set_eq_dynamicMapMono (typed : ValidElfFile) (newName : String)
    (h : typed.dynamic.isSome) :
    modifySoname typed .set newName h
      = { (typed.growDynstr newName).1 with
            dynamic := (typed.growDynstr newName).1.dynamic.map
              (fun d => d.setSonameOff (typed.dynstr.appendOffset newName)) } := rfl

theorem toElfFile_modifyRPath_set_factor (template : ElfFile) (typed : ValidElfFile)
    (fr : Bool) (newRpath : String) (h : typed.dynamic.isSome)
    (td : DynamicSection (typed.growDynstr newRpath).1.dynstr)
    (hTd : (typed.growDynstr newRpath).1.dynamic = some td)
    (iDyn : Nat)
    (hIdx0 : (applyDynsym (applyDynstr template (typed.growDynstr newRpath).1.dynstr) (ds := (typed.growDynstr newRpath).1.dynstr) (typed.growDynstr newRpath).1.dynsym).dynamicIdx = some iDyn)
    (bd : Array DynEntry)
    (hByte0 : (applyDynsym (applyDynstr template (typed.growDynstr newRpath).1.dynstr) (ds := (typed.growDynstr newRpath).1.dynstr) (typed.growDynstr newRpath).1.dynsym).dynamic = some bd)
    (hbN : iDyn < (applyVerneed (applyGnuHash (applySysvHash (applyVersym (applyDynamic (applyDynsym (applyDynstr template (typed.growDynstr newRpath).1.dynstr) (ds := (typed.growDynstr newRpath).1.dynstr) (typed.growDynstr newRpath).1.dynsym) (ds := (typed.growDynstr newRpath).1.dynstr) (some td)) (typed.growDynstr newRpath).1.versym) (typed.growDynstr newRpath).1.sysvHash) (typed.growDynstr newRpath).1.gnuHash) (typed.growDynstr newRpath).1.verneed).sections.size)
    (dynN : Array DynEntry)
    (hContentN : ((applyVerneed (applyGnuHash (applySysvHash (applyVersym (applyDynamic (applyDynsym (applyDynstr template (typed.growDynstr newRpath).1.dynstr) (ds := (typed.growDynstr newRpath).1.dynstr) (typed.growDynstr newRpath).1.dynsym) (ds := (typed.growDynstr newRpath).1.dynstr) (some td)) (typed.growDynstr newRpath).1.versym) (typed.growDynstr newRpath).1.sysvHash) (typed.growDynstr newRpath).1.gnuHash) (typed.growDynstr newRpath).1.verneed).sections[iDyn]'hbN).content = .dynamic dynN)
    {dsN : StringTable}
    (hDsN : (applyVerneed (applyGnuHash (applySysvHash (applyVersym (applyDynamic (applyDynsym (applyDynstr template (typed.growDynstr newRpath).1.dynstr) (ds := (typed.growDynstr newRpath).1.dynstr) (typed.growDynstr newRpath).1.dynsym) (ds := (typed.growDynstr newRpath).1.dynstr) (some td)) (typed.growDynstr newRpath).1.versym) (typed.growDynstr newRpath).1.sysvHash) (typed.growDynstr newRpath).1.gnuHash) (typed.growDynstr newRpath).1.verneed).dynstr = some dsN)
    (hInterpNe : ∀ i, (applyVerneed (applyGnuHash (applySysvHash (applyVersym (applyDynamic (applyDynsym (applyDynstr template (typed.growDynstr newRpath).1.dynstr) (ds := (typed.growDynstr newRpath).1.dynstr) (typed.growDynstr newRpath).1.dynsym) (ds := (typed.growDynstr newRpath).1.dynstr) (some td)) (typed.growDynstr newRpath).1.versym) (typed.growDynstr newRpath).1.sysvHash) (typed.growDynstr newRpath).1.gnuHash) (typed.growDynstr newRpath).1.verneed).interpIdx = some i → i ≠ iDyn) :
    toElfFile template (modifyRPath typed fr .set newRpath h)
      = (toElfFile template (typed.growDynstr newRpath).1).updateSectionContent iDyn
          (.dynamic (patchDynamicEntries bd (td.setRpathTag fr (typed.dynstr.appendOffset newRpath)))) := by
  rw [modifyRPath_set_eq_dynamicMapMono]
  exact toElfFile_dynamicMapMono_factor template (typed.growDynstr newRpath).1
    (fun d => d.setRpathTag fr (typed.dynstr.appendOffset newRpath)) td hTd iDyn hIdx0 bd hByte0 hbN dynN hContentN hDsN hInterpNe

theorem toElfFile_modifySoname_set_factor (template : ElfFile) (typed : ValidElfFile)
    (newName : String) (h : typed.dynamic.isSome)
    (td : DynamicSection (typed.growDynstr newName).1.dynstr)
    (hTd : (typed.growDynstr newName).1.dynamic = some td)
    (iDyn : Nat)
    (hIdx0 : (applyDynsym (applyDynstr template (typed.growDynstr newName).1.dynstr) (ds := (typed.growDynstr newName).1.dynstr) (typed.growDynstr newName).1.dynsym).dynamicIdx = some iDyn)
    (bd : Array DynEntry)
    (hByte0 : (applyDynsym (applyDynstr template (typed.growDynstr newName).1.dynstr) (ds := (typed.growDynstr newName).1.dynstr) (typed.growDynstr newName).1.dynsym).dynamic = some bd)
    (hbN : iDyn < (applyVerneed (applyGnuHash (applySysvHash (applyVersym (applyDynamic (applyDynsym (applyDynstr template (typed.growDynstr newName).1.dynstr) (ds := (typed.growDynstr newName).1.dynstr) (typed.growDynstr newName).1.dynsym) (ds := (typed.growDynstr newName).1.dynstr) (some td)) (typed.growDynstr newName).1.versym) (typed.growDynstr newName).1.sysvHash) (typed.growDynstr newName).1.gnuHash) (typed.growDynstr newName).1.verneed).sections.size)
    (dynN : Array DynEntry)
    (hContentN : ((applyVerneed (applyGnuHash (applySysvHash (applyVersym (applyDynamic (applyDynsym (applyDynstr template (typed.growDynstr newName).1.dynstr) (ds := (typed.growDynstr newName).1.dynstr) (typed.growDynstr newName).1.dynsym) (ds := (typed.growDynstr newName).1.dynstr) (some td)) (typed.growDynstr newName).1.versym) (typed.growDynstr newName).1.sysvHash) (typed.growDynstr newName).1.gnuHash) (typed.growDynstr newName).1.verneed).sections[iDyn]'hbN).content = .dynamic dynN)
    {dsN : StringTable}
    (hDsN : (applyVerneed (applyGnuHash (applySysvHash (applyVersym (applyDynamic (applyDynsym (applyDynstr template (typed.growDynstr newName).1.dynstr) (ds := (typed.growDynstr newName).1.dynstr) (typed.growDynstr newName).1.dynsym) (ds := (typed.growDynstr newName).1.dynstr) (some td)) (typed.growDynstr newName).1.versym) (typed.growDynstr newName).1.sysvHash) (typed.growDynstr newName).1.gnuHash) (typed.growDynstr newName).1.verneed).dynstr = some dsN)
    (hInterpNe : ∀ i, (applyVerneed (applyGnuHash (applySysvHash (applyVersym (applyDynamic (applyDynsym (applyDynstr template (typed.growDynstr newName).1.dynstr) (ds := (typed.growDynstr newName).1.dynstr) (typed.growDynstr newName).1.dynsym) (ds := (typed.growDynstr newName).1.dynstr) (some td)) (typed.growDynstr newName).1.versym) (typed.growDynstr newName).1.sysvHash) (typed.growDynstr newName).1.gnuHash) (typed.growDynstr newName).1.verneed).interpIdx = some i → i ≠ iDyn) :
    toElfFile template (modifySoname typed .set newName h)
      = (toElfFile template (typed.growDynstr newName).1).updateSectionContent iDyn
          (.dynamic (patchDynamicEntries bd (td.setSonameOff (typed.dynstr.appendOffset newName)))) := by
  rw [modifySoname_set_eq_dynamicMapMono]
  exact toElfFile_dynamicMapMono_factor template (typed.growDynstr newName).1
    (fun d => d.setSonameOff (typed.dynstr.appendOffset newName)) td hTd iDyn hIdx0 bd hByte0 hbN dynN hContentN hDsN hInterpNe

/-! ## §B — `addNeeded` Tier-D round-trip (the priority capstone)

    A grow op widens a section, so `eo`'s per-section disjointness BREAKS; the
    grow-tolerant driver `tierD_roundtrip_of_grown_eo` routes through the layout
    pass, hypothesizing only the NORMALIZED form's `spliceRegionsDisjoint`
    (`hSplice`).  Every other `EncodePreconditions` field is derived from `eo` via
    the existing `*_normalized_of_eo` helpers (inside the driver).  Caliber:
    identical to the landed `addDebugTag` / `noDefaultLib` grow capstones. -/

/-- Tier-D byte round-trip for `addNeeded`.  Instantiates
    `tierD_roundtrip_of_grown_eo` on `eo := toElfFile template (addNeeded typed
    lib h)`; the conclusion is the REAL `addNeeded`'s
    `parse (encode eo) = .ok ⟨prepLayoutForEncode (syncDtStrszInFile eo), …⟩`. -/
theorem toElfFile_addNeeded_tierD_roundtrip_derived (template : ElfFile) (typed : ValidElfFile)
    (lib : String) (h : typed.dynamic.isSome)
    (hVal : (toElfFile template (addNeeded typed lib h)).IsValid)
    (hPhdrFit : ((toElfFile template (addNeeded typed lib h)).phdrs.size + 1) < UInt16.size)
    {ds : StringTable} (hDs : (toElfFile template (addNeeded typed lib h)).dynstr = some ds)
    (hFit : ds.bytes.size < UInt64.size)
    (hSplice : (prepLayoutForEncode (syncDtStrszInFile (toElfFile template (addNeeded typed lib h)))).spliceRegionsDisjoint)
    (hIdentEo : IdentBytesValid (toElfFile template (addNeeded typed lib h)))
    (hSizeFitEo : ∀ (i : Nat) (hi : i < (toElfFile template (addNeeded typed lib h)).sections.size),
      ((toElfFile template (addNeeded typed lib h)).sections[i]'hi).shdrSize < UInt64.size)
    (hNullEmptyEo : ∀ (i : Nat) (hi : i < (toElfFile template (addNeeded typed lib h)).sections.size),
      ((toElfFile template (addNeeded typed lib h)).sections[i]'hi).type = ShType.SHT_NULL →
      ∃ ty hOk bs, ((toElfFile template (addNeeded typed lib h)).sections[i]'hi).content = .raw ty hOk bs ∧ bs.size = 0)
    (hHdrEntryEo : (toElfFile template (addNeeded typed lib h)).header.entry.val < UInt64.size)
    (hHdrPhoff : (prepLayoutForEncode (syncDtStrszInFile (toElfFile template (addNeeded typed lib h)))).header.phoff.val < UInt64.size)
    (hHdrShoff : (prepLayoutForEncode (syncDtStrszInFile (toElfFile template (addNeeded typed lib h)))).header.shoff.val < UInt64.size)
    (hPhdrFitEn : ∀ (i : Nat) (hi : i < (prepLayoutForEncode (syncDtStrszInFile (toElfFile template (addNeeded typed lib h)))).phdrs.size),
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (addNeeded typed lib h)))).phdrs[i]'hi).offset.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (addNeeded typed lib h)))).phdrs[i]'hi).vaddr.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (addNeeded typed lib h)))).phdrs[i]'hi).paddr.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (addNeeded typed lib h)))).phdrs[i]'hi).filesz.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (addNeeded typed lib h)))).phdrs[i]'hi).memsz.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (addNeeded typed lib h)))).phdrs[i]'hi).align.val < UInt64.size)
    (hShdrFitEn : ∀ (i : Nat) (hi : i < (prepLayoutForEncode (syncDtStrszInFile (toElfFile template (addNeeded typed lib h)))).sections.size),
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (addNeeded typed lib h)))).sections[i]'hi).addr.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (addNeeded typed lib h)))).sections[i]'hi).offset.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (addNeeded typed lib h)))).sections[i]'hi).addralign.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (addNeeded typed lib h)))).sections[i]'hi).entsize.val < UInt64.size) :
    parse (encode (toElfFile template (addNeeded typed lib h)))
      = .ok ⟨prepLayoutForEncode (syncDtStrszInFile (toElfFile template (addNeeded typed lib h))),
             prepLayout_syncDtStrsz_preserves_valid _ hVal hPhdrFit hDs⟩ :=
  tierD_roundtrip_of_grown_eo (toElfFile template (addNeeded typed lib h))
    hVal hPhdrFit hDs hFit hSplice hIdentEo hSizeFitEo hNullEmptyEo hHdrEntryEo
    hHdrPhoff hHdrShoff hPhdrFitEn hShdrFitEn

/-! ## §C — Tier-D round-trips for `modifyRPath .set` / `modifySoname .set`

    The other two `growDynstrDynamicOp` ops; identical caliber to `addNeeded`. -/

/-- Tier-D byte round-trip for `modifyRPath .set` (see the `addNeeded` capstone). -/
theorem toElfFile_modifyRPath_set_tierD_roundtrip_derived (template : ElfFile) (typed : ValidElfFile)
    (fr : Bool) (newRpath : String) (h : typed.dynamic.isSome)
    (hVal : (toElfFile template (modifyRPath typed fr .set newRpath h)).IsValid)
    (hPhdrFit : ((toElfFile template (modifyRPath typed fr .set newRpath h)).phdrs.size + 1) < UInt16.size)
    {ds : StringTable} (hDs : (toElfFile template (modifyRPath typed fr .set newRpath h)).dynstr = some ds)
    (hFit : ds.bytes.size < UInt64.size)
    (hSplice : (prepLayoutForEncode (syncDtStrszInFile (toElfFile template (modifyRPath typed fr .set newRpath h)))).spliceRegionsDisjoint)
    (hIdentEo : IdentBytesValid (toElfFile template (modifyRPath typed fr .set newRpath h)))
    (hSizeFitEo : ∀ (i : Nat) (hi : i < (toElfFile template (modifyRPath typed fr .set newRpath h)).sections.size),
      ((toElfFile template (modifyRPath typed fr .set newRpath h)).sections[i]'hi).shdrSize < UInt64.size)
    (hNullEmptyEo : ∀ (i : Nat) (hi : i < (toElfFile template (modifyRPath typed fr .set newRpath h)).sections.size),
      ((toElfFile template (modifyRPath typed fr .set newRpath h)).sections[i]'hi).type = ShType.SHT_NULL →
      ∃ ty hOk bs, ((toElfFile template (modifyRPath typed fr .set newRpath h)).sections[i]'hi).content = .raw ty hOk bs ∧ bs.size = 0)
    (hHdrEntryEo : (toElfFile template (modifyRPath typed fr .set newRpath h)).header.entry.val < UInt64.size)
    (hHdrPhoff : (prepLayoutForEncode (syncDtStrszInFile (toElfFile template (modifyRPath typed fr .set newRpath h)))).header.phoff.val < UInt64.size)
    (hHdrShoff : (prepLayoutForEncode (syncDtStrszInFile (toElfFile template (modifyRPath typed fr .set newRpath h)))).header.shoff.val < UInt64.size)
    (hPhdrFitEn : ∀ (i : Nat) (hi : i < (prepLayoutForEncode (syncDtStrszInFile (toElfFile template (modifyRPath typed fr .set newRpath h)))).phdrs.size),
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (modifyRPath typed fr .set newRpath h)))).phdrs[i]'hi).offset.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (modifyRPath typed fr .set newRpath h)))).phdrs[i]'hi).vaddr.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (modifyRPath typed fr .set newRpath h)))).phdrs[i]'hi).paddr.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (modifyRPath typed fr .set newRpath h)))).phdrs[i]'hi).filesz.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (modifyRPath typed fr .set newRpath h)))).phdrs[i]'hi).memsz.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (modifyRPath typed fr .set newRpath h)))).phdrs[i]'hi).align.val < UInt64.size)
    (hShdrFitEn : ∀ (i : Nat) (hi : i < (prepLayoutForEncode (syncDtStrszInFile (toElfFile template (modifyRPath typed fr .set newRpath h)))).sections.size),
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (modifyRPath typed fr .set newRpath h)))).sections[i]'hi).addr.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (modifyRPath typed fr .set newRpath h)))).sections[i]'hi).offset.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (modifyRPath typed fr .set newRpath h)))).sections[i]'hi).addralign.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (modifyRPath typed fr .set newRpath h)))).sections[i]'hi).entsize.val < UInt64.size) :
    parse (encode (toElfFile template (modifyRPath typed fr .set newRpath h)))
      = .ok ⟨prepLayoutForEncode (syncDtStrszInFile (toElfFile template (modifyRPath typed fr .set newRpath h))),
             prepLayout_syncDtStrsz_preserves_valid _ hVal hPhdrFit hDs⟩ :=
  tierD_roundtrip_of_grown_eo (toElfFile template (modifyRPath typed fr .set newRpath h))
    hVal hPhdrFit hDs hFit hSplice hIdentEo hSizeFitEo hNullEmptyEo hHdrEntryEo
    hHdrPhoff hHdrShoff hPhdrFitEn hShdrFitEn

/-- Tier-D byte round-trip for `modifySoname .set` (see the `addNeeded` capstone). -/
theorem toElfFile_modifySoname_set_tierD_roundtrip_derived (template : ElfFile) (typed : ValidElfFile)
    (newName : String) (h : typed.dynamic.isSome)
    (hVal : (toElfFile template (modifySoname typed .set newName h)).IsValid)
    (hPhdrFit : ((toElfFile template (modifySoname typed .set newName h)).phdrs.size + 1) < UInt16.size)
    {ds : StringTable} (hDs : (toElfFile template (modifySoname typed .set newName h)).dynstr = some ds)
    (hFit : ds.bytes.size < UInt64.size)
    (hSplice : (prepLayoutForEncode (syncDtStrszInFile (toElfFile template (modifySoname typed .set newName h)))).spliceRegionsDisjoint)
    (hIdentEo : IdentBytesValid (toElfFile template (modifySoname typed .set newName h)))
    (hSizeFitEo : ∀ (i : Nat) (hi : i < (toElfFile template (modifySoname typed .set newName h)).sections.size),
      ((toElfFile template (modifySoname typed .set newName h)).sections[i]'hi).shdrSize < UInt64.size)
    (hNullEmptyEo : ∀ (i : Nat) (hi : i < (toElfFile template (modifySoname typed .set newName h)).sections.size),
      ((toElfFile template (modifySoname typed .set newName h)).sections[i]'hi).type = ShType.SHT_NULL →
      ∃ ty hOk bs, ((toElfFile template (modifySoname typed .set newName h)).sections[i]'hi).content = .raw ty hOk bs ∧ bs.size = 0)
    (hHdrEntryEo : (toElfFile template (modifySoname typed .set newName h)).header.entry.val < UInt64.size)
    (hHdrPhoff : (prepLayoutForEncode (syncDtStrszInFile (toElfFile template (modifySoname typed .set newName h)))).header.phoff.val < UInt64.size)
    (hHdrShoff : (prepLayoutForEncode (syncDtStrszInFile (toElfFile template (modifySoname typed .set newName h)))).header.shoff.val < UInt64.size)
    (hPhdrFitEn : ∀ (i : Nat) (hi : i < (prepLayoutForEncode (syncDtStrszInFile (toElfFile template (modifySoname typed .set newName h)))).phdrs.size),
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (modifySoname typed .set newName h)))).phdrs[i]'hi).offset.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (modifySoname typed .set newName h)))).phdrs[i]'hi).vaddr.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (modifySoname typed .set newName h)))).phdrs[i]'hi).paddr.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (modifySoname typed .set newName h)))).phdrs[i]'hi).filesz.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (modifySoname typed .set newName h)))).phdrs[i]'hi).memsz.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (modifySoname typed .set newName h)))).phdrs[i]'hi).align.val < UInt64.size)
    (hShdrFitEn : ∀ (i : Nat) (hi : i < (prepLayoutForEncode (syncDtStrszInFile (toElfFile template (modifySoname typed .set newName h)))).sections.size),
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (modifySoname typed .set newName h)))).sections[i]'hi).addr.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (modifySoname typed .set newName h)))).sections[i]'hi).offset.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (modifySoname typed .set newName h)))).sections[i]'hi).addralign.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile (toElfFile template (modifySoname typed .set newName h)))).sections[i]'hi).entsize.val < UInt64.size) :
    parse (encode (toElfFile template (modifySoname typed .set newName h)))
      = .ok ⟨prepLayoutForEncode (syncDtStrszInFile (toElfFile template (modifySoname typed .set newName h))),
             prepLayout_syncDtStrsz_preserves_valid _ hVal hPhdrFit hDs⟩ :=
  tierD_roundtrip_of_grown_eo (toElfFile template (modifySoname typed .set newName h))
    hVal hPhdrFit hDs hFit hSplice hIdentEo hSizeFitEo hNullEmptyEo hHdrEntryEo
    hHdrPhoff hHdrShoff hPhdrFitEn hShdrFitEn

end Patchelf.Elf.Adapter
