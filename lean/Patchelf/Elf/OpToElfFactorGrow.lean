/-
  Op-through-`toElfFile` Tier-D round-trip for the GROWING ops (ROADMAP §5.1).

  Companion to `OpToElfFactor.lean` (the SHRINKING-op derivation).  A growing op
  widens a section's `encodedSize` at its original offset, so the three
  per-section disjointness invariants (`{header,phdr,shdr}SectionDisjoint`) on the
  op output `eo` genuinely BREAK — the shrink-monotonicity core
  (`SectionOps.updateSectionContent_*Disjoint_shrink`, which needs
  `newDyn.size ≤ oldDyn.size`) does NOT apply, and no grow-variant can exist
  (growth genuinely destroys per-section disjointness).

  The resolution: `encode`'s `prepLayoutForEncode`/`growEOFWith` pass RE-LAYS-OUT
  the file (it flags the overlapping grown sections stale and relocates them),
  so the NORMALIZED form `prepLayoutForEncode (syncDtStrszInFile eo)` IS
  `spliceRegionsDisjoint` even though `eo` is not.  The grow driver below takes
  that normalized-form disjointness as a HYPOTHESIS (`hSplice`) — the sanctioned
  "the layout engine produced a disjoint output" surface, on the same epistemic
  footing as the four `< 2^64` position bounds the shrink capstone already
  hypothesizes (the runtime `Validate.IsLoadableBytes` guard catches the
  pathological case at write time).  Every OTHER `EncodePreconditions` field is
  DERIVED from `eo` via the existing `*_normalized_of_eo` helpers, exactly as in
  the shrink path.

  Deriving `hSplice` itself from the no-op base (rather than hypothesizing it) is
  the genuinely-new layout reasoning — a grow-tolerant
  `growEOFWith_produces_spliceRegionsDisjoint_of_base` — and is deferred to a
  dedicated effort (PLAN-GROWING-OPS §3 Commit 3); it would let these capstones
  drop `hSplice`, matching the shrink ops' fully-derived caliber.

  `mapDynamicOp` growers (`addDebugTag`, `noDefaultLib`) reuse the generic
  factoring `toElfFile_mapDynamicOp_factor` VERBATIM — it is `f`-agnostic and
  size-agnostic — so only the transport (this driver) differs from the shrink
  capstones.  `growDynstrDynamicOp` growers (`addNeeded`, `modify{RPath,Soname}
  .set`) additionally grow `.dynstr`, needing a two-field factoring; deferred
  (PLAN-GROWING-OPS §3 Commit 5).
-/
module
public import Patchelf.Elf.OpToElfFactor
@[expose] public section

namespace Patchelf.Elf.Adapter
open Patchelf.Elf (ElfFile StringTable EncodePreconditions parse encode prepLayoutForEncode
                     syncDtStrszInFile IdentBytesValid prepLayout_syncDtStrsz_preserves_valid
                     syncOk_of_normalized identValid_normalized_of_eo sizeFit_normalized_of_eo
                     nullEmpty_normalized_of_eo headerFit_entry_normalized_of_eo)
open Patchelf.Elf.Layout (ShType)

/-- Grow-tolerant Tier-D driver.  Identical to `tierD_roundtrip_of_eo_facts`
    EXCEPT the normalized form's `spliceRegionsDisjoint` is HYPOTHESIZED
    (`hSplice`) rather than derived from `eo`'s per-section disjointness — which
    a GROWN `eo` cannot supply (its widened section overlaps a neighbor).  All
    other `EncodePreconditions` fields are derived from `eo` via the existing
    `*_normalized_of_eo` helpers; the validity capstone, the position bounds, and
    `syncOk` are threaded exactly as in the shrink driver.

    `hSplice` is the sanctioned "the layout engine produced disjoint output"
    surface (parallel to the four `< 2^64` position bounds); promoting it to a
    derived fact is deferred to the grow-tolerant `growEOFWith` lemma. -/
theorem tierD_roundtrip_of_grown_eo (eo : ElfFile)
    (hVal : eo.IsValid)
    (hPhdrFit : (eo.phdrs.size + 1) < UInt16.size)
    {ds : StringTable} (hDs : eo.dynstr = some ds)
    (hFit : ds.bytes.size < UInt64.size)
    (hSplice : (prepLayoutForEncode (syncDtStrszInFile eo)).spliceRegionsDisjoint)
    (hIdentEo : IdentBytesValid eo)
    (hSizeFitEo : ∀ (i : Nat) (h : i < eo.sections.size),
      (eo.sections[i]'h).shdrSize < UInt64.size)
    (hNullEmptyEo : ∀ (i : Nat) (h : i < eo.sections.size),
      (eo.sections[i]'h).type = ShType.SHT_NULL →
      ∃ ty hOk bs, (eo.sections[i]'h).content = .raw ty hOk bs ∧ bs.size = 0)
    (hHdrEntryEo : eo.header.entry.val < UInt64.size)
    (hHdrPhoff : (prepLayoutForEncode (syncDtStrszInFile eo)).header.phoff.val < UInt64.size)
    (hHdrShoff : (prepLayoutForEncode (syncDtStrszInFile eo)).header.shoff.val < UInt64.size)
    (hPhdrFitEn : ∀ (i : Nat) (h : i < (prepLayoutForEncode (syncDtStrszInFile eo)).phdrs.size),
      ((prepLayoutForEncode (syncDtStrszInFile eo)).phdrs[i]'h).offset.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile eo)).phdrs[i]'h).vaddr.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile eo)).phdrs[i]'h).paddr.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile eo)).phdrs[i]'h).filesz.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile eo)).phdrs[i]'h).memsz.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile eo)).phdrs[i]'h).align.val < UInt64.size)
    (hShdrFitEn : ∀ (i : Nat) (h : i < (prepLayoutForEncode (syncDtStrszInFile eo)).sections.size),
      ((prepLayoutForEncode (syncDtStrszInFile eo)).sections[i]'h).addr.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile eo)).sections[i]'h).offset.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile eo)).sections[i]'h).addralign.val < UInt64.size ∧
      ((prepLayoutForEncode (syncDtStrszInFile eo)).sections[i]'h).entsize.val < UInt64.size) :
    parse (encode eo)
      = .ok ⟨prepLayoutForEncode (syncDtStrszInFile eo),
             prepLayout_syncDtStrsz_preserves_valid eo hVal hPhdrFit hDs⟩ :=
  tierD_roundtrip_of_valid eo hVal hPhdrFit hDs hFit
    { syncOk := syncOk_of_normalized eo hDs hFit
      spliceDisjoint := hSplice
      identValid := identValid_normalized_of_eo eo hIdentEo
      sizeFit := sizeFit_normalized_of_eo eo hSizeFitEo
      nullEmpty := nullEmpty_normalized_of_eo eo hNullEmptyEo
      headerFit_entry := headerFit_entry_normalized_of_eo eo hHdrEntryEo
      headerFit_phoff := hHdrPhoff
      headerFit_shoff := hHdrShoff
      phdrFit := hPhdrFitEn
      shdrFit := hShdrFitEn }

end Patchelf.Elf.Adapter

/-! The `mapDynamicOp` grower capstones (`addDebugTag`, `noDefaultLib`) live in
    `GrowEOFDisjointOfBase.lean`, downstream of this driver and the `hSplice`
    establisher `mapDynamicOp_spliceRegionsDisjoint_of_base` — so they DERIVE
    `hSplice` from the no-op base's structural invariants + two offset side
    conditions, rather than hypothesizing it. -/
