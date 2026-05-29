# Plan: Tier-D for the GROWING ops (`growEOFWith` transport)

Design plan only — NOT an implementation. Author was **READ-ONLY** on all
code and did **NOT** run `lake build` (a concurrent agent owns the build dir).
Every load-bearing claim is tagged with its `file:line` source; claims that
could not be confirmed by reading (i.e. would need a compile to verify a
tactic actually closes) are marked `[NEEDS COMPILE-VERIFICATION]`.

This is the GROWING-op companion to the just-landed SHRINKING-op derivation
(`research/PLAN-OPTOELFFACTOR-REFACTOR.md`, code in
`lean/Patchelf/Elf/OpToElfFactor.lean`). Read that plan first for house style
and the shrink template this contrasts against.

Baseline (from `lean/STATUS.md`): the four shrinking ops
(`removeRpath`/`modifyRPath.remove`/`removeNeeded`/`modifySoname.remove`) have
their `eo`-structural invariants DERIVED via the generic `mapDynamicOp f`
machinery; §1.2 `_preserves_loadable` ladder is complete through the full
encoder pipeline; Tier-D drivers `tierD_roundtrip{,_of_valid,_of_eo_facts}`
are in place. NO growing op has any Tier-D theorem yet (confirmed: grep for
`addNeeded_tierD`/`addDebugTag_tierD`/`noDefaultLib_tierD` returns nothing).

---

## 0. Verified ground truth (read the source)

### 0.1 The growing ops and their exact dynstr/dynamic effect

| Op | combinator | `f` / mutator | dynstr effect | `.dynamic`-entry-count effect | source |
|---|---|---|---|---|---|
| `addDebugTag` | `mapDynamicOp` | `(·.addDebugTag)` | **UNCHANGED** | **+0 or +1** (append DT_DEBUG iff absent) | `Ops/AddDebugTag.lean:16-17` |
| `noDefaultLib` | `mapDynamicOp` | `(·.setNoDefaultLib)` | **UNCHANGED** | **+0 or +1** (append DT_FLAGS_1 iff absent) | `Ops/NoDefaultLib.lean:19-20` |
| `modifyRPath .set` | `growDynstrDynamicOp` | `(·.setRpathTag forceRpath off)` | **GROWS** (append `newRpath`) | +0 or +1 (sets rpath/runpath slot; entry added iff no slot existed) | `Ops/Rpath.lean:22-27` |
| `modifySoname .set` | `growDynstrDynamicOp` | `(·.setSonameOff off)` | **GROWS** (append `newName`) | +0 or +1 | `Ops/Soname.lean:27-31` |
| `addNeeded` | `growDynstrDynamicOp` | `(fun _ off d => d.pushNeeded off)` | **GROWS** (append `lib`) | **+1** (prepend a DT_NEEDED) | `Ops/AddNeeded.lean:21-23` |
| `replaceNeeded` (grow path) | bespoke record literal | `replaceNeededBy` + `rewriteVnFile` | **GROWS** (append `newName`) | +0 (same count; rewrites offsets) but **dynstr grows** | `Ops/ReplaceNeeded.lean:57-67` |

Key combinator facts:

* `mapDynamicOp e f = { e with dynamic := e.dynamic.map f }`
  (`ObservableCombinators.lean:104-108`) — changes ONLY `.dynamic`; dynstr
  identical. This is the SAME combinator the shrinking ops use, so
  `toElfFile_mapDynamicOp_factor` applies VERBATIM (see §3).
* `growDynstrDynamicOp e name f` (`ObservableCombinators.lean:48-55`):
  `let p := e.growDynstr name; { p.1 with dynamic := p.1.dynamic.map (f _ p.2) }`.
  So it FIRST replaces `dynstr` with a strictly larger `StringSection` (and
  rebases `dynsym`/`dynamic`), THEN maps `f` over `.dynamic`.
* `ValidElfFile.growDynstr e s` (`ValidElfFile.lean:97-112`): produces a new
  `ValidElfFile` whose `.dynstr := (e.dynstr.append s).1` (larger), with
  `dynsym`/`dynamic` rebased via `(·.rebase h)` and all other fields copied.
  Returns the appended offset as the second component.

### 0.2 Why the dynstr section's byte size genuinely grows

`Section.encodedSize` for `.strtab st` content is `st.bytes.size`
(`ElfFile.lean:129-133`). `growDynstr` enlarges `dynstr.bytes`, so the
`.dynstr` section's `encodedSize` strictly grows. `applyDynstr e ds` writes
`.strtab ⟨ds.bytes⟩` at `e.dynstrIdx` (`Adapter.lean:808-811`). Hence for a
`growDynstrDynamicOp`-based op, the `toElfFile` output differs from the no-op
output in **two** section contents: the `.dynstr` section (bigger) AND the
`.dynamic` section (rewritten, possibly bigger).

### 0.3 Why `mapDynamicOp` growers (`addDebugTag`/`noDefaultLib`) widen `.dynamic` by ≤1

`patchDynamicEntries byteDyn typed` (`Adapter.lean:351-…`) = a `foldl patchStep`
producing `st`, then `appendSurplusNeeded`, then **five `appendUnless` blocks**
(flags1, debug, rpath, runpath, soname), then a final null push. The
`appendUnless` block appends an entry iff the field was NOT applied in the loop
and `typed.<field>` is `some` (`Adapter.lean:344-349`). `addDebugTag` sets
`debug := some 0` when absent (`DynamicSection.lean:117-120`); `setNoDefaultLib`
sets `flags1 := some (… ||| 0x800)` (always `some`, `DynamicSection.lean:125-126`).
So `f td` differs from `td` only by turning ONE `none` field `some` (or leaving
it). The matching `appendUnless` block therefore appends 0 or 1 more entry. The
existing `appendUnless_size_le : (appendUnless …).size ≤ result.size + 1`
(`Adapter.lean:457-463`) is the building block for the per-op +1 bound (§3.1).

### 0.4 The shrink-monotonicity core requires `newDyn.size ≤ oldDyn.size`

`SectionOps.lean:474-551`: `updateSectionContent_sectionInterval_shrink` and
its three specializations (`_headerSectionDisjoint_shrink`,
`_phdrSectionDisjoint_shrink`, `_shdrSectionDisjoint_shrink`) all take
`hShrink : newDyn.size ≤ oldDyn.size`. The proof's core step
(`SectionOps.lean:503-511`) uses `IntervalDisjoint_shrink_right` — disjointness
of `[off, off+s)` from a fixed interval is preserved only when shrinking `s`.
**When the section grows, a wider `[off, off+s')` can reach into a neighbor →
disjointness BREAKS.** There is NO grow-variant of these lemmas (confirmed:
grep `Disjoint_grow`/`sectionInterval_grow` returns nothing). `_section0Null`
(`SectionOps.lean:555-572`) is the lone size-free survivor — it only needs that
the `.dynamic` index ≠ 0, which holds regardless of size.

---

## 1. The core obstacle (the crux)

### 1.1 Which structural invariants survive growth, which break

For the op output `eo := toElfFile template (op typed)` of a growing op, the
six `spliceRegionsDisjoint` clauses (defs at `ElfFile.lean:625-685`) split:

**SURVIVE (size-independent — depend only on `header.{phoff,shoff}`,
`phdrs.size`, `sections.size`, none of which a typed-layer
dynstr/dynamic-content edit changes):**

* `headerPhdrDisjoint` (`ElfFile.lean:625-628`) — `[0,ehdr)` vs
  `[phoff, phoff + phdrs.size·phdrSize)`.
* `headerShdrDisjoint` (`ElfFile.lean:634-637`) — `[0,ehdr)` vs the shdr table.
* `phdrShdrDisjoint` (`ElfFile.lean:643-646`) — phdr table vs shdr table.

These transport through `updateSectionContent` already, via
`updateSectionContent_{headerPhdr,headerShdr,phdrShdr}Disjoint`
(`SectionOps.lean:442-462`) — which have NO shrink hypothesis. So even after the
two content edits, these three hold on `eo` whenever they hold on the no-op
output. (`toElfFile … typed`'s header/phdr equal `typed.header`/`typed.phdrs`
by `rfl`, `Adapter.lean:860-867`.)

**BREAK (read each section's `[offset, offset + encodedSize)`):**

* `headerSectionDisjoint` (`ElfFile.lean:652-658`)
* `phdrSectionDisjoint` (`ElfFile.lean:664-670`)
* `shdrSectionDisjoint` (`ElfFile.lean:676-682`)

The grown `.dynamic` section (and, for `growDynstr` ops, the grown `.dynstr`
section) keeps its ORIGINAL `offset` but has a larger `encodedSize`, so its file
range `[off, off+encodedSize)` can now overlap a neighbor section, the phdr
table, or the shdr table. **These three are exactly what the shrink lemmas
deliver and exactly what a grower cannot establish on the un-laid-out `eo`.**

(`sectionsNonOverlapping`, the 7th `spliceRegionsDisjoint` clause, likewise
breaks; it is supplied by `IsLoadable` in the driver chain — see §1.3.)

### 1.2 The resolution: `prepLayoutForEncode` ESTABLISHES disjointness; it is
### not required as input on `eo`

The decisive observation, from reading the existing Tier-D driver chain:
**`tierD_roundtrip_of_eo_facts` already does NOT require `eo` to be
`spliceRegionsDisjoint`.** It requires the six structural input invariants on
`eo` and feeds them to `prepLayoutForEncode`, which runs `growEOFWith` to
RE-LAY-OUT the file and PRODUCE disjointness on the *output*. Trace
(`OpAdapterPreservation.lean`):

* `tierD_roundtrip_of_eo_facts eo …` (`:411-446`) takes
  `hS0/hHP/hHS/hPS/hHSec/hPSec` on `eo`, then calls
  `encodePreconditions_of_layoutNormalized`.
* `encodePreconditions_of_layoutNormalized` (`:304-348`) discharges the
  `spliceDisjoint` field via `spliceRegionsDisjoint_of_structural_eo`
  (`:259-271`), which transports the 6 invariants through `syncDtStrszInFile`
  then hands them to `prepLayoutForEncode_produces_spliceRegionsDisjoint`
  (`Encoder.lean:949-959`).
* `prepLayoutForEncode_produces_spliceRegionsDisjoint` → (non-fast-path)
  `growEOFWith_produces_spliceRegionsDisjoint`
  (`GrowEOF.lean:4088-4141`), whose own preconditions are EXACTLY the six
  structural input invariants — i.e. `growEOFWith` consumes the *input's*
  disjointness facts and emits the *output's* full `spliceRegionsDisjoint`.

**But this is the catch that makes the growers genuinely harder than a
re-parameterization:** `growEOFWith_produces_spliceRegionsDisjoint` ALSO takes
`hHeaderSec`/`hPhdrSec` (and `prepLayoutForEncode_produces` adds nothing) as
*inputs* (`GrowEOF.lean:4094-4095`). I.e. the current "produces disjoint"
theorem assumes the per-section disjointness ALREADY HOLDS on its input and only
re-establishes `sectionsNonOverlapping` + `shdrSectionDisjoint` (the two clauses
`layoutAlreadyValid` would have rejected). **So routing a grown `eo` through the
existing `tierD_roundtrip_of_eo_facts` does NOT work: you cannot supply
`hHSec`/`hPSec` for the grown `eo`.** This is the precise gap. `[NEEDS
COMPILE-VERIFICATION — confirm growEOFWith_produces actually needs hHeaderSec/
hPhdrSec on its input by reading GrowEOF.lean:4118-4141 branch leaves; they are
in the signature, so this is high-confidence]`

### 1.3 The driver-signature question (hard question #2)

So the answer is **(a) a NEW driver is needed.** The existing
`tierD_roundtrip_of_eo_facts` requires `eo`'s per-section disjointness, which a
grown `eo` lacks. Two candidate driver shapes, in increasing order of how much
new layout reasoning they demand:

**Option A (preferred — reuse the loadable ladder, route through `growEOFWith`
deriving disjointness from a STRONGER per-section input that DOES survive):**

The `growEOFWith` branch theorems do not in fact need the *full* per-section
disjointness of the grown file — they need enough to run their stale-detection
and placement. But the packaged top-level theorem demands `hHeaderSec`/`hPhdrSec`.
The cleanest NEW driver therefore reuses the §1.2 *loadable* ladder, which has a
DIFFERENT and weaker structural surface. Inspect
`prepLayout_syncDtStrsz_preserves_loadable` (`Encoder.lean:1026-1045`): it takes
`hLoad : eo.IsLoadable`, `hPhdrFit`, `hSection0Null`, `hHeaderPhdr`,
`hHeaderSec`, `hPhdrSec`, `hDs`. So it ALSO consumes `hHeaderSec`/`hPhdrSec` on
`eo` — same wall. **Therefore neither the validity nor the loadable ladder, as
currently stated, lets a grown `eo` through without per-section disjointness.**

This means the genuinely-new lemma the growers need is a
**`growEOFWith_produces_spliceRegionsDisjoint`-style theorem whose per-section
hypotheses are stated about a section array that has NOT yet been widened** —
i.e. the input invariants must be discharged on the no-op output
`base := toElfFile template typed` (which IS laid-out / parser-derivable) and
the theorem must tolerate the single grown `.dynamic` (and grown `.dynstr`)
section. Concretely, the new driver's signature would be roughly:

```lean
theorem tierD_roundtrip_of_grown_eo
    (eo : ElfFile)
    (hVal      : eo.IsValid)
    (hPhdrFit  : (eo.phdrs.size + 1) < UInt16.size)
    {ds : StringTable} (hDs : eo.dynstr = some ds) (hFit : ds.bytes.size < UInt64.size)
    -- header/phdr-table invariants (SURVIVE growth — established on eo directly):
    (hS0  : ∀ h, (eo.sections[0]'h).type = SHT_NULL)
    (hHP  : eo.headerPhdrDisjoint) (hHS : eo.headerShdrDisjoint) (hPS : eo.phdrShdrDisjoint)
    -- per-section disjointness is NO LONGER required on eo; instead the layout
    -- pass re-establishes it.  What replaces hHSec/hPSec is the obligation that
    -- growEOFWith's stale-detection moves the grown sections — see §1.4.
    …
    -- the same residual < 2^64 position bounds on the normalized form …
    : parse (encode eo) = .ok ⟨prepLayoutForEncode (syncDtStrszInFile eo), …⟩
```

`[NEEDS COMPILE-VERIFICATION]` — the exact replacement for `hHSec`/`hPSec` is
the open question (§1.4). The KEY reuse is the BODY: once
`(prepLayoutForEncode (syncDtStrszInFile eo)).spliceRegionsDisjoint` is
established by a new `growEOFWith`-side lemma, the rest is the EXISTING spine:
`encode_roundtrip_via_normalized` (`:227-233`) + `tierD_roundtrip`
(`:362-369`) + the residual `EncodePreconditions` fields — all of which are
`f`-agnostic and size-agnostic.

**Option B (heavier — prove a grow-tolerant `growEOFWith_produces` directly):**
state and prove a `growEOFWith_produces_spliceRegionsDisjoint_of_base` whose
per-section hypotheses are about `base` (the laid-out no-op) plus a witness that
`eo`'s sections equal `base`'s except at the grown indices. This is the honest
crux and likely ~the bulk of the growing-op work. See §3, Commit 3.

### 1.4 What actually has to be proven about `growEOFWith` on a grown file

`growEOFWith` (`GrowEOF.lean:987-1083`) fast-paths via `layoutAlreadyValid e`
(`:989`); a grown `eo` is NOT layout-valid (its grown section overlaps), so it
takes the non-fast path: detect stale sections (`sectionStale`,
`GrowEOF.lean:200-208`), append them to a fresh region (`appendStaleSections`),
extend the last PT_LOAD or add a fresh one. The grown `.dynamic`/`.dynstr`
sections WILL be flagged stale (their `[off, off+encodedSize')` overlaps a
neighbor), get relocated, and the output is disjoint by
`growEOFWith_produces_spliceRegionsDisjoint`'s conclusion. The NEW obligation is
purely about that theorem's INPUT hypotheses `hHeaderSec`/`hPhdrSec`: they must
be re-derived for the grown `eo`. Two sub-options:

* **(i)** Prove they still hold because a grown section that overlaps is caught
  by stale-detection and the header/phdr table themselves don't move — i.e.
  show `growEOFWith`'s output disjointness can be derived from `base`'s
  per-section disjointness + the grown-section deltas. This needs a new
  `growEOFWith` lemma. `[NEEDS COMPILE-VERIFICATION — feasibility]`
* **(ii)** Strengthen the precondition: supply the per-section disjointness as a
  hypothesis ON THE NORMALIZED/LAID-OUT form rather than on `eo` (the same
  "sanctioned file < 2^64 / well-laid-out" surface the shrink capstone already
  uses for the four position bounds). This keeps the proof tractable by stating
  the genuinely-hard layout fact as a hypothesis, exactly as the shrink capstone
  states `hHdrPhoff`/`hHdrShoff`/`hPhdrFitEn`/`hShdrFitEn` as hypotheses.
  Recommended FIRST cut. `[NEEDS COMPILE-VERIFICATION]`

---

## 2. What's reusable (exact names)

### 2.1 The generic factor — FREE for `mapDynamicOp` growers, no size assumption

`toElfFile_mapDynamicOp_factor` (`OpToElfFactor.lean:475-499`) factors
`toElfFile template (mapDynamicOp typed f)` as
`(toElfFile template typed).updateSectionContent iDyn (.dynamic (patchDynamicEntries bd (f td)))`
for an **arbitrary** `f : {ds} → DynamicSection ds → DynamicSection ds`. **Read
its signature: it assumes NOTHING about size** (no `hShrink`, no
`newDyn.size ≤ …`). The proof (`:490-499`) is the header/phdrs `rfl` bullets +
the sections bullet via `innerChain_factor_general` (`:452-469`) +
`updateSectionContent_sections_eq_of_sections`. None of these reference shrink.
So for `addDebugTag`/`noDefaultLib` the factoring is identical to the shrink
case — **only the transport changes** (you cannot use the `_shrink` transport;
see §3.1).

Supporting `f`-agnostic, size-agnostic lemmas that carry over verbatim:
`applyDynamic_factor_general` (`:442-448`), `innerChain_factor_general`
(`:452-469`), `outerChain_dynamic_comm` (`:373-392`), the per-type
`apply{Versym,SysvHash,GnuHash,Verneed}_{dynamic_comm,dynamicIdx,content_at}`
families, `toElfFile_content_at_dynamicIdx` (`:577-607`), and the
`RemoveRpathFactorData` bundle (`:610-631`, misnamed but already `f`-agnostic —
all fields describe the NO-OP chain).

### 2.2 The §1.2 ladders (the layout-move spine) — fully landed, the growers' engine

* `growEOFWith_produces_spliceRegionsDisjoint` (`GrowEOF.lean:4088-4141`) — the
  layout pass emits a 7-clause-disjoint output from the 6 input invariants. This
  is what RE-ESTABLISHES disjointness after growth (§1.2). **The growers' single
  most important reuse.**
* `growEOFWith_preserves_loadable` (`GrowEOF.lean:4210-4250`) +
  `growEOFWith_preserves_valid` (`:4158-4191`) — IsLoadable/IsValid survive the
  move; built on `updatePhdrsAfterMove_*` (`GrowEOF.lean:606-744`) and
  `retargetPtPhdr_*` (`:772-882`) per-phdr families.
* `prepLayoutForEncode_produces_spliceRegionsDisjoint` (`Encoder.lean:949-959`),
  `prepLayoutForEncodeWith_preserves_loadable` (`:976-996`),
  `prepLayout_syncDtStrsz_preserves_loadable` (`:1026-1045`),
  `prepLayout_syncDtStrsz_preserves_valid` (used by every Tier-D capstone).
* `growEOFWith_dynstr` / `growEOFWith_dynamic` (`GrowEOF.lean:4256-4313`) — the
  layout pass preserves both accessors (needed to thread `hDs` through, and for
  Obligation A).

### 2.3 The Tier-D drivers — size/`f`-agnostic spine reusable as-is

* `encode_roundtrip_via_normalized` (`OpAdapterPreservation.lean:227-233`) — the
  byte round-trip reduction to three obligations on the normalized form. No size
  or growth assumption.
* `tierD_roundtrip` (`:362-369`) and `tierD_roundtrip_of_valid` (`:390-400`) —
  glue obligations + the validity capstone. Reusable for growers once
  `EncodePreconditions` on the normalized form is assembled.
* `spliceRegionsDisjoint_of_structural{,_eo}` (`:241-271`),
  `encodePreconditions_of_layoutNormalized` (`:304-348`) — assemble
  `EncodePreconditions` from the 6 structural input invariants + residual
  bounds. **These already route disjointness through `prepLayoutForEncode`
  (i.e. they ESTABLISH it on the output) — the grower-friendly half.** The only
  blocker is that their `hHSec`/`hPSec` arguments are stated on `eo` (§1.3).
* `tierD_roundtrip_of_eo_facts` (`:411-446`) — the full eo-level driver. **Does
  NOT apply directly to growers** (its `hHSec`/`hPSec` are unprovable for a
  grown `eo`); it is the TEMPLATE for the new `tierD_roundtrip_of_grown_eo`.

### 2.4 The shrink transport — does NOT carry over

`mapDynamicOp_structural_transport` (`OpToElfFactor.lean:646-683`) and the
`SectionOps.updateSectionContent_*Disjoint_shrink` family (`SectionOps.lean:515-551`)
are the SHRINK-ONLY half. They consume `hSizeBound : (patch bd (f td)).size ≤
(patch bd td).size`, which is FALSE for growers. **This is the one block that
must be replaced** — by the new grow driver of §1.3, not by a new
`updateSectionContent_*Disjoint_grow` (which cannot exist — growth genuinely
breaks per-section disjointness; §0.4).

### 2.5 Size-bound helpers already present (for the +1 grower bound)

`appendUnless_size_le` (≤ result+1), `_ge` (≥ result), `_mono`, `_none`
(`Adapter.lean:457-487`); `appendSurplusNeeded_size_{mono,exact}` (`:445-`,
`:554-`); `Array.foldl_proj_size_le_add` (`:201-`). These support an
`addDebugTag`/`noDefaultLib` **upper** bound `(patch bd (f td)).size ≤
(patch bd td).size + 1` — note this is the OPPOSITE direction from the shrink
bound and is NOT consumed by any existing disjointness lemma (it would feed a
hypothetical grow-tolerant `growEOFWith` input fact, §1.4 / §3.1).

---

## 3. Commit plan (tiered, cheapest grower first)

Mirror the 5-commit shape of the OpToElfFactor plan: each commit builds + tests
green before the next; the cheapest grower (`addDebugTag`) lands first and
proves the new driver, then the others instantiate it. Branch is
`vibe-coding/pure-ir-migration` (NOT master).

### Commit 1 — the NEW grow driver `tierD_roundtrip_of_grown_eo` (the keystone)
**New file** `lean/Patchelf/Elf/OpToElfFactorGrow.lean` (sibling to
`OpToElfFactor.lean`; do NOT bloat the shrink file).

**Obligations:**
1. A grow-tolerant disjointness establisher. Per §1.4, take the FIRST CUT as
   sub-option (ii): state `tierD_roundtrip_of_grown_eo` taking
   `hS0`/`hHP`/`hHS`/`hPS` on `eo` (survive growth, §1.1) PLUS the per-section
   disjointness as hypotheses **on the normalized form**
   `prepLayoutForEncode (syncDtStrszInFile eo)` (the sanctioned "well-laid-out"
   surface, parallel to how the shrink capstone hypothesizes the four position
   bounds). Then the body is the EXISTING spine: build `EncodePreconditions`
   from `spliceRegionsDisjoint_of_structural` (fed the normalized-form
   per-section facts directly, BYPASSING the eo-level `_eo` wrapper that demands
   `hHSec`/`hPSec` on `eo`) + the residual fields, then
   `tierD_roundtrip_of_valid`. `[NEEDS COMPILE-VERIFICATION — that
   `spliceRegionsDisjoint_of_structural` (Encoder, on `syncDtStrszInFile eo`)
   can be satisfied without the eo-level transport; you may instead need to call
   `prepLayoutForEncode_produces_spliceRegionsDisjoint` with the no-op base's
   invariants — see Commit 3 for the honest version.]`
2. Thread `hVal`, `hDs`, `hFit`, `hPhdrFit` exactly as
   `tierD_roundtrip_of_eo_facts` does.

**Risk:** HIGH (this is the crux; the first-cut hypothesis surface may be wrong
and need Commit 3's honest layout lemma). **Verify:** build + `#print axioms`
(should be the standard `[propext, Classical.choice, Quot.sound]` + 3 bv_decide,
no `sorryAx`).

### Commit 2 — `addDebugTag` Tier-D (cheapest grower: `mapDynamicOp`, +≤1, no dynstr)
**Why cheapest:** uses `mapDynamicOp` (so `toElfFile_mapDynamicOp_factor`
applies FREE, §2.1), dynstr UNCHANGED (so only ONE section content differs from
the no-op — the `.dynamic` section), and the `.dynamic` array grows by ≤1.

**Obligations:**
1. The factoring is FREE: `toElfFile template (addDebugTag typed h) =
   (toElfFile template typed).updateSectionContent iDyn (.dynamic (patch bd
   (td.addDebugTag)))` by `toElfFile_mapDynamicOp_factor template typed
   (·.addDebugTag) …` (closes by `exact` since `addDebugTag typed h` is
   definitionally `mapDynamicOp typed (·.addDebugTag)`, `Ops/AddDebugTag.lean:16-17`).
   `[NEEDS COMPILE-VERIFICATION — the definitional `exact`, mirroring the shrink
   capstones' `removeRpath = mapDynamicOp (·.stripRpath)` closure.]`
2. The +1 size bound `patchDynamicEntries_addDebugTag_size_le_succ`:
   `(patch bd (td.addDebugTag)).size ≤ (patch bd td).size + 1`, built from
   `appendUnless_size_le`/`_mono` (`Adapter.lean:457-487`) — the debug
   `appendUnless` block is the only one whose `val?` changes (`none → some 0`).
   `[NEEDS COMPILE-VERIFICATION — whether the four OTHER unless-blocks +
   surplus + loop are provably IDENTICAL between `td` and `td.addDebugTag`; they
   should be, since `addDebugTag` touches only `.debug`.]`
3. Instantiate `tierD_roundtrip_of_grown_eo` at `eo := toElfFile template
   (addDebugTag typed h)`. The grown `eo`'s `.dynamic` section has the same
   `offset` as the no-op's and `encodedSize` at most +`dynEntrySize`; this is
   where the new driver's per-section hypothesis (Commit 1) is discharged —
   either via the normalized-form hypothesis surface (first cut) or via the
   honest layout lemma (Commit 3).

**Risk:** MEDIUM (depends on Commit 1's driver shape). **Verify:** build +
tests + axioms.

### Commit 3 — the HONEST grow-tolerant `growEOFWith` disjointness lemma
**(promote Commit 1's hypothesis to a derived fact — do only if §1.4(ii)'s
hypothesis surface proves unacceptable, else DEFER)**

State and prove `growEOFWith_produces_spliceRegionsDisjoint_of_base`: from
`base := toElfFile template typed` being fully laid-out (its 6 invariants
parser-derivable) + a witness that `eo.sections` equals `base.sections` except
at the grown indices (the `.dynamic` index, and for `growDynstr` ops the
`.dynstr` index), conclude
`(prepLayoutForEncode (syncDtStrszInFile eo)).spliceRegionsDisjoint`. The proof
leans on the FACT that `growEOFWith` flags the grown sections stale and
relocates them (`sectionStale`/`appendStaleSections`, `GrowEOF.lean:200-240`),
so the OUTPUT disjointness follows from
`growEOFWith_produces_spliceRegionsDisjoint`'s conclusion — the work is
re-deriving that theorem's `hHeaderSec`/`hPhdrSec` INPUTS for `eo` from `base`'s.
`[NEEDS COMPILE-VERIFICATION — this is the genuinely-new layout reasoning and
the single largest risk in the whole effort; budget accordingly. It may turn
out that `growEOFWith_produces` must itself be generalized to not require
per-section disjointness of its input.]`

**Risk:** VERY HIGH. **Verify:** build + tests + axioms; then retrofit Commits
1–2 to consume it (removing the hypothesis), keeping their STATEMENTS' public
surface where possible.

### Commit 4 — `noDefaultLib` Tier-D (second `mapDynamicOp` grower, near-free)
Identical shape to `addDebugTag` (Commit 2): `mapDynamicOp` (`Ops/NoDefaultLib.lean:19-20`),
dynstr unchanged, `.dynamic` +≤1 (the flags1 `appendUnless` block). Reuses the
generic factor + the new driver; only the size bound differs
(`patchDynamicEntries_noDefaultLib_size_le_succ`, same `appendUnless_size_le`
recipe but on the flags1 block; note `setNoDefaultLib` ALWAYS sets `flags1 :=
some _`, so if `td.flags1` was already `some` the count is unchanged, else +1).
**Risk:** LOW (mirror of Commit 2). **Verify:** build + tests + axioms.

### Commit 5 — `addNeeded` Tier-D (the hardest: dynstr + dynamic BOTH grow)
**Why hardest:** uses `growDynstrDynamicOp` (`Ops/AddNeeded.lean:21-23`), so the
`toElfFile` output differs from the no-op in TWO section contents (the bigger
`.dynstr` AND the bigger `.dynamic`, §0.2), and the dynstr is a DIFFERENT
`StringSection` (so `toElfFile … typed.dynstr ≠ toElfFile … (growDynstr typed).dynstr`
— the dependent index changes).

**Obligations:**
1. **A two-field factoring.** `toElfFile_mapDynamicOp_factor` does NOT apply
   (it assumes only `.dynamic` changes). You need a new factoring that pushes
   BOTH a `.strtab` update (the dynstr section) AND a `.dynamic` update out
   through the `applyX` chain. Assess: the `applyDynstr`/`applyDynsym` applies
   are at the FRONT of the chain (`Adapter.lean:860-867`:
   `applyInterp (… (applyVersym (applyDynamic (applyDynsym (applyDynstr template ds) …) …) …) …)`).
   The dynstr edit is the INNERMOST apply, so commuting a `.strtab` update out
   means pushing it through the ENTIRE outer chain (versym/sysvhash/gnuhash/
   verneed/interp AND applyDynamic AND applyDynsym). The existing per-type
   commutation suite is keyed on a `.dynamic` update at `iDyn`; a `.strtab`
   update at `iDynstr` needs an ANALOGOUS suite (commute past each apply whose
   target ≠ `iDynstr`). Critically, the dynstr index is `shstrndx`-adjacent and
   feeds `findIdxByName`/`shstrtab` (`SectionOps.lean:271-304`), so the
   commutation past `applyInterp` (which reads `interpIdx` via `findIdxByName`)
   needs `iDynstr ≠ shstrndx` (already available as
   `shstrndx_ne_of_content_dynamic_of_dynstr`-style facts). **Most of the
   `applyX` commutation suite does NOT survive verbatim** because the SECTION
   the dynstr edit targets is different from `iDyn`; you need a parallel
   `applyTypeOpt_strtab_comm`/`applyDynsym_strtab_comm`/etc. family. Budget
   this as comparable to the original `OpToElfFactor` §B suite. `[NEEDS
   COMPILE-VERIFICATION]`
2. **The dynstr-grows transport.** Even after factoring, the dynstr section's
   `encodedSize` grows, so its per-section disjointness breaks too — the new
   grow driver (Commit 1/3) must tolerate TWO grown sections, not one. The
   `growEOFWith` stale-detection handles both (both get relocated), but the
   Commit-3 honest lemma's "grown indices" witness must include `{iDyn, iDynstr}`.
3. The `.dynamic` count is +1 (prepend a DT_NEEDED, `DynamicSection.lean:84-86`),
   so a size bound `(patch bd (td.pushNeeded off)).size ≤ (patch bd td).size + 1`
   via the surplus/loop machinery (the prepended NEEDED is consumed by the loop's
   `.needed` arm or the surplus tail). `[NEEDS COMPILE-VERIFICATION]`

**Risk:** VERY HIGH (two-field factoring is genuinely new work; the dynstr
commutation suite is the bulk). **Verify:** build + tests + axioms.

**Deferred (out of scope for first pass), in rising difficulty after `addNeeded`:**
* `modifyRPath .set` / `modifySoname .set` — `growDynstrDynamicOp`, so they share
  `addNeeded`'s two-field factoring + dynstr-grow transport; the only delta is the
  `f` (`setRpathTag`/`setSonameOff` vs `pushNeeded`) and its ≤1 count bound. Once
  Commit 5 lands the two-field machinery, these are near-instantiations.
* `replaceNeeded` (grow path) — `growDynstr` + a bespoke record literal that ALSO
  rewrites `.verneed` (`Ops/ReplaceNeeded.lean:57-67`). The `.verneed` edit is a
  THIRD changed section (`applyVerneed`), so it needs a third commutation strand;
  hardest of all. Defer last.

---

## 4. Open questions / compile-verification needed

1. **(crux) Does `tierD_roundtrip_of_grown_eo` work with per-section
   disjointness hypothesized on the NORMALIZED form (§1.4(ii) / Commit 1), or
   must Commit 3's honest grow-tolerant `growEOFWith` lemma be proven first?**
   The existing `encodePreconditions_of_layoutNormalized`/
   `spliceRegionsDisjoint_of_structural_eo` route disjointness through
   `prepLayoutForEncode` but pin `hHSec`/`hPSec` on `eo`
   (`OpAdapterPreservation.lean:259-271, 304-348`); whether a parallel route can
   take those facts on `syncDtStrszInFile eo` / the normalized form without the
   `_eo` transport is unconfirmed by reading. **This determines whether Commit 3
   is optional or mandatory.**
2. **Does `growEOFWith_produces_spliceRegionsDisjoint` genuinely require
   `hHeaderSec`/`hPhdrSec` on its (grown) input, or do its branch leaves only
   use them on non-stale sections?** The signature has them
   (`GrowEOF.lean:4094-4095`); if the proof only consumes them for non-stale
   sections, a grow-tolerant restatement may be cheap. Needs reading
   `growEOFWithMainBody_produces_spliceRegionsDisjoint` and the fresh-PT_LOAD
   branch bodies (not read in full here).
3. **The definitional `exact` for `addDebugTag`/`noDefaultLib`** — confirm
   `addDebugTag typed h` reduces to `mapDynamicOp typed (·.addDebugTag)` so the
   generic factor closes by `exact` (mirrors the shrink capstones). High
   confidence from `Ops/AddDebugTag.lean:16-17`, but unverified by compile.
4. **The +1 size bounds** (`addDebugTag`/`noDefaultLib`) — confirm the four
   non-touched `appendUnless` blocks + surplus + loop are provably identical
   between `td` and `f td` (so only the touched block contributes the +1). High
   confidence (`f` touches one field) but the Lean equality of the loop state
   across the field change is unverified.
5. **The two-field factoring for `addNeeded`** — how much of the per-type
   `applyX` commutation suite survives when the changed section is the dynstr
   index (not `iDyn`)? Likely a fresh parallel suite is needed; size estimate
   (~comparable to OpToElfFactor §B) is a guess.
6. **`growEOFWith`'s output offsets/sizes < 2^64** — the four position bounds
   (`hHdrPhoff`/`hHdrShoff`/`hPhdrFitEn`/`hShdrFitEn`) are hypothesized on the
   normalized form even in the shrink capstone; for growers `growEOFWith` adds a
   fresh region via `roundUp` arithmetic, so these stay hypotheses (the
   sanctioned "file < 2^64" surface). Confirm the grow driver threads them
   identically to the shrink capstone.
