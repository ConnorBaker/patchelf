# Deferred-Work Roadmap

Forward-looking ledger of work deferred from the Lean 4 `patchelf`
port.  Current state of landed work is in
[`lean/STATUS.md`](../lean/STATUS.md); this document is the
forward-looking view.

> **§5.1 genericized over `mapDynamicOp f`; all 4 shrinking ops DERIVED.**
> `OpToElfFactor.lean`'s `removeRpath`-specific factoring/transport/capstone
> are now generic over an arbitrary `f`
> (`toElfFile_mapDynamicOp_factor` / `mapDynamicOp_structural_transport` /
> `toElfFile_mapDynamicOp_tierD_roundtrip_derived`); `removeRpath` (regression
> gate, unchanged statement+axioms), `modifyRPath.remove` (free),
> `removeNeeded` (new `filterNeededBy` size bound via the `NeededRel` potential
> function), and `modifySoname.remove` (`removeSoname` size bound, a `ShrinkRel`
> variant) all instantiate it.  The 4× type-based outer-apply duplication
> collapsed to 3 `applyTypeOpt_*` generics.  The shrinking-op family is now 4/4.
>
> **§5.1 growing ops — the `mapDynamicOp` growers are now FULLY DERIVED
> (`hSplice` no longer hypothesized).**  `OpToElfFactorGrow.lean` ships the
> keystone grow driver `tierD_roundtrip_of_grown_eo` (identical to
> `tierD_roundtrip_of_eo_facts` except it HYPOTHESIZES the normalized form's
> `spliceRegionsDisjoint` `hSplice`, since a grown `eo`'s widened section
> overlaps a neighbor and the layout pass re-lays-out the file to produce the
> disjoint normalized form; every other `EncodePreconditions` field stays
> derived from `eo`).  The new module `GrowEOFDisjointOfBase.lean` DERIVES
> `hSplice` from the no-op base for the two `mapDynamicOp` growers
> (PLAN-GROWING-OPS §3 Commit 3, the "very-high-risk" item, LANDED): a
> `mapDynamicOp` grower widens ONE section at its FIXED offset, so the
> size-independent invariants transport verbatim and the two per-section clauses
> survive via the LEFT disjunct, given two honest offset side conditions
> (`hDynAfterHeader`/`hDynAfterPhdr` — the dynamic section sits after the header
> / phdr table, WEAKER than the shrink path's `hSizeBound`).  Establisher
> `spliceRegionsDisjoint_of_grown_base` + corollary
> `Adapter.mapDynamicOp_spliceRegionsDisjoint_of_base`; the two capstones
> `toElfFile_{addDebugTag,noDefaultLib}_tierD_roundtrip_derived` MOVED here and
> were UPGRADED to no longer hypothesize `hSplice` — their surface is now the
> no-op base's 6 structural invariants (same as the shrink capstones) + the 2
> offset side conditions.  The driver `tierD_roundtrip_of_grown_eo` KEEPS its
> hypothesized `hSplice` (reused by the dynstr growers).
>
> **§5.1 dynstr growers — Tier-D capstones LANDED (hSplice HYPOTHESIZED; the
> two-field factoring DERIVED).**  `OpToElfFactorGrowDynstr.lean` ships Tier-D
> round-trips for the `growDynstrDynamicOp` growers `addNeeded` /
> `modifyRPath.set` / `modifySoname.set` (dynstr AND dynamic both grow) —
> PLAN-GROWING-OPS §3 Commit 5, LANDED.  The genuinely-new artifact, the
> **Strategy-A two-field factoring**, is DERIVED: the key insight collapses "two
> fields" to one — `addNeeded typed lib h = { tg with dynamic := tg.dynamic.map
> (·.pushNeeded off) }` by `rfl`, where `tg := (typed.growDynstr lib).1`
> ABSORBS the entire dynstr growth + dynsym/dynamic rebases into the base
> `toElfFile template tg`, leaving a single `.dynamic` update at `iDyn`, so NO
> parallel `.strtab`-commutation suite was needed.  Keystone
> `toElfFile_dynamicMapMono_factor` generalizes `toElfFile_mapDynamicOp_factor`
> to a MONOMORPHIC `g` on `.dynamic` (reusing `innerChain_factor_general`
> verbatim); per-op factorings
> `toElfFile_{addNeeded,modifyRPath_set,modifySoname_set}_factor` + the
> content-at-`iDyn` corollary `toElfFile_addNeeded_content_at_dynamicIdx`
> (`[propext, Quot.sound]`).  The three capstones
> `toElfFile_{addNeeded,modifyRPath_set,modifySoname_set}_tierD_roundtrip_derived`
> instantiate `tierD_roundtrip_of_grown_eo`, so they HYPOTHESIZE the normalized
> form's `spliceRegionsDisjoint` (`hSplice`, first-cut caliber) — UNLIKE the
> `mapDynamicOp` growers, whose `hSplice` is derived.  **So every growing op
> named in PLAN-GROWING-OPS now has a Tier-D capstone.**  The ONLY remaining
> §5.1 growing-ops item: DERIVE `hSplice` for the dynstr growers — a
> TWO-grown-section analogue of `mapDynamicOp_spliceRegionsDisjoint_of_base`
> (the `.dynstr` section grows too); `toElfFile_addNeeded_content_at_dynamicIdx`
> is the building block, but the establisher is NOT done.
>
> **Layout + validator landed.** The PT_LOAD coherence work designed
> in [`REWRITE-PHASE-3-DESIGN.md`](REWRITE-PHASE-3-DESIGN.md) shipped
> in a minimal form: `growEOF` + `syncDtAddrTagsInFile` (replacing
> `layoutForEncoding` as the primary layout strategy) plus a
> decidable pre-write validator (`Patchelf/Elf/Validate.lean`) that
> the CLI runs before every write.  CLI also migrated to lean4-cli
> subcommands.  This closes ROADMAP §3.6 and §3.7 outright; renders
> §3.1 obsolete; reduces §3.5 to "PT_GNU_STACK append" (a different
> phdr-table-growth subset).
>
> **Encoder-output `spliceDisjoint` landed.**
> `Encoder.prepLayoutForEncodeWith_produces_spliceRegionsDisjoint`
> closes §1.3a's encoder-output side via the unified `PlaceFold`
> scaffolding (one fold-induction skeleton specialized to both
> `layoutForEncoding` and `growEOFWith`'s `appendStaleSections`).
> §5.1 (op-level Tier D) was supposed to be unblocked by this
> work, but a non-trivial dependent-type obstacle in `Adapter.toElfFile`
> was discovered during the worked example — see §5.1 for details.
>
> Item §1.2 is now **fully landed** — both the `_preserves_valid`
> and `_preserves_loadable` ladders close, including the top-level
> `growEOFWith_preserves_loadable` dispatch and the end-to-end
> `prepLayout_syncDtStrsz_preserves_loadable`.  §5.1 (op-level Tier D)
> is **in progress, open core CLOSED**: the `toElfFile` dependent-type
> obstacle is resolved, Tier-1 ops + the Tier-2/3 scaffold landed, and
> the three open-core obligations (A `syncOk`, B `hIdem`, C residual
> `EncodePreconditions`) are now proven and composed into the
> `tierD_roundtrip` driver, applied to the two shrinking ops
> (`removeRpath`/`removeNeeded`).  Remaining: per-op discharge of each
> op's `eo` facts (currently hypotheses) — canonical next pickup,
> [`PICKUP-PROMPT-OP-TIER-D.md`](PICKUP-PROMPT-OP-TIER-D.md).  §3.5a
> fully landed (both in-place and relocatePht sub-cases — see below).
> §1.1 parser side landed.
>
> **2026-05 cleanup + feature gap pass landed.** Six commits of
> mechanical-duplication cleanup (~−260 LOC across CLI, Adapter,
> AdapterRoundtrip, ByteRoundtrip, SectionOps; extends
> `simp_splice`'s omega-discharger with `writeArray_*_size`
> lemmas).  Plus three feature commits closing §3.3 (GNU hash
> rebuild + reloc remap), §3.4 (vn_file rewrite in replace-needed),
> and adding the §3.5a porting plan
> ([`REWRITE-FRESH-PT-LOAD-DESIGN.md`](REWRITE-FRESH-PT-LOAD-DESIGN.md)).
> See ROADMAP §3.3 / §3.4 / §3.5a for current state.
>
> **2026-05 IR migration + §3.5a fully landed.**
> SectionContent IR migration (Section.type derived from content;
> raw constructor proof-carrying); `EncodePreconditions` shrinks
> from 11 to 10 fields.  Plus §3.5a complete: in-place
> (`growEOFWithFreshPtLoad`) + relocatePht
> (`growEOFWithFreshPtLoadReloc`) sub-cases.  Empirically verified
> on coreutils `ls` (the canonical relocatePht-class binary).
> Tests: 52 → 54 shell tests passing.

---

## Picking up work (for fresh agents)

**Build and test from `lean/`:**
```sh
nix develop ../.#lean -c lake build              # expect a clean build
nix develop ../.#lean -c bash tests/run.sh       # 54/54 shell tests expected
grep -rn "sorry\b" Patchelf/                     # zero matches expected
```

**The single fresh-agent handoff covering ALL open work is
[`PICKUP-PROMPT-OP-TIER-D.md`](PICKUP-PROMPT-OP-TIER-D.md)** (despite the
filename it now scopes §5.1 + §3.5b + §4.2, in priority order; §5.2 is now
closed).  The growing-ops half of §5.1 has its own design plan,
[`PLAN-GROWING-OPS.md`](PLAN-GROWING-OPS.md).

**Recommended pickup order (the complete open menu):**

- **§5.1 op-level Tier D — IN PROGRESS; all four shrinking ops' structural invariants now DERIVED, via generic `mapDynamicOp f`.**
  The `Adapter.toElfFile` dependent-type obstacle is RESOLVED (the
  un-bundling refactor, commit `8ffe2cb`).  Tier 1 ops (`setOsAbi`,
  `modifyExecstack`) have full `_preserves_loadable`; the Tier-2/3
  round-trip scaffold + the three **open-core obligations** (A `syncOk`,
  B `hIdem`, C residual `EncodePreconditions`) are CLOSED, composed
  into the `tierD_roundtrip` / `tierD_roundtrip_of_eo_facts` drivers.
  Obligation C DERIVES `identValid`/`sizeFit`/`nullEmpty`/`headerFit_entry`;
  only the 4 position-bound families remain hypotheses.

  **`removeRpath` + `modifyRPath.remove` + `removeNeeded` + `modifySoname.remove`
  criterion-2 DONE** (`Patchelf/Elf/OpToElfFactor.lean`).  The factoring/transport/capstone are
  now generic over an arbitrary `f` (since every shrinking op is
  `mapDynamicOp e f`): `toElfFile_mapDynamicOp_factor` factors `toElfFile
  template (mapDynamicOp typed f)` as a single `.dynamic`-shrink
  `updateSectionContent` on the no-op output;
  `mapDynamicOp_structural_transport` derives the 6 disjointness invariants +
  section-0-NULL from the no-op output's, taking the lone per-`f` fact
  `hSizeBound : (patch byteDyn (f d)).size ≤ (patch byteDyn d).size`; the generic
  capstone `toElfFile_mapDynamicOp_tierD_roundtrip_derived` is instantiated at:
  * `removeRpath` (`f := ·.stripRpath`, bound `patchDynamicEntries_stripRpath_size_le`)
    — `toElfFile_removeRpath_tierD_roundtrip_derived`, the regression gate
    (statement + axioms unchanged across the genericization).
  * `modifyRPath.remove` (same `f`, free) — `toElfFile_modifyRPath_remove_tierD_roundtrip_derived`.
  * `removeNeeded` (`f := ·.filterNeededBy lib.toUTF8`, bound
    `patchDynamicEntries_filterNeededBy_size_le` via the `NeededRel`
    potential function) — `toElfFile_removeNeeded_tierD_roundtrip_derived`.
  * `modifySoname.remove` (`f := ·.removeSoname`, bound
    `patchDynamicEntries_removeSoname_size_le`, a `ShrinkRel` variant) —
    `toElfFile_modifySoname_remove_tierD_roundtrip_derived`.  Closes the family 4/4.

  Each capstone takes only the *no-op output's* structural invariants
  (template-/parser-derivable) + the sanctioned eo-level remainder (`IsValid`,
  phnum, dynstr + `< 2^64` fit, the 4 derived-field facts, the 4 position bounds).

  **Growing ops — the `mapDynamicOp` growers are now FULLY DERIVED**
  (`Patchelf/Elf/OpToElfFactorGrow.lean` + `Patchelf/Elf/GrowEOFDisjointOfBase.lean`).
  The keystone grow driver `tierD_roundtrip_of_grown_eo` HYPOTHESIZES the
  normalized form's `spliceRegionsDisjoint` (`hSplice`) — a grown `eo`'s widened
  section overlaps a neighbor, so per-section disjointness on `eo` is
  unprovable; the layout pass (`prepLayoutForEncode`/`growEOFWith`) re-lays-out
  the file and produces the disjoint normalized form — and derives every other
  `EncodePreconditions` field from `eo`.  `GrowEOFDisjointOfBase.lean` now
  DERIVES `hSplice` from the no-op base for the two `mapDynamicOp` growers
  (PLAN-GROWING-OPS §3 Commit 3, the "very-high-risk" item): a `mapDynamicOp`
  grower widens ONE section at its FIXED offset, so section-0-NULL + the 3
  header/table clauses transport verbatim and `headerSectionDisjoint`/
  `phdrSectionDisjoint` survive via the LEFT disjunct, given two honest offset
  side conditions (`hDynAfterHeader`/`hDynAfterPhdr`, WEAKER than the shrink
  path's `hSizeBound`); `shdrSectionDisjoint`/`sectionsNonOverlapping` are
  re-established by `growEOFWith`.  Establisher
  `spliceRegionsDisjoint_of_grown_base` (`namespace Patchelf.Elf`) + corollary
  `Adapter.mapDynamicOp_spliceRegionsDisjoint_of_base` (mirror of
  `mapDynamicOp_structural_transport`, reusing `RemoveRpathFactorData`); both
  pure `[propext, Classical.choice, Quot.sound]`.  The two capstones
  `toElfFile_{addDebugTag,noDefaultLib}_tierD_roundtrip_derived` MOVED here and
  were UPGRADED: they NO LONGER hypothesize `hSplice` — their surface is the
  no-op base's 6 structural invariants (same as the shrink capstones) + the 2
  offset side conditions.  The driver `tierD_roundtrip_of_grown_eo` STAYS in
  `OpToElfFactorGrow.lean` and KEEPS its hypothesized `hSplice` (reused by the
  dynstr growers).

  **Dynstr growers — Tier-D capstones LANDED** (`Patchelf/Elf/OpToElfFactorGrowDynstr.lean`,
  PLAN-GROWING-OPS §3 Commit 5).  `addNeeded` / `modifyRPath.set` /
  `modifySoname.set` use `growDynstrDynamicOp` (dynstr AND dynamic both grow).
  The genuinely-new artifact, the **Strategy-A two-field factoring**, is DERIVED:
  the key insight collapses "two fields" to one — `addNeeded typed lib h = { tg
  with dynamic := tg.dynamic.map (·.pushNeeded off) }` by `rfl`, where `tg :=
  (typed.growDynstr lib).1` ABSORBS the entire dynstr growth + dynsym/dynamic
  rebases into the base `toElfFile template tg`, leaving a single `.dynamic`
  update at `iDyn` (NO parallel `.strtab`-commutation suite needed).  Keystone
  `toElfFile_dynamicMapMono_factor` generalizes `toElfFile_mapDynamicOp_factor`
  to a MONOMORPHIC `g` on `.dynamic` (reusing `innerChain_factor_general`
  verbatim); per-op factorings
  `toElfFile_{addNeeded,modifyRPath_set,modifySoname_set}_factor` + the
  content-at-`iDyn` corollary `toElfFile_addNeeded_content_at_dynamicIdx`.  The
  three capstones
  `toElfFile_{addNeeded,modifyRPath_set,modifySoname_set}_tierD_roundtrip_derived`
  instantiate `tierD_roundtrip_of_grown_eo`, so they HYPOTHESIZE the normalized
  form's `spliceRegionsDisjoint` (`hSplice`) — UNLIKE the `mapDynamicOp` growers,
  whose `hSplice` is derived.

  **So every growing op named in PLAN-GROWING-OPS now has a Tier-D capstone.**
  The shrinking-op family is COMPLETE (4/4); the `mapDynamicOp` growers are FULLY
  DERIVED (carrying only the 2 offset side conditions atop the shrink ops'
  no-op-base surface); the dynstr growers have capstones LANDED with the
  two-field factoring derived but `hSplice` still hypothesized.  **The ONLY
  remaining §5.1 growing-ops item:** DERIVE `hSplice` for the dynstr growers — a
  TWO-grown-section analogue of `mapDynamicOp_spliceRegionsDisjoint_of_base` (the
  `.dynstr` section grows too); `toElfFile_addNeeded_content_at_dynamicIdx` is the
  building block, but the establisher is NOT done.  See §5.1 for the full chain +
  the reusable generic `OpToElfFactor` primitives.
- **§5.2 strengthen weak `_observable` theorems — DONE.**  Every mutating op now
  has an adversary-rejecting observable: `noDefaultLib_observable_strong` (the
  last genuinely-missing case-split) + `modify{RPath,Soname}.set`'s
  non-corruption `_set_preserves` companions landed this cycle, joining the
  earlier `addDebugTag_observable_strong` / `removeNeeded_needed_size_lt`.  See
  the §5.2 table — all rows are now "yes".  Pure typed-algebra, no layout.
- **§4.2 trailing-array DSL field kind + `Verneed.write_decode`** —
  independent typed-side completeness item; `.verneed` is stored as `.raw`
  at the byte layer, so the byte-roundtrip doesn't depend on it.  Adds a
  `trailing Array<SubType>` DSL field kind + forward roundtrips for Verneed
  / SysVHashTable / GnuHashTable.  See §4.2 + `RESEARCH-SCHEMA-DSL.md`.
- **§3.5b PT_GNU_STACK append when missing** — small C++-parity feature gap.
  `set-execstack` on a binary without a PT_GNU_STACK phdr is a no-op;
  C++ appends one.  The phdr-grow machinery from §3.5a is in place; this is
  mechanically similar to `freshPtLoad`.  Pick up if/when the use case arises.

**Recently-closed work** (kept for cross-reference):

- §3.5a (both in-place + relocatePht sub-cases) — LANDED.
- §1.1 parser side (`Parser.parseLoadable` + `LoadableElfFile`) — LANDED.
- §1.2 `_preserves_valid` ladder (all 7 byte-layer theorems +
  top-level `growEOFWith_preserves_valid`) — LANDED.
- §1.2 `_preserves_loadable` ladder (all four branches +
  top-level `growEOFWith_preserves_loadable`, lifted to the
  pipeline-level `prepLayoutForEncodeWith_preserves_loadable` and the
  end-to-end `prepLayout_syncDtStrsz_preserves_loadable`) — LANDED.
- §1.3a `prepLayoutForEncodeWith_produces_spliceRegionsDisjoint` — LANDED.

**Patterns to know before touching Tier D / encoder proofs:**

- `Encoder.encode` and `Encoder.encodeBody` are `@[irreducible]`;
  use the `_eq` companion lemmas for unfolding.  Removing the
  attribute will time out per-byte access proofs at >32M
  heartbeats.
- For do-blocks that need proof navigation, two routes work:
  (a) rewrite to explicit `if-then-else` — the `Id.run do` form
  elaborates to lambda continuations that resist `simp [bind]`.  See
  `Parse.parseHeader` and `LayoutEngine.layoutAlreadyValid` for
  precedent.  (b) for genuinely imperative shapes (`let mut` +
  `for`), use `mvcgen` from `Std.Tactic.Do` (Lean 4.21+); see
  `Adapter.patchDynamicEntries` for a current `Id.run do` candidate.
- For loop-based decoders (`decodeDynamic`), use two-state
  foldl/loop induction — see `decodeDynamic_writeArray_eq` for
  the template.

---

## Deferred work, prioritized

### Priority 1 — Unblock tiers above IsValid

#### 1.1 Parser: establish `IsLoadable`, not just `IsValid` — PARSER SIDE LANDED

`Parser.parseLoadable` now returns `LoadableElfFile`, a stronger
companion to `ParsedElf` that bundles:

- `elf : ElfFile` (the parsed file);
- `isLoadable : elf.IsLoadable` (4-clause: `IsValid` plus
  `sectionsNonOverlapping`, `ptInterpAgreement`,
  `ptDynamicAgreement`, `segmentCongruence`);
- `shdrSecDisjoint : elf.shdrSectionDisjoint`;
- `secInSomeLoad : elf.sectionFileInSomePtLoad`.

These cover everything the kernel + glibc loader inspect at exec.
On failure, `parseLoadable` dispatches to per-clause `ParseError`
variants: `sectionsOverlapping`, `shdrSectionsOverlapping`,
`ptInterpAgreementFailed`, `ptDynamicAgreementFailed`,
`segmentCongruenceFailed`, `sectionFileOutsidePtLoad`.

`LoadableElfFile.toParsedElf` recovers the weaker bundle for
callers that only need `IsValid`.

The CLI's `validate` subcommand cross-checks both paths
(`validateBytes` and `parseLoadable`); any divergence surfaces as
exit 5.  Real-binary tests 50–54 transitively exercise the new
predicate via the pre-write validator.

**Downstream still open:** every op needs an `_preserves_loadable`
theorem so the static guarantee threads through CLI flows.  Most
ops preserve all clauses definitionally; the interesting ones are
`setInterpreter` (PT_INTERP agreement after changing interp
offset) and any op whose post-encode routes through
`growEOFWith`'s fresh-PT_LOAD or relocatePht branches.  Now that the
layout pass's `growEOFWith_preserves_loadable` is closed, per-op
preservation is the remaining loader-coherence work — pick up under
§5.1.

#### 1.2 Pre-encode passes: `_preserves_valid` + `_preserves_loadable` — FULLY LANDED

**Status:** both ladders are closed.  `syncDtStrszInFile_preserves_valid`
(`Encoder.lean`) and `syncDtAddrTagsInFile_preserves_valid`
(`GrowEOF.lean`) landed; the latter mirrors the former's structure
(aux + outer wrapper) with `e.dynstr = some ds` as a precondition
(needed to derive `iDyn ≠ shstrndx` — `IsValid` alone doesn't force
shstrndx to point at a strtab; real ELFs always satisfy it, and the
runtime validator catches pathological inputs).  The top-level
`growEOFWith_preserves_valid` and `growEOFWith_preserves_loadable`
both compose their four branches (see below).

**`_preserves_valid` ladder complete.**  Top-level
`growEOFWith_preserves_valid` lands by composing four branches:

1. `layoutAlreadyValid e = true` → identity (trivial).
2. `lastPtLoadIdx e.phdrs = none` → `layoutForEncoding` →
   `layoutForEncoding_preserves_valid`.
3. `canExtendLastPtLoad ... = true` → `growEOFWithMainBody` →
   `growEOFWithMainBody_preserves_valid`.
4. Else if `canAddFreshPtLoad e = true` → `growEOFWithFreshPtLoad`
   → `growEOFWithFreshPtLoad_preserves_valid`.
5. Else → `growEOFWithFreshPtLoadReloc` →
   `growEOFWithFreshPtLoadReloc_preserves_valid`.

Built on these reusable pieces:

* `PlaceFold.ValueInv` + `placeFold_value_inv` +
  `placeFold_value_witness` (`LayoutEngine.lean`) — structural
  fact that every `placeFold` output entry is either the input
  section verbatim or `transform input off` for some `off`.
* Per-field corollaries: `appendStaleSections_*` (in `GrowEOF.lean`)
  and `layoutSectionsFold_field_eq` (in `LayoutEngine.lean`) plus
  per-field rfl lemmas for both `appendTransform` and
  `Section.withOffset`.
* Accessor preservations (`dynamicIdx`, `dynamic`, `dynsym`,
  `dynstr`, `shstrtab`, `findIdxByName`, etc.) for each of the
  four output shapes — typed accessors all preserved because
  per-section types/names/content are.

The fresh-PT_LOAD branches' theorem takes
`(e.phdrs.size + 1) < UInt16.size` for the bumped-phnum UInt16
round-trip; real binaries satisfy this trivially.

**`_preserves_loadable` ladder complete (LANDED).**  All four
branches plus the top-level dispatch ship:
`layoutForEncoding_preserves_loadable` (`LayoutEngine.lean`,
no-PT_LOAD branch, built on `relocatePhdr_*`),
`growEOFWithMainBody_preserves_loadable`,
`growEOFWithFreshPtLoad_preserves_loadable`,
`growEOFWithFreshPtLoadReloc_preserves_loadable`, and
`growEOFWith_preserves_loadable` (`GrowEOF.lean`).

The growEOFWith branches needed new per-phdr facts for
`updatePhdrsAfterMove` — structurally more involved than
`relocatePhdr` because the `if i = lastIdx` branch updates
filesz/memsz (preserving type/offset/vaddr/align) which then
crosses the PT_INTERP / PT_DYNAMIC type-test if-then-else.  The
key tactic over the previous stuck attempt: **`subst` the
`i = lastIdx` and `interpIdx?`/`dynamicIdx?` witnesses rather than
`rw`-ing them** (the rewrites trip the dependent-motive checker
under the nested `dif`).  Lemmas:

- `updatePhdrsAfterMove_pt_load_offset_vaddr_align` — bypasses the
  PT_INTERP/PT_DYNAMIC tests via type-disjointness (PT_LOAD ≠
  both), giving segmentCongruence.
- `updatePhdrsAfterMove_pt_interp` / `_pt_dynamic` — the agreement
  clauses; handle the lastIdx pre-update via the `subst` trick.
- `updatePhdrsAfterMove_type` / `_size` — general type / size
  preservation.
- `retargetPtPhdr_{size,type,of_not_pt_phdr}` + composed
  `retarget_update_*` — the relocate branch's extra outer
  `retargetPtPhdr` layer (PT_PHDR ≠ PT_LOAD/INTERP/DYNAMIC, so it's
  identity on the three relevant types).
- `freshPtLoad_roundUp_congruence` — the fresh PT_LOAD's
  congruence (offset/vaddr both `roundUp _ align` ⟹ `≡ 0 mod align`).

The fresh-PT_LOAD branches take `(e.phdrs.size + 1) < UInt16.size`;
the top-level dispatch additionally takes the structural
disjointness invariants (`hSection0Null` / `headerPhdrDisjoint` /
`headerSectionDisjoint` / `phdrSectionDisjoint`) for the per-branch
`sections_nonoverlapping`.

**Pipeline-level closure.** The ladder was lifted one rung above
`growEOFWith` to the full pre-encode pipeline.
`prepLayoutForEncodeWith` is `if layoutAlreadyValid then e else
syncDtAddrTagsInFile (growEOFWith …)`, so
`prepLayoutForEncodeWith_preserves_loadable` (`Encoder.lean`)
composes `growEOFWith_preserves_loadable` with a new
`syncDtAddrTagsInFile_preserves_loadable` (`GrowEOF.lean`).  The
latter is light: `syncDtAddrTagsInFile` only same-size-`map`s the
`.dynamic` section, so it preserves `phdrs` verbatim and per-section
`(type, offset, encodedSize)` everywhere; the four clauses transport
directly (three via the literal `phdrs` preservation,
`sections_nonoverlapping` via the per-section facts).  A
`growEOFWith_dynstr` dispatch lemma threads the `dynstr`
precondition (needed for `iDyn ≠ shstrndx`) through `growEOFWith`.

**End-to-end closure.** The first pre-encode pass
(`syncDtStrszInFile`, the DT_STRSZ resync) also preserves
loadability — `syncDtStrszInFile_preserves_loadable` (`Encoder.lean`),
structurally identical to `syncDtAddrTagsInFile` (no-op or same-size
`.dynamic` map).  Plus the precondition-lifting lemmas (`_header`,
`_dynstr`, `_{headerPhdr,headerSection,phdrSection}Disjoint`,
`_section0Null`) let it chain with the second pass into the capstone
`prepLayout_syncDtStrsz_preserves_loadable`:
`(prepLayoutForEncode (syncDtStrszInFile e)).IsLoadable`.  By
`encode_eq` that IS the IR `encodeBody` serializes, so the encoder's
entire pre-write transform provably preserves loadability.

Axioms: `[propext, Classical.choice, Quot.sound]` — no `sorryAx`.
Actual cost was ~780 LOC across `GrowEOF.lean` (L1 per-phdr facts +
four branch theorems + top-level dispatch), ~190 LOC for the
pipeline-level lift, and ~290 LOC in `Encoder.lean` for the
first-pass `syncDtStrszInFile` family + the end-to-end capstone.

**Supporting infrastructure landed.** `Patchelf/Elf/SectionOps.lean`
(~420 LOC) exposes the helpers `growEOFWith` / `syncDtAddrTagsInFile`'s
preservation proofs will reuse:

- Field projections: `updateSectionContent_{header,phdrs,sections,
  sections_size,sections,getElem_ne,getElem_self,type,name,offset}`.
- Structural-index preservation:
  `updateSectionContent_{findUniqueTypeIdx,dynamicIdx,dynsymIdx,
  versymIdx,shstrtab,findIdxByName,dynstrIdx,interpIdx}`.
- Typed-accessor preservation under content-disjoint updates:
  `updateSectionContent_{contentAt_none,contentAt_some_ne,dynsym_eq,
  dynstr_eq,interp_eq}`.
- Generic `firstIdxWhereIn_congr` (drives the index-preservation
  proofs above) and `firstIdxWhereIn_some_implies` /
  `findUniqueTypeIdx_section_type` (extract structural facts about a
  found section).
- "Different content constructor ⇒ index disjointness":
  `dynstrIdx_target_ne_of_content_dynamic`,
  `dynsymIdx_target_ne_of_content_dynamic`,
  `shstrndx_ne_of_content_dynamic_of_dynstr`.

#### 1.3 Unconditional Tier D — DONE

`ByteRoundtrip.parse_encode_roundtrip` is unconditional under
`EncodePreconditions`.  See `lean/STATUS.md` §Tier D.

#### 1.3a `EncodePreconditions` from parser output — 9 of 10 done

`encodePreconditions_of_parser bs shdrs e` derives all fields except
`spliceDisjoint` from parser-output structural facts.  Per-clause
helpers:

| Clause | Helper | Caller-supplied side condition |
|---|---|---|
| `identValid` | `identBytesValid_of_parseHeader_ok` | `parseHeader bs = .ok e.header` |
| `nullEmpty` | `sectionFromShdr_null_empty` | per SHT_NULL shdr: `sh.size.val = 0` |
| `sizeFit` | `sectionFromShdr_encodedSize_le` | per shdr: `sh.size.val < UInt64.size` |
| `syncOk` | `syncDtStrszInFile_eq_id` | `e.dynStrszCoherent` |
| `headerFit_{entry,phoff,shoff}` | `parseHeader_byte_facts` + `(readU64 _ _).toNat_lt` | `parseHeader bs = .ok e.header` |
| `phdrFit` | per-element `Decode.decodePhdrs_getElem` + `toNat_lt` | `e.phdrs = decodePhdrs bs ...` |
| `shdrFit` | per-element `Decode.decodeShdrs_getElem` + `toNat_lt` | `shdrs = decodeShdrs bs ...` |

`typesMatch` is gone after the SectionContent IR migration.
`Section.type` is now derived from `content.type` (no stored field),
and `SectionContent.raw` carries a structural proof that its
`sh_type` is non-structural — so the type↔content invariant holds
by construction with no external predicate or precondition.

`spliceDisjoint` is the missing field.  Parser-side: not
derivable, since overlapping sections are spec-valid and the parser
shouldn't enforce pairwise region disjointness.

Encoder-output side: **DONE.**  The composed API
`Encoder.prepLayoutForEncodeWith_produces_spliceRegionsDisjoint`
takes the 5 structural input invariants
(`headerPhdrDisjoint` / `headerShdrDisjoint` / `phdrShdrDisjoint` /
`headerSectionDisjoint` / `phdrSectionDisjoint`) plus
`hSection0Null` and returns `spliceRegionsDisjoint` on the
encoder's full layout pre-pass output.  Composes:

* `GrowEOF.growEOFWith_produces_spliceRegionsDisjoint` — discharges
  all 3 branches (fast path / fallback / main path) via the unified
  `LayoutEngine.PlaceFold` scaffolding parameterized over
  `verbatim`, `transform`, and `baseOffset`; both `layoutForEncoding`
  and `growEOFWith`'s `appendStaleSections` are specializations.
  Client specializations exhibit a `TransformSpec`
  (field-preservation contract) and a `VerbatimWitness`
  (NULL/NOBITS-or-bound + pairwise disjoint for verbatim entries).
* `GrowEOF.syncDtAddrTagsInFile_preserves_spliceRegionsDisjoint` —
  the second pre-encode pass preserves the predicate.

The remaining gap to *unconditional* Tier D is op-level: each op must
establish the 5 input invariants on its output.  This is item §5.1,
which has a non-trivial dependent-type obstacle (see §5.1).

### Priority 2 — Test coverage + spec strengthening

#### 2.1 Weak observable theorems — DONE

`addDebugTag_observable_strong` (`Ops/AddDebugTag.lean`) returns the
disjunction `(DT_DEBUG was present and value preserved) ∨ (DT_DEBUG
was absent and value = 0)`.  `removeNeeded_needed_size_lt`
(`Ops/RemoveNeeded.lean`) gives a strict-decrease witness when the
target lib was present.  Both are adversary-rejecting: identity ops
fail them.

#### 2.2 Smoke roundtrip test — DONE

`tests/cases/00-parse-encode-identity.sh` runs `patchelf roundtrip
--output OUT IN && cmp IN OUT` against a hand-rolled
layout-already-valid fixture.

### Priority 3 — Feature parity with C++ patchelf

Closed in earlier passes (kept here as cross-reference targets):

- **§3.1 Multi-op canonical ordering — OBSOLETE.** Subcommand CLI
  retires single-process multi-op; chain via shell.
- **§3.2 `shrinkRPath` FS probing — DONE.** `runShrinkRpath` probes
  with `System.FilePath.pathExists`; `--allowed-prefixes` is a
  pure-filter override.
- **§3.6 `--page-size <N>` — DONE.** Threaded `Options.pageSize` →
  `encodeWith pageSize?` → `growEOFWith`'s `alignStartPage =
  max pageSize (maxPtLoadAlign e.phdrs)`.
- **§3.7 `--debug` — DONE.** `Patchelf.Log` (an `IO.Ref Bool` plus
  a `debug` helper); `runWith` enables it from `Options.debug` and
  emits trace lines at parse / validate / write / result-rendering
  points.

Open items:

#### 3.3 `.gnu.hash` rebuild in `rename-dynamic-symbols` — DONE

Implemented in commits `da73c51` (rebuild) and `ccc7bc6` (reloc
remap).  New module `Patchelf/Elf/GnuHashRebuild.lean` mirrors C++
`rebuildGnuHashTable`: re-bucketizes the hashed dynsym range,
rewrites bloom/buckets/chain, and reorders dynsym + versym so
symbols of the same bucket are contiguous (loader range-scan
requirement).  Returns the dynsym permutation `(firstSymIdx, perm)`.

`Patchelf/Elf/Ops/RenameDynamicSymbols.lean` exposes
`gnuHashRebuildOp : ValidElfFile → ValidElfFile × Option (Nat ×
Array Nat)` as a separate post-pass.  CLI's `renameOnce`
pipelines `renameDynamicSymbols` → `gnuHashRebuildOp` →
`Adapter.toElfFile` → `ElfFile.remapRelocs perm` → `encode`.

`Patchelf/Elf/RelocRemap.lean` walks SHT_REL (16-byte) and
SHT_RELA (24-byte) sections by raw bytes; for each entry decodes
`r_info`, applies the permutation to the high-32-bit symbol
index, recombines.  Operates on bytes rather than structural
section types to avoid bloating the central byte roundtrip
dispatch — relocations stay as `SectionContent.raw`.

Tests: shell tests 51 (rename on `.gnu.hash` binary, loader
accepts rebuilt table) and 52 (rename forces bucket movement,
relocation targets correctly remap, binary still runs).  Both
exercise `/tmp/lean-pe-fixtures/hello`, a real glibc-linked
binary.

#### 3.4 `.gnu.version_r` update in `replace-needed` — DONE

Implemented in commit `e2633d2`.
`Patchelf/Elf/Ops/ReplaceNeeded.lean` exposes
`VerneedSection.rewriteVnFile`; both `replaceNeededReuse` and
`replaceNeeded` thread it through.  The grow path passes the OLD
dynstr to the lookup since old offsets remain valid in the
appended-to dynstr.

Tests: shell test 50 verifies on a real glibc binary that
`readelf -V` shows the renamed library name post-rename.

#### 3.5a Allocate a fresh PT_LOAD when extension is unsafe — DONE

Plan documented in
[`REWRITE-FRESH-PT-LOAD-DESIGN.md`](REWRITE-FRESH-PT-LOAD-DESIGN.md).
Both sub-cases shipped:

**In-place** (`growEOFWithFreshPtLoad`): when `canExtendLastPtLoad`
rejects (BSS-heavy binary) AND `canAddFreshPtLoad` accepts (room
for one more phdr in the existing slot):

- append a brand-new PT_LOAD entry to `e.phdrs` covering
  `[startOffset, startOffset + appendedBytes)`;
- bump `header.phnum` by 1;
- leave the original phdr table in place.

Proven via `growEOFWithFreshPtLoad_produces_spliceRegionsDisjoint`.
Test: `tests/cases/53-cli-set-rpath-bss-heavy.sh` (synthetic).

**RelocatePht** (`growEOFWithFreshPtLoadReloc`): when there is no
in-place room (`canAddFreshPtLoad` rejects), move the phdr table
itself to the appended region:

- new layout in the appended region:
  `[startOffset, startOffset + phtSize)` — relocated phdr table,
  `[startOffset + phtSize, ...)` — moved sections;
- new PT_LOAD covers BOTH (`filesz = memsz = phtSize + appendedBytes`);
- update `header.phoff = startOffset`, `header.phnum = phdrs.size + 1`;
- retarget the PT_PHDR program header via `retargetPtPhdr`
  (without this, glibc's `ld.so` miscomputes the load base and
  segfaults at the first relocation).

Proven via `growEOFWithFreshPtLoadReloc_produces_spliceRegionsDisjoint`.
Crucially, this proof needs no extra precondition beyond the
standard structural input invariants — the relocated phdr region
sits at `[startOffset, ...)` past `currentFileEnd`, so verbatim-section
disjointness comes directly from `currentFileEnd_ge_section_end`.

Test: `tests/cases/54-cli-set-rpath-relocate-pht.sh` (real
`coreutils ls`; canonical relocatePht-class binary, with the phdr
table packed tight against `.note.gnu.build-id`).

#### 3.5b PT_GNU_STACK append when missing

`set-execstack` on a binary without PT_GNU_STACK phdr is currently
a no-op (`Ops/Execstack.lean` only maps over existing phdrs);
C++ appends.  The phdr-array-grow machinery from §3.5a is now
fully in place — appending a PT_GNU_STACK phdr is mechanically
similar to `freshPtLoad`: just construct a different phdr value
(PhType.PT_GNU_STACK with PF_R | PF_W, zero offset/size) and bump
phnum.  Pick up if/when the use case arises.

#### 3.8 Per-clause `ParseError` classification — DONE

`Parser.parse` now dispatches IsValid failures to per-clause
variants via the 8 decidable sub-instances.  Six new variants
(`headerCountsMismatch`, `strtabMalformed`, `dynamicWellFormedFailed`,
`contentWellFormedFailed`, `typesNotDistinct`, `namesNotUnique`)
plus reuses of `shdr0NotNull` and `dynsymOffsetOutOfBounds`.
`shdrIdxMismatch` remains as a totality fall-through.

### Priority 4 — DSL extensions

`§4.1 decode ∘ write = id emission` is DONE — all 7 fixed-layout
schemas get `X_decode_write` theorems auto-emitted by `elf_schema`,
consumed by `section_decode_encode`.

#### 4.2 Variable-length trailing-array field kind + Verneed forward

The DSL supports 5 fixed-layout field kinds.  Three writers remain
hand-written in Schemas.lean (Verneed, SysVHashTable, GnuHashTable)
because their shape is fixed-prefix + trailing-variable-array(s).
Adding a `trailing Array<SubType>` field kind would let these
become pure DSL invocations.  See `RESEARCH-SCHEMA-DSL.md` §"DSL
v3" for the design sketch.

The forward direction `Verneed.write_decode` is currently pending
and would benefit most from the trailing-array DSL kind: the chain
walking on `vna_next` / `vn_next` requires canonicalizing those
fields (vna_next = 16 except last = 0, vn_aux = 16, vn_cnt =
aux.size) so the writer emits canonical layout.  `.verneed` is
stored as `.raw` at the byte layer, so this gap doesn't block the
byte-roundtrip — it's a typed-side completeness item.

`SysVHashTable_decode_write` and `GnuHashTable_decode_write` for
the typed-side roundtrip are also pending and follow the same
pattern.  Estimated ~150-200 LOC each.

### Priority 5 — Code quality

#### 5.1 Op-level byte roundtrip lemmas — IN PROGRESS (Tier 1 + open core landed; all 4 shrinking ops' structural invariants DERIVED via generic `mapDynamicOp f`; the `mapDynamicOp` growers FULLY DERIVED — `hSplice` derived from the no-op base; the dynstr growers now have Tier-D capstones too — two-field factoring DERIVED, `hSplice` HYPOTHESIZED; ONLY remaining: derive the dynstr growers' `hSplice`)

A stronger replacement for the existing `_preserves_valid` lemmas:
prove `parse (encode (op e)) = .ok ⟨prepLayoutForEncode
(syncDtStrszInFile (op e)), _⟩` for each op.

`spliceDisjoint` is discharged by
`Encoder.prepLayoutForEncodeWith_produces_spliceRegionsDisjoint`
(landed; see §1.3a) — each op needs to establish the 5 structural
input invariants on its own output (`headerPhdrDisjoint` etc.),
which are parser-derivable for any op that doesn't widen the file.

**Dependent-type obstacle — RESOLVED via workaround (a).**  The
historical blocker: `Adapter.toElfFile` threaded `typed : ValidElfFile`
through dependent-type-bearing matches (`applyDynamic`'s match on
`typed.dynamic : Option (DynamicSection typed.dynstr)`).  A header-only
op like `setOsAbi` made the index become `({typed with header :=
…}).dynstr` instead of `typed.dynstr`, blocking the dependent match
from reducing even though the two are `rfl`-equal.

Commit `8ffe2cb` applied **workaround (a)**: the `applyX` helpers now
take the typed *fields* as explicit arguments (with the dependent
index `ds : StringSection` free), not the bundled `typed`.  This was
cheaper and lower-risk than the ~200 LOC estimate — the `applyX`
helpers had zero external callers, and `toElfFile`'s outer
`{ e with header := …, phdrs := … }` shape was preserved, so
`toElfFile_header`/`_phdrs` stayed `rfl` and the 4 CLI sites + 8
`AdapterRoundtrip` theorems were untouched.  `toElfFile template
(setOsAbi typed abi)` now reduces to `{ toElfFile template typed with
header := … }` by `rfl`.

**Tier map for op-level preservation (discovered while implementing).**
The ops split sharply by what their *byte-level* `toElfFile` output
looks like — driven by whether `patchDynamicEntries` (the positional
`.dynamic` rebuilder) changes the byte-level entry count:

* **Tier 1 — section positions unchanged (LANDED, commit `8ecaba0`).**
  Only `setOsAbi` (header ident byte) and `modifyExecstack`
  (PT_GNU_STACK phdr `flags`).  Adapter `sections` are definitionally
  the no-op output's; `_preserves_loadable` ships for both, via the
  reusable `isValid_of_phdrs_map` / `isLoadable_of_phdrs_map` helpers
  in `Patchelf/Elf/OpAdapterPreservation.lean`.
* **Tier 2/3 — byte-level `.dynamic` size changes (OPEN).**  Every
  other op.  `patchDynamicEntries`'s trailing `unless flags1Applied`
  / `unless debugApplied` / NEEDED-append blocks mean even the
  "trivial-looking" `noDefaultLib` / `addDebugTag` can *append* a
  DT_FLAGS_1 / DT_DEBUG entry (and `removeRpath`/`removeNeeded`
  *drop* entries).  So their raw `toElfFile` output has shifted
  section offsets and is **not laid out** — loadability is restored
  only by `encode`'s `growEOFWith` pass.  The meaningful theorem for
  these is therefore the full Tier D round-trip
  `parse (encode (toElfFile … (op typed)))`, NOT raw
  `_preserves_loadable`.  That needs: (i) the op establishes the 5
  structural input invariants (`headerPhdrDisjoint` etc.) on its
  grown output, then (ii) the §1.2 pipeline
  (`prepLayout_syncDtStrsz_preserves_loadable`) + the encoder-output
  `prepLayoutForEncodeWith_produces_spliceRegionsDisjoint` carry it to
  loadable bytes.  Each op needs a per-op `_produces_spliceRegionsDisjoint`
  on its `toElfFile` output (parser-derivable for ops that don't widen
  past `currentFileEnd`), composed with the landed §1.2 machinery.

The earlier workarounds (b) per-op congruence and (c) `EncodeCompatible`
transport are subsumed: (b) is now the `toElfFile_<op>_eq` commutation
lemma shape used in Tier 1; (c) is unnecessary given the direct
clause-by-clause transport.

**Tier 2/3 scaffold landed (commit `5c27487`).**  The reusable spine
for the round-trip is in `OpAdapterPreservation.lean`:

* `encode_roundtrip_via_normalized eo` — routes the round-trip through
  the encoder-normalized form `en := prepLayoutForEncode
  (syncDtStrszInFile eo)` (the structure `encodeBody` actually
  serializes, per `encode_eq`).  Reduces each op's Tier D to:
  `en.IsValid` (§1.2), `EncodePreconditions en`, and
  `encode eo = encode en` (pre-pass idempotence).
* `spliceRegionsDisjoint_of_structural eo` — discharges the hardest
  `EncodePreconditions` clause from the 5 structural input invariants
  on `syncDtStrszInFile eo` (§1.3a).

**Open core CLOSED (Obligations A/B/C).**  The three obligations on the
encoder-normalized form `en := prepLayoutForEncode (syncDtStrszInFile eo)`
are now proven:

* **A — `syncOk`** (`syncOk_of_normalized`, `ByteRoundtrip.lean`):
  `syncDtStrszInFile_establishes_dynStrszCoherent` (`Encoder.lean`) shows
  the first pre-pass writes every DT_STRSZ ← `dynstr.bytes.size` (so the
  output is coherent, given `dynstr.bytes.size < 2^64`), and
  `prepLayoutForEncode_preserves_dynStrszCoherent` shows the layout pass
  leaves it intact — `growEOFWith_dynamic`/`_dynstr` preserve the `.dynamic`
  content + `.dynstr`, and `syncDtAddrTagsInFile` is the identity on
  DT_STRSZ (`syncDtAddrEntry_eq_self_of_not_addressTag` — DT_STRSZ is not
  an address tag).  `syncDtStrszInFile_eq_id` then gives `syncOk`.
* **B — `hIdem`** (`encode_eq_encode_normalized`, `ByteRoundtrip.lean`):
  via `encode_eq` twice, reduces to `renormalize_eq_self` — `syncOk` (A)
  lets `syncDtStrszInFile en = en`, then `prepLayoutForEncode en = en`
  from `layoutAlreadyValid_of_spliceRegionsDisjoint ← en.spliceRegionsDisjoint`
  (`prepLayoutForEncode_{dynstr,eq_self_of_spliceRegionsDisjoint}`,
  `Encoder.lean`).
* **C — residual `EncodePreconditions`**
  (`encodePreconditions_of_layoutNormalized`, `OpAdapterPreservation.lean`):
  derives `syncOk` (A) + `spliceDisjoint` (§1.3a
  `spliceRegionsDisjoint_of_structural`) + four of the eight residual fields
  — `identValid`, `sizeFit`, `nullEmpty`, `headerFit_entry` — from the
  matching facts on `eo`, via the pre-encode pipeline's per-section
  `content`/`shdrSize`/`type` + `header.{ident,entry}` preservation
  (`{identValid,sizeFit,nullEmpty,headerFit_entry}_normalized_of_eo`).  This
  needed cracking the `growEOFWith` content-preservation getElem-dispatch:
  the per-element form's dependent `hj` bound defeats `cases`/`split`, so
  `growEOFWith_sections_content` is derived from a bound-free
  `growEOFWith_sections_map_content` (`map (·.content)`) equation — proved
  by `rw [growEOFWith.eq_1]; cases pageSize?` (kills the `match pageSize?`
  entanglement) `; simp only []` (zeta-reduces the `have`s) `; repeat' split`.
  Only the 4 position-bound families (`headerFit_phoff`/`shoff`, `phdrFit`,
  `shdrFit`) remain explicit hypotheses on `en` — genuinely NOT structurally
  derivable (`en`'s offsets come from `growEOFWith`'s unbounded `roundUp`
  arithmetic).  This is the sanctioned "file < 2^64" precondition — every
  real ELF satisfies it and the runtime `Validate.IsLoadableBytes` guards
  the pathological case at write time.

**Composed drivers + worked examples.**
`tierD_roundtrip` / `tierD_roundtrip_of_valid` / `tierD_roundtrip_of_eo_facts`
(`OpAdapterPreservation.lean`) glue A+B+C + the `IsValid` capstone
`prepLayout_syncDtStrsz_preserves_valid` (`Encoder.lean`) into
`parse (encode eo) = .ok ⟨en, _⟩`.  `_of_eo_facts` states its ENTIRE surface
on `eo` (validity + 6 structural disjointness invariants + section-0-NULL +
the four eo-level derived-field facts + only the 4 residual `< 2^64` position
bounds) — `spliceRegionsDisjoint_of_structural_eo` transports the structural
invariants through `syncDtStrszInFile` (the 3 previously-missing
`syncDtStrszInFile_{headerShdr,phdrShdr,shdrSection}Disjoint` lemmas now
exist).  The two shrinking ops ship full round-trips:
`toElfFile_{removeRpath,removeNeeded}_tierD_roundtrip`.

The content-preservation getElem-dispatch that previously blocked deriving
`identValid`/`sizeFit`/`nullEmpty` is now CRACKED (bound-free
`map (·.content)` equation, see Obligation C above), so all four
in-principle-derivable residual fields are derived; only the 4 position
bounds stay hypotheses.

**Reusable shrink-monotonicity core** (`SectionOps.lean`):
`updateSectionContent_{headerPhdr,headerShdr,phdrShdr,headerSection,
phdrSection,shdrSection}Disjoint_shrink` + `_section0Null` — a
`.dynamic`-rewrite with `newDyn.size ≤ oldDyn.size` preserves all 6
disjointness clauses + section-0-NULL (disjointness is monotone in the
section's `encodedSize = size · dynEntrySize`).  This is the layout core
every shrinking op's structural-invariant discharge needs.

**Shrinking-op per-op discharge — DONE for all 3, generic over `mapDynamicOp f`**
(`Patchelf/Elf/OpToElfFactor.lean`).  Every shrinking op is `mapDynamicOp e f`,
so the factoring/transport/capstone are now parameterized on `f`:

1. **Factoring** `toElfFile_mapDynamicOp_factor` — `toElfFile template
   (mapDynamicOp typed f) = (toElfFile template typed).updateSectionContent iDyn
   (.dynamic (patch bd (f td)))`.  Since `mapDynamicOp typed f` changes only
   `typed.dynamic`, `eo` and the no-op output share the whole `applyX` chain
   except `applyDynamic`'s argument; the single `.dynamic` update is pushed out
   through the 5 outer applies (`applyVersym`…`applyInterp`, each commuting since
   it targets a section ≠ the dynamic index — `updateSectionContent_comm` dodges
   the dependent-`Array.set` motive wall via getElem-characterization) and the
   header/phdrs override.  The 4× type-based outer-apply duplication is collapsed
   to 3 generic `applyTypeOpt_*` lemmas.  The no-op's dynamic content is
   identified as `patchDynamicEntries (template bytes) typed.dynamic` by
   `toElfFile_content_at_dynamicIdx` (a `calc`/`.trans` chain — plain `rw` on the
   giant `applyX` term whnf-times-out even at 1M heartbeats).
2. **Transport** `mapDynamicOp_structural_transport` — derives the 6 disjointness
   invariants + section-0-NULL on `eo` from the no-op output's via the `SectionOps`
   shrink core, taking the lone per-`f` fact `hSizeBound : (patch byteDyn (f d)).size
   ≤ (patch byteDyn d).size`.  The generic capstone
   `toElfFile_mapDynamicOp_tierD_roundtrip_derived` glues it into the full byte
   round-trip.
3. **Per-`f` size bounds** (`Adapter.lean`), the *relative* form (op vs. NO-OP on
   the *same* `byteDyn`; no parse-balance preconditions), proved on the
   compositional `patchDynamicEntries` refactor (pure loop fold `patchStep` +
   explicit tail-append helpers `appendSurplusNeeded`/`appendUnless`,
   byte-identical to the old `Id.run do` block, confirmed by 54/54 shell tests):
   * `patchDynamicEntries_stripRpath_size_le` — `stripRpath` nulls two TAIL
     `unless`-blocks at EQUAL cursor; lockstep fold tracks `ShrinkRel`.  Used by
     `removeRpath` (`toElfFile_removeRpath_tierD_roundtrip_derived`, the
     regression gate, statement + axioms unchanged) AND `modifyRPath.remove`
     (same `f`, free — `toElfFile_modifyRPath_remove_tierD_roundtrip_derived`).
   * `patchDynamicEntries_filterNeededBy_size_le` — `filterNeededBy` drops LOOP
     `needed` entries, so the op/no-op cursors run UNEQUAL; the lockstep relation
     is a POTENTIAL function `NeededRel = result.size + (needed.size − cursor)`
     (not `ShrinkRel`), with `appendSurplusNeeded_size_exact` + `tail_filterNeeded`
     collapsing the tail to the loop-end potential.  Used by `removeNeeded`
     (`toElfFile_removeNeeded_tierD_roundtrip_derived`).
   * `patchDynamicEntries_removeSoname_size_le` — `removeSoname` clears the soname
     TAIL field at EQUAL cursor (like `stripRpath`); a `ShrinkRel` variant
     (`ShrinkRelSoname` tracks the four non-soname applied-flags).  Used by
     `modifySoname.remove` (`toElfFile_modifySoname_remove_tierD_roundtrip_derived`).

   (The landed `Adapter.idForIn_proj_size_le` / `foldl_proj_size_le_add` bridges —
   the absolute-loop-bound route — are unused by these proofs but kept for any
   growing op needing the absolute form.)

**Reusable shrink-monotonicity core** (`SectionOps.lean`):
`updateSectionContent_{headerPhdr,headerShdr,phdrShdr,headerSection,
phdrSection,shdrSection}Disjoint_shrink` + `_section0Null` — a
`.dynamic`-rewrite with `newDyn.size ≤ oldDyn.size` preserves all 6
disjointness clauses + section-0-NULL (disjointness is monotone in the
section's `encodedSize = size · dynEntrySize`).  This is the layout core
every shrinking op's structural-invariant discharge needs.

The shrinking-op family is now COMPLETE (4/4: removeRpath, modifyRPath.remove,
removeNeeded, modifySoname.remove).

**Growing-op Tier-D — the `mapDynamicOp` growers are now FULLY DERIVED**
(`Patchelf/Elf/OpToElfFactorGrow.lean` + `Patchelf/Elf/GrowEOFDisjointOfBase.lean`).
A growing op widens a section's `encodedSize` at its ORIGINAL offset, so the three
per-section disjointness invariants (`{header,phdr,shdr}SectionDisjoint`) on the
op output `eo` genuinely BREAK — the shrink-monotonicity core (which needs
`newDyn.size ≤ oldDyn.size`) does NOT apply.  The resolution: `encode`'s
`prepLayoutForEncode`/`growEOFWith` pass RE-LAYS-OUT the file (flags the
overlapping grown sections stale, relocates them), so the NORMALIZED form
`prepLayoutForEncode (syncDtStrszInFile eo)` IS `spliceRegionsDisjoint` even
though `eo` is not.

1. **Keystone grow driver** `tierD_roundtrip_of_grown_eo`
   (`OpToElfFactorGrow.lean`) — identical to `tierD_roundtrip_of_eo_facts`
   EXCEPT it HYPOTHESIZES the normalized form's `spliceRegionsDisjoint`
   (`hSplice`) rather than deriving it from `eo`'s per-section disjointness
   (which a GROWN `eo` cannot supply).  Every OTHER `EncodePreconditions` field
   is DERIVED from `eo` via the existing `*_normalized_of_eo` helpers +
   `tierD_roundtrip_of_valid`.  The generic factoring
   `toElfFile_mapDynamicOp_factor` carries over VERBATIM (it is `f`-agnostic and
   size-agnostic).  This driver STAYS hypothesizing `hSplice` — it is the path
   the dynstr growers (`addNeeded` / `modify{RPath,Soname}.set`) REUSE: their
   Tier-D capstones in `OpToElfFactorGrowDynstr.lean` instantiate it (still
   hypothesizing `hSplice`, since the two-grown-section establisher is not done).
2. **`hSplice` DERIVED from the no-op base** (`GrowEOFDisjointOfBase.lean`,
   PLAN-GROWING-OPS §3 Commit 3 — the "very-high-risk" item, LANDED).  A
   `mapDynamicOp` grower widens ONE section (the dynamic section) at its FIXED
   offset (`updateSectionContent` preserves `.offset`).  Of the 6 structural
   invariants `prepLayoutForEncode_produces_spliceRegionsDisjoint` consumes:
   section-0-NULL + the 3 header/table clauses are size-INDEPENDENT (transport
   verbatim); `headerSectionDisjoint`/`phdrSectionDisjoint` survive growth via
   the LEFT disjunct (a section AFTER a region stays disjoint when it grows at a
   fixed offset) — needing only that the dynamic section sits at/after the ELF
   header and at/after the phdr table (`hDynAfterHeader`/`hDynAfterPhdr`, two
   honest offset side conditions, true for every real ELF, WEAKER than the
   shrink path's `hSizeBound`); `shdrSectionDisjoint`+`sectionsNonOverlapping`
   genuinely break, but `growEOFWith` RE-ESTABLISHES exactly those, so they are
   NOT preconditions.  Establisher `spliceRegionsDisjoint_of_grown_base`
   (`namespace Patchelf.Elf`) feeds the 6 transported invariants into
   `Adapter.spliceRegionsDisjoint_of_structural_eo`; the `mapDynamicOp`-level
   corollary `Adapter.mapDynamicOp_spliceRegionsDisjoint_of_base` (mirror of
   `mapDynamicOp_structural_transport`, reusing the `RemoveRpathFactorData`
   bundle) is the drop-in `hSplice` for the capstones; supporting lemmas
   `IntervalDisjoint_grow_right_of_le`,
   `ElfFile.updateSectionContent_sectionInterval_grow` (grow analogue of
   `_sectionInterval_shrink`) + `_headerSectionDisjoint_grow` /
   `_phdrSectionDisjoint_grow`.  Establisher + corollary are pure `[propext,
   Classical.choice, Quot.sound]` (no bv_decide).
3. **The two `mapDynamicOp` growers** (dynstr UNCHANGED, `.dynamic` grows by ≤1),
   MOVED into `GrowEOFDisjointOfBase.lean` and UPGRADED:
   `toElfFile_addDebugTag_tierD_roundtrip_derived` (`addDebugTag typed h ≡
   mapDynamicOp typed (·.addDebugTag)`, the DT_DEBUG `appendUnless` block) and
   `toElfFile_noDefaultLib_tierD_roundtrip_derived` (`≡ mapDynamicOp typed
   (·.setNoDefaultLib)`, the DT_FLAGS_1 block).  They NO LONGER hypothesize
   `hSplice` — they DERIVE it via the corollary, so their surface is the no-op
   base's 6 structural invariants (the SAME surface the shrink capstones use) +
   the 2 offset side conditions.  Axioms `[propext, Classical.choice,
   Quot.sound]` + 3 bv_decide, no `sorryAx`.

**Dynstr-growing ops — Tier-D capstones LANDED**
(`Patchelf/Elf/OpToElfFactorGrowDynstr.lean`, PLAN-GROWING-OPS §3 Commit 5).
`addNeeded` / `modifyRPath.set` / `modifySoname.set` use `growDynstrDynamicOp`
(the `.dynstr` section AND the `.dynamic` section both grow), so
`toElfFile_mapDynamicOp_factor` does NOT apply directly — they need a
genuinely-new TWO-FIELD factoring.

1. **The two-field factoring — DERIVED.**  The key insight that collapses the
   "two-field" problem to ONE field: `addNeeded typed lib h = { tg with dynamic
   := tg.dynamic.map (·.pushNeeded off) }` by `rfl`, where `tg :=
   (typed.growDynstr lib).1` is `typed` with its dynstr grown and `.dynsym` /
   `.dynamic` rebased.  The ENTIRE dynstr growth (+ rebases) is ABSORBED into the
   base `toElfFile template tg`, so the only delta from that base is a single
   `.dynamic` update at `iDyn` (the `pushNeeded` patch) — NO parallel
   `.strtab`-commutation suite was needed.  The keystone
   `toElfFile_dynamicMapMono_factor` generalizes `toElfFile_mapDynamicOp_factor`
   to a MONOMORPHIC `g : DynamicSection tg.dynstr → DynamicSection tg.dynstr`
   (the grow-dynstr mutator is `ds`-monomorphic, tied to `off : Fin
   tg.dynstr.size`; the proof only touches `.dynamic` as `Option.map`, so it
   reuses `innerChain_factor_general` verbatim); the three growers differ only
   in `g` (`pushNeeded off` / `setRpathTag fr off` / `setSonameOff off`).  Per-op
   factorings `toElfFile_{addNeeded,modifyRPath_set,modifySoname_set}_factor` +
   the content-at-`iDyn` corollary `toElfFile_addNeeded_content_at_dynamicIdx`
   (the building block for a future `hSplice` derivation) are `[propext,
   Quot.sound]`.
2. **The capstones — `hSplice` HYPOTHESIZED.**  The three capstones
   `toElfFile_{addNeeded,modifyRPath_set,modifySoname_set}_tierD_roundtrip_derived`
   (conclusions are the REAL ops' `parse (encode eo) = .ok ⟨…⟩`) instantiate the
   grow driver `tierD_roundtrip_of_grown_eo`, so they HYPOTHESIZE the normalized
   form's `spliceRegionsDisjoint` (`hSplice`, first-cut caliber) — UNLIKE the
   `mapDynamicOp` growers, whose `hSplice` is now DERIVED.  `[propext,
   Classical.choice, Quot.sound]` + 3 bv_decide, no `sorryAx`.

So every growing op named in PLAN-GROWING-OPS now has a Tier-D round-trip
capstone.

**The ONLY remaining §5.1 growing-ops item** (deferred to a dedicated session,
see `PLAN-GROWING-OPS.md`): DERIVE `hSplice` for the dynstr growers — this needs
a TWO-grown-section analogue of
`Adapter.mapDynamicOp_spliceRegionsDisjoint_of_base` (the `.dynstr` section grows
too, in addition to `.dynamic`).  `toElfFile_addNeeded_content_at_dynamicIdx` is
the building block, but the two-grown-section establisher is NOT done.  The §1.2
`updatePhdrsAfterMove_*` / `retargetPtPhdr_*` families remain reusable for any
op-level proof routing through `growEOFWith`.

§1.1 (Parser establishes `IsLoadable`) and §1.2
(`growEOFWith_preserves_loadable`, lifted to the end-to-end
`prepLayout_syncDtStrsz_preserves_loadable`) are both closed — they
provide the layout-pass preservation the Tier 2/3 op proofs compose
with.  The `updatePhdrsAfterMove_*` / `retargetPtPhdr_*` per-phdr lemma
families from §1.2 are reusable for any op-level proof that routes
through `growEOFWith`.

#### 5.2 Op-level `_observable` completeness

Every mutating op should have at least one observable theorem that
an adversarial identity function fails.  Current status per op:

| Op | Observable | Adversarial-identity rules out? |
|---|---|---|
| setOsAbi | yes + preserves_everything_else | yes (changed + no-other-fields-changed) |
| modifyExecstack | yes (set + clear) | yes (PF_X set on all PT_GNU_STACK) |
| removeRpath | yes | partial (∀ i, tag ≠ rpathish) |
| removeNeeded | yes + `_needed_size_lt` | yes (strictly smaller `needed` when a match existed) |
| clearSymbolVersion | yes (cleared + preserved_other) | yes |
| setInterpreter | yes | yes (.interp = encoded path) |
| addDebugTag | yes + `_observable_strong` | yes (present→preserved ∨ absent→`some 0` case-split) |
| noDefaultLib | yes + `_observable_strong` | yes (present→`v\|\|\|DF_1_NODEFLIB` ∨ absent→`DF_1_NODEFLIB` case-split) |
| addNeeded | yes | yes (`needed[0]` points at appended dynstr name; matches C++ front-insert) |
| addRpathEntry | yes | yes |
| modifyRPath.remove / .set | yes / yes + `_set_preserves` | yes (`.set`: dynstr.lookup off = name, identity can't fake; + non-corruption companion) |
| modifySoname.remove / .set | yes / yes + `_set_preserves` | yes (`.set`: dynstr.lookup off = name; + non-corruption companion) |
| replaceNeeded / replaceNeededReuse | yes / yes | yes |
| renameDynamicSymbols | yes | yes (`.st_name` points at appended `.dynstr` entry) |

§5.2 is now COMPLETE — every mutating op has at least one adversary-rejecting
observable.  The last gaps closed: `noDefaultLib_observable_strong` (the one
genuinely-missing case-split), and `modify{RPath,Soname}.set`'s non-corruption
companions `_set_preserves` (the `.set` ops already rejected identity via the
`dynstr.lookup off = name` clause; these add the "touches only its slot" axis
matching the fully-"yes" `setOsAbi`/`clearSymbolVersion` rows).  Earlier cycles
landed `addDebugTag_observable_strong` and `removeNeeded_needed_size_lt`.

#### 5.3 `SectionOps.lean` flatness — REOPENED

Originally marked DONE: the 530-LOC preservation infrastructure had
zero external callers and was deleted, leaving `SectionOps.lean` at
52 LOC.

It was re-grown to ~420 LOC in a later commit
(`7798b5d Lean port: close 5 ROADMAP items + SectionOps preservation
helpers`) when the §1.2 work made the helpers load-bearing again.

The current `SectionOps.lean` carries:

* Field projections: `updateSectionContent_{header, phdrs,
  sections_size, sections, getElem_ne, getElem_self, type, name,
  offset}`.
* Structural-index preservation: `updateSectionContent_{
  findUniqueTypeIdx, dynamicIdx, dynsymIdx, versymIdx, shstrtab,
  findIdxByName, dynstrIdx, interpIdx}`.
* Typed-accessor preservation under content-disjoint updates:
  `updateSectionContent_{contentAt_none, contentAt_some_ne,
  dynsym_eq, dynstr_eq, interp_eq}`.
* Index-disjointness: `dynstrIdx_target_ne_of_content_dynamic`,
  `shstrndx_ne_of_content_dynamic_of_dynstr`.
  (`dynsymIdx_target_ne_of_content_dynamic` was deleted in the
  2026-05 cleanup pass — zero external callers.)

These are the helpers §1.2's `_preserves_valid` proofs will reuse;
`syncDtAddrTagsInFile_preserves_spliceRegionsDisjoint` already
exercises a subset of them.  No further action needed unless the
§1.2 proofs need additional infrastructure.

#### 5.4 Splice/extract simp set + tactic — DONE (extended 2026-05)

`Patchelf/Elf/Tactic/SpliceSimproc{Attr,,Test}.lean` provide the
`[splice_simp]` simp set and a `simp_splice` macro
(`simp (discharger := splice_disch) only [splice_simp]`, where
`splice_disch` rewrites splice-buffer sizes and then runs `omega`).
The simp set is extensible via `@[splice_simp]`; new
`readUN_splice_*` or buffer-size lemmas attach without touching the
tactic file.

**2026-05 extension** (commit `7964eee`): `splice_disch` now also
rewrites `(writeArray Foo.write arr).size` → `arr.size * <bytes>`
via per-struct `@[simp]` lemmas in `Schemas.lean`
(`writeArray_{ProgramHeader,SectionHeader,Symbol,DynEntry,writeU16}_size`),
plus `Array.size_map` and the per-struct `Layout.{ehdr,phdr,shdr,dynEntry,symEntry}Size`
constants.  Effect: per-region preservation proofs no longer
need 4 `let buf0..buf3` aliases plus 4 `hBufNSz` hypotheses just
to expose buffer sizes to omega.  Four region preservation proofs
(`readU8_encode_in_{header,phdr,shdr,section}`) collapsed by ~88
LOC; the discharger is now general infrastructure for future
region proofs.

Original §5.4 estimate (~800 LOC bucket-1 collapse) was overstated;
combined original + 2026-05 delta is ~140 LOC across 7
splice-cascade sites + 4 region proofs in `ByteRoundtrip.lean`.
The remaining bucket-1 LOC is structural plumbing (per-section
foldl preservation, disjointness extraction from
`spliceRegionsDisjoint`) that isn't splice-cascade-shaped.

---

## Out of scope (not on the roadmap)

- **Cross-endian / ELF32.** The port models little-endian ELF64 only.
- **Architecture-specific relocations.** The port doesn't handle
  architecture-specific dynamic relocation types.
- **Shared-object creation from relocatable objects.** The port
  operates on existing ELF files; it doesn't link.
- **Non-Linux/non-glibc loaders.** `Validate.IsLoadableBytes` targets
  the Linux+glibc loader contract; musl, FreeBSD `rtld-elf`,
  bionic, Solaris `ld.so.1` are explicitly out of scope (see
  `REWRITE-PHASE-3-DESIGN.md` §1).  The port may produce binaries
  those loaders reject and we don't commit to the contrary.

---

For the typed-section algebra schema and the byte/typed split, see
[`lean/ARCHITECTURE.md`](../lean/ARCHITECTURE.md).
