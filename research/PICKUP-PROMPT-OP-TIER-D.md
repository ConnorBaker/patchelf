# Pickup prompt: all remaining work on the patchelf Lean 4 port

Single-shot handoff for a fresh agent with shell access, the Lean build
environment, and repo read access, but no other context.  Paste the fenced
block below into that agent.

Despite the filename, this is now the **comprehensive handoff for every
open item**, in priority order: §5.1 (op-level Tier D — the large one),
§5.2 (strengthen weak observables — small warm-up), §4.2 (trailing-array
DSL + forward roundtrips), §3.5b (PT_GNU_STACK append).  The byte-level
codec, the layout engine (`growEOF` + fresh-PT_LOAD), the §1.1 parser
`IsLoadable`, the §1.2 `_preserves_valid` / `_preserves_loadable` ladders,
and the §5.1 open core (A/B/C) are all CLOSED.

**§5.1 update (latest):** **all FOUR shrinking ops** now have their op-output
structural invariants DERIVED (criterion 2 met) — see
`Patchelf/Elf/OpToElfFactor.lean`.  The factoring/transport/capstone are now
GENERIC over `mapDynamicOp f` (`toElfFile_mapDynamicOp_factor` /
`mapDynamicOp_structural_transport` / `toElfFile_mapDynamicOp_tierD_roundtrip_derived`),
instantiated by `removeRpath` (`toElfFile_removeRpath_tierD_roundtrip_derived`,
the regression gate), `modifyRPath.remove`
(`toElfFile_modifyRPath_remove_tierD_roundtrip_derived`, free), `removeNeeded`
(`toElfFile_removeNeeded_tierD_roundtrip_derived`), and `modifySoname.remove`
(`toElfFile_modifySoname_remove_tierD_roundtrip_derived`).  The per-`f` size
bounds live in `Adapter.lean`: `patchDynamicEntries_stripRpath_size_le`
(`ShrinkRel`), `patchDynamicEntries_filterNeededBy_size_le` (the `NeededRel`
potential function), and `patchDynamicEntries_removeSoname_size_le`
(`ShrinkRelSoname`).  The shrinking-op family is now complete (4/4).

**Growing ops — the `mapDynamicOp` growers are now FULLY DERIVED**
(`Patchelf/Elf/OpToElfFactorGrow.lean` + `Patchelf/Elf/GrowEOFDisjointOfBase.lean`).
A growing op widens a section's `encodedSize` at its original offset, so the
per-section disjointness invariants on `eo` genuinely BREAK and the shrink core
cannot apply; `encode`'s `prepLayoutForEncode`/`growEOFWith` re-lays-out the file
to produce a disjoint NORMALIZED form.  The keystone grow driver
`tierD_roundtrip_of_grown_eo` mirrors `tierD_roundtrip_of_eo_facts` but
HYPOTHESIZES the normalized form's `spliceRegionsDisjoint` (`hSplice`) and
derives every other `EncodePreconditions` field from `eo`.
`GrowEOFDisjointOfBase.lean` now DERIVES `hSplice` from the no-op base for the
two `mapDynamicOp` growers (PLAN-GROWING-OPS §3 Commit 3, the "very-high-risk"
item, LANDED): a `mapDynamicOp` grower widens ONE section at its FIXED offset, so
the size-independent invariants transport verbatim and
`headerSectionDisjoint`/`phdrSectionDisjoint` survive via the LEFT disjunct,
given two honest offset side conditions (the dynamic section sits after the
header / phdr table — `hDynAfterHeader`/`hDynAfterPhdr`, WEAKER than the shrink
path's `hSizeBound`).  Establisher `spliceRegionsDisjoint_of_grown_base` +
corollary `Adapter.mapDynamicOp_spliceRegionsDisjoint_of_base`; the two capstones
`toElfFile_{addDebugTag,noDefaultLib}_tierD_roundtrip_derived` MOVED here and were
UPGRADED to no longer hypothesize `hSplice` — their surface is now the no-op
base's 6 structural invariants (same as the shrink capstones) + the 2 offset side
conditions.  The driver `tierD_roundtrip_of_grown_eo` STAYS in
`OpToElfFactorGrow.lean` hypothesizing `hSplice` (reused by the dynstr growers).

**Dynstr growers — Tier-D capstones LANDED (hSplice HYPOTHESIZED; the two-field
factoring DERIVED)** (`Patchelf/Elf/OpToElfFactorGrowDynstr.lean`,
PLAN-GROWING-OPS §3 Commit 5).  `addNeeded` / `modifyRPath.set` /
`modifySoname.set` use `growDynstrDynamicOp` (dynstr AND dynamic both grow).  The
genuinely-new artifact, the **Strategy-A two-field factoring**, is DERIVED: the
key insight collapses "two fields" to one — `addNeeded typed lib h = { tg with
dynamic := tg.dynamic.map (·.pushNeeded off) }` by `rfl`, where `tg :=
(typed.growDynstr lib).1` ABSORBS the entire dynstr growth + dynsym/dynamic
rebases into the base `toElfFile template tg`, leaving a single `.dynamic` update
at `iDyn` (NO parallel `.strtab`-commutation suite needed).  Keystone
`toElfFile_dynamicMapMono_factor` generalizes `toElfFile_mapDynamicOp_factor` to
a MONOMORPHIC `g` on `.dynamic` (reusing `innerChain_factor_general` verbatim);
per-op factorings `toElfFile_{addNeeded,modifyRPath_set,modifySoname_set}_factor`
+ corollary `toElfFile_addNeeded_content_at_dynamicIdx`.  The three capstones
`toElfFile_{addNeeded,modifyRPath_set,modifySoname_set}_tierD_roundtrip_derived`
instantiate `tierD_roundtrip_of_grown_eo`, so they HYPOTHESIZE the normalized
form's `spliceRegionsDisjoint` (`hSplice`) — UNLIKE the `mapDynamicOp` growers,
whose `hSplice` is derived.  **So every growing op named in PLAN-GROWING-OPS now
has a Tier-D capstone.**  **The ONLY remaining §5.1 growing-ops item** (the
next concrete task): DERIVE `hSplice` for the dynstr growers — a
TWO-grown-section analogue of `Adapter.mapDynamicOp_spliceRegionsDisjoint_of_base`
(the `.dynstr` section grows too); `toElfFile_addNeeded_content_at_dynamicIdx` is
the building block, but the establisher is NOT done.  See `PLAN-GROWING-OPS.md`.

---

```
You are picking up the patchelf Lean 4 port.  Everything through the
end-to-end pre-encode `_preserves_loadable` ladder and the §5.1 op-level
"open core" (Obligations A/B/C) is DONE and machine-checked.  Pick ONE of
the open tasks below (they are independent); §5.1 is the canonical/largest,
§5.2 is the easiest warm-up.

## Orientation reads (do these first, in order)

1. `/home/cbaker2/ext-sources/patchelf/lean/STATUS.md` — top banner (what
   works end-to-end) + "Known gaps" (esp. the "Op-level Tier D" bullet).
2. `/home/cbaker2/ext-sources/patchelf/lean/ARCHITECTURE.md` — the
   three-layer stack (byte layer ↔ typed algebra via the Adapter), the
   validity ladder (IsValid ⊂ IsLoadable ⊂ IsFullyValid), the encoder
   pipeline, and the op convention.  Skim if short on time; the Tier-D
   reader below is enough for §5.1.
3. `/home/cbaker2/ext-sources/patchelf/research/ROADMAP.md` — "Picking up
   work" (the open menu) + the specific §-section for your chosen task.
4. `/home/cbaker2/ext-sources/patchelf/lean/INVENTORY.md` — declaration
   index by file; grep it for any lemma name you need.

## Working directory and environment

    cd /home/cbaker2/ext-sources/patchelf/lean
    nix develop ..#lean -c lake build              # baseline; expect 113 jobs clean
    nix develop ..#lean -c bash tests/run.sh       # 54/54 shell tests
    grep -rnE "(:= *sorry|by *sorry| sorry$)" Patchelf/   # zero; keep it

`lake build` from cold is a few minutes — set a generous timeout.
Build one module fast with `nix develop ..#lean -c lake build Patchelf.Elf.<Mod>`.
Develop new lemmas in a scratch file (`Patchelf/Scratch.lean`) that
`import`s the relevant module for a fast feedback loop, then transplant
into the real file.  DELETE the scratch file before committing (it is
gitignored, but don't leave it around).

## Hard constraints (all tasks)

- No `sorry`s, even temporarily.  If blocked, document the obstacle as
  `-- TODO §<n>: <what you tried, what failed>` and stop with a writeup.
- Don't weaken or delete any existing theorem/test.  113 lake jobs must
  build; 54 shell tests must pass.
- Don't re-introduce the `Adapter.toElfFile` bundling, and keep its outer
  `{ e with header := …, phdrs := … }` shape — `toElfFile_header`/`_phdrs`
  are `rfl` and load-bearing.
- `Encoder.encode` / `encodeBody` are `@[irreducible]`; use the `_eq`
  companion lemmas to unfold (removing the attribute times out per-byte
  proofs at >32M heartbeats).
- Small focused commits in the existing style (`git log --oneline -15`).
  End commit messages with the Co-Authored-By line the repo uses.  Update
  STATUS.md + ROADMAP.md + this prompt when you change the open-work state.

## Tactics / gotchas (learned the hard way — read before any encoder/layout proof)

- DEPENDENT MOTIVE: `cases`/`rw`/`unfold … at hj` fails ("motive is not
  type correct") when a hypothesis `hj` carries a length bound depending on
  the rewritten term.  Two escapes: (a) do the case-split ladder WITHOUT a
  dependent `hj` in context (see `growEOFWith_dynstr`); (b) state the fact
  as a bound-FREE whole-array equation, e.g. `map (·.content)` instead of a
  per-element `getElem` (see `growEOFWith_sections_map_content`).  `subst`
  an index/Option witness rather than `rw`-ing it (memory:
  `lean-subst-not-rw-dependent-motive`).
- DISPATCH over `growEOFWith`'s 5 inlined branches: it inlines its branches
  behind `let`/`have`, so `split` can't descend.  For PROJECTION lemmas use
  the `by_cases hLay / cases hLast / by_cases hExt / by_cases hAdd` ladder +
  `simp only [..., ↓reduceIte] <;> first | rfl | exact <branch_lemma>` (the
  `<;>` tolerates branches simp already closed).  To get past the
  `match pageSize?` entanglement in a bound-free goal, use
  `rw [growEOFWith.eq_1]; cases pageSize?; simp only []; repeat' split`.
  (Memory: `groweofwith-dispatch-idiom`.)
- SCRATCH vs IN-FILE: dispatch-shaped `simp only [hCond, ↓reduceIte]`
  cascades fire in the real file but NOT in a standalone scratch importing
  the olean.  Develop sub-lemmas in scratch; transplant dispatch-shaped
  proofs into the file before judging them.
- `Id.run do` blocks (`let mut` + `for`): convert `forIn` via
  `Array.forIn_eq_foldlM` (Id collapses `foldlM`; steps are `.yield`);
  the trailing `while`/`unless` desugars to nested `__do_jp` join-points
  (brittle — consider `mvcgen` from `Std.Tactic.Do`, or refactor the def).
- `#print axioms <thm>` on any headline theorem must show only
  `[propext, Classical.choice, Quot.sound]` + the 3 `bv_decide`
  readU/writeU axioms — no `sorryAx`.

=====================================================================
## TASK §5.1 — op-level Tier D: per-op fact discharge (CANONICAL, LARGEST)
=====================================================================

GOAL: make a mutating op's full byte round-trip self-contained —
`parse (encode (toElfFile template (op typed))) = .ok ⟨normalized, _⟩` —
by DERIVING the op output's facts from the typed op + template, instead of
taking them as hypotheses.  **All FOUR shrinking ops are DONE**, via generic
`mapDynamicOp f` machinery: `removeRpath`, `modifyRPath.remove`, `removeNeeded`,
`modifySoname.remove`.  **The two `mapDynamicOp` GROWERS are now FULLY DERIVED
too** (`addDebugTag`/`noDefaultLib`): `Patchelf/Elf/GrowEOFDisjointOfBase.lean`
DERIVES the normalized form's `spliceRegionsDisjoint` (`hSplice`) from the no-op
base, so the capstones no longer hypothesize it — their surface is now the no-op
base's 6 structural invariants (same as the shrink capstones) + 2 honest offset
side conditions (the dynamic section sits after the header / phdr table, WEAKER
than the shrink path's `hSizeBound`).  The generic grow driver
`tierD_roundtrip_of_grown_eo` (`Patchelf/Elf/OpToElfFactorGrow.lean`) STILL
hypothesizes `hSplice` — that is the path the dynstr growers reuse.

**The `growDynstrDynamicOp` growers now have Tier-D capstones too**
(`Patchelf/Elf/OpToElfFactorGrowDynstr.lean`, PLAN-GROWING-OPS §3 Commit 5,
LANDED): `addNeeded` / `modifyRPath.set` / `modifySoname.set` (dynstr AND dynamic
both grow).  The genuinely-new **Strategy-A two-field factoring** is DERIVED — the
key insight collapses "two fields" to ONE via the `rfl` identity `addNeeded typed
lib h = { tg with dynamic := tg.dynamic.map (·.pushNeeded off) }` (where `tg :=
(typed.growDynstr lib).1` ABSORBS the entire dynstr growth + rebases into the
base `toElfFile template tg`), so NO parallel `.strtab`-commutation suite was
needed; the keystone `toElfFile_dynamicMapMono_factor` generalizes
`toElfFile_mapDynamicOp_factor` to a MONOMORPHIC `g` on `.dynamic`, reusing
`innerChain_factor_general` verbatim.  The three capstones instantiate
`tierD_roundtrip_of_grown_eo` and so still HYPOTHESIZE `hSplice` (unlike the
`mapDynamicOp` growers, whose `hSplice` is derived).  **So every growing op named
in PLAN-GROWING-OPS now has a Tier-D capstone.**

**Next up (the next concrete task):** DERIVE `hSplice` for the dynstr growers — a
TWO-grown-section analogue of `Adapter.mapDynamicOp_spliceRegionsDisjoint_of_base`
(the `.dynstr` section grows too, in addition to `.dynamic`).  The building block
`toElfFile_addNeeded_content_at_dynamicIdx` (content-at-`iDyn` corollary) is
landed in `OpToElfFactorGrowDynstr.lean`, but the two-grown-section establisher is
NOT done.  See `PLAN-GROWING-OPS.md` for the full design.  Read
`Patchelf/Elf/OpToElfFactor.lean`, `Patchelf/Elf/OpToElfFactorGrow.lean`,
`Patchelf/Elf/GrowEOFDisjointOfBase.lean`, AND
`Patchelf/Elf/OpToElfFactorGrowDynstr.lean` end-to-end first — the generic
factoring/transport/capstone + per-apply commutation suite are reusable for any
`mapDynamicOp f`; a further `mapDynamicOp` op would need only its `Adapter.lean`
size bound (shrink) or the grow driver + the no-op-base `hSplice` derivation
(grow); a `growDynstrDynamicOp` op reuses the two-field factoring keystone
`toElfFile_dynamicMapMono_factor` (the dynstr-grower `hSplice` derivation is the
open item).

### Tier-D readers (after orientation)

- `Patchelf/Elf/OpToElfFactor.lean` — **the generic `mapDynamicOp f` solution;
  read FIRST for §5.1.**  §A `updateSectionContent` algebra (`_comm`, `_set_set`,
  content congruences, `applyOpt`-commutation — all dodging the
  dependent-`Array.set` motive wall); the 3 generic `applyTypeOpt_*` lemmas (4×
  outer-apply collapse) + per-apply commutation / `dynamicIdx` / `sections.size`
  / content-at-`iDyn` wrappers (interp + applyDynamic separate);
  `toElfFile_mapDynamicOp_factor` + `toElfFile_content_at_dynamicIdx`;
  `mapDynamicOp_structural_transport`; the generic capstone
  `toElfFile_mapDynamicOp_tierD_roundtrip_derived`; then the 3 op instantiations
  (`removeRpath` is the regression gate — statement + axioms unchanged).  For a
  new shrink op: add its `patchDynamicEntries_<f>_size_le` in `Adapter.lean` and
  instantiate the generic capstone (~5 lines).
- `Patchelf/Elf/OpToElfFactorGrow.lean` — **the GROWING-op companion; read after
  OpToElfFactor.lean.**  The keystone grow driver `tierD_roundtrip_of_grown_eo`
  (HYPOTHESIZES the normalized form's `spliceRegionsDisjoint` `hSplice` — read its
  docstring on why a grown `eo` can't supply it and how the layout pass produces
  it — then derives every other `EncodePreconditions` field from `eo`).  This
  driver STAYS hypothesizing `hSplice`; it is the path `addNeeded` will reuse.
- `Patchelf/Elf/GrowEOFDisjointOfBase.lean` — **the `mapDynamicOp`-grower
  `hSplice` derivation; read after OpToElfFactorGrow.lean.**  DERIVES `hSplice`
  from the no-op base: a `mapDynamicOp` grower widens ONE section at its FIXED
  offset, so the size-independent invariants transport verbatim and the two
  per-section clauses survive via the LEFT disjunct given 2 honest offset side
  conditions (`spliceRegionsDisjoint_of_grown_base` + the `mapDynamicOp`-level
  corollary `Adapter.mapDynamicOp_spliceRegionsDisjoint_of_base`, a mirror of
  `mapDynamicOp_structural_transport` reusing `RemoveRpathFactorData`).  The two
  `mapDynamicOp` grower capstones `toElfFile_{addDebugTag,noDefaultLib}_tierD_roundtrip_derived`
  live here, UPGRADED to derive `hSplice` (no longer hypothesize it).  For a new
  `mapDynamicOp` grower: instantiate the grow driver + supply the no-op-base
  structural invariants + 2 offset side conditions through this corollary (~5–10
  lines).
- `Patchelf/Elf/OpToElfFactorGrowDynstr.lean` — **the dynstr-GROWER (two-field)
  companion; read after GrowEOFDisjointOfBase.lean.**  Tier-D for the
  `growDynstrDynamicOp` growers `addNeeded` / `modifyRPath.set` /
  `modifySoname.set` (dynstr AND dynamic both grow).  The DERIVED Strategy-A
  two-field factoring: read the file header for the `rfl` insight that collapses
  "two fields" to one (`addNeeded typed lib h = { tg with dynamic :=
  tg.dynamic.map (·.pushNeeded off) }`, the dynstr growth ABSORBED into the base
  `tg := (typed.growDynstr lib).1`).  Keystone `toElfFile_dynamicMapMono_factor`
  (monomorphic-`g` generalization of `toElfFile_mapDynamicOp_factor`, reuses
  `innerChain_factor_general` verbatim) + per-op factorings
  `toElfFile_{addNeeded,modifyRPath_set,modifySoname_set}_factor` + the
  content-at-`iDyn` corollary `toElfFile_addNeeded_content_at_dynamicIdx` (the
  building block for the open `hSplice` derivation) + the three capstones
  `toElfFile_{addNeeded,modifyRPath_set,modifySoname_set}_tierD_roundtrip_derived`
  (instantiate `tierD_roundtrip_of_grown_eo`, so they HYPOTHESIZE `hSplice` — the
  open follow-up is the TWO-grown-section establisher; `PLAN-GROWING-OPS.md`).
- `Patchelf/Elf/OpAdapterPreservation.lean` — the WHOLE file.  Home base.
  In order: Tier-1 worked examples (`toElfFile_setOsAbi_*`,
  `_modifyExecstack_*`); the scaffold (`encode_roundtrip_via_normalized`,
  `spliceRegionsDisjoint_of_structural{,_eo}`); the Obligation-C package
  `encodePreconditions_of_layoutNormalized` (read its docstring); the
  drivers `tierD_roundtrip` / `tierD_roundtrip_of_valid` /
  `tierD_roundtrip_of_eo_facts`; and the worked examples
  `toElfFile_{removeRpath,removeNeeded}_tierD_roundtrip` (note what they
  take as HYPOTHESES — that is your work).
- `Patchelf/Elf/SectionOps.lean` — the shrink-monotonicity core (search
  `_Disjoint_shrink`, `_section0Null`, `updateSectionContent_sectionInterval_shrink`).
- `Patchelf/Elf/Adapter.lean` — `toElfFile` (~432), `patchDynamicEntries`
  (~255), and the loop-size bridges `foldl_proj_size_le_add` (~201) /
  `idForIn_proj_size_le` (~222).
- `Patchelf/Elf/Encoder.lean` — the §1.2/A/B capstones + the
  `syncDtStrszInFile_*Disjoint` transport family + the
  `prepLayout_syncDtStrsz_sections_*` pipeline lemmas.

### Use the right driver

`tierD_roundtrip_of_eo_facts` states its ENTIRE surface on `eo := toElfFile
template (op typed)` — validity, the 6 disjointness invariants +
section-0-NULL, the four eo-level derived-field facts
(`identValid`/`sizeFit`/`nullEmpty`/`headerFit_entry`), and only the 4
residual `< 2^64` position bounds on the normalized form.  So you never
touch `syncDtStrszInFile eo` or the layout output directly — everything is
on `eo`, except the 4 position bounds (the sanctioned "file < 2^64"
precondition; the runtime `Validate.IsLoadableBytes` guards the
pathological case at write time, so leaving them as a hypothesis is fine).

### What each op still owes, and the order to discharge it

1. EASY: `eo.IsValid`, `(eo.phdrs.size+1) < UInt16.size`, `eo.dynstr = some
   ds`, `ds.bytes.size < UInt64.size`.  `toElfFile_{header,phdrs}` are
   `rfl`, so phdrs/header come from `typed`; `eo.IsValid` from the typed
   algebra / AdapterRoundtrip; `eo.dynstr` by tracing `applyDynstr`; the
   `< 2^64` fit is the explicit "file < 2^64" precondition.
2. EASY: the four eo-level derived-field facts — these are about a freshly
   `toElfFile`-built `eo`; `nullEmpty`/`sizeFit`/`identValid`/`headerFit_entry`
   on `eo` are parser-derivable from the template (the op doesn't touch
   SHT_NULL sections / the ident bytes / the entry point).
3. THE SUBSTANCE: the 6 structural disjointness invariants + section-0-NULL
   on `eo`.  For a SHRINKING op (`removeRpath`/`removeNeeded`, which only
   DROP `.dynamic` entries) the reusable shrink-monotonicity lemmas
   (`SectionOps.updateSectionContent_*Disjoint_shrink`) transport these from
   the no-op output's invariants — via two op-specific lemmas, **both DONE for
   `removeRpath` in `OpToElfFactor.lean`** (mirror them for `removeNeeded`):

   (a) **`patchDynamicEntries` output-size bound** — the RIGHT target is the
       *relative* form `(patchDynamicEntries byteDyn (op-shrink d)).size ≤
       (patchDynamicEntries byteDyn d).size` (op output vs. NO-OP output on the
       SAME `byteDyn`), NOT the absolute `≤ byteDyn.size`.  The relative form
       is what the shrink lemmas consume and needs NO parse-balance
       preconditions (the NEEDED-balance / single-DT_NULL worry is moot).
       SHIPPED for `removeRpath`: `patchDynamicEntries_stripRpath_size_le`
       (`Adapter.lean`), proved on a **compositional `patchDynamicEntries`
       refactor** (pure loop fold `patchStep` + tail helpers `appendSurplusNeeded`
       /`appendUnless`, byte-identical to the old do-block — no `__do_jp` walk,
       no `mvcgen`) via a lockstep `Array.foldl_rel` + tail bound.  For
       `removeNeeded`: prove the analogous `filterNeededBy` relative bound
       (the loop's NEEDED arm pushes fewer entries when typed.needed is
       filtered; soname/flags1/debug/rpath/runpath unchanged).

   (b) **factor `eo = (toElfFile template typed).updateSectionContent iDyn
       (.dynamic newDyn)`** on the NO-OP output — DONE:
       `toElfFile_removeRpath_factor`.  `toElfFile` is a chain of `applyX`
       updates; a shrinking op changes only `applyDynamic`'s arg, so the lone
       `.dynamic` update is pushed out through the outer `applyX` chain
       (`OpToElfFactor.lean` §B per-apply commutation lemmas, all reusable for
       `removeNeeded`).  The no-op's dynamic content is identified by
       `toElfFile_content_at_dynamicIdx`, and `removeRpath_structural_transport`
       + the capstone glue it together.

   GROWING ops widen `.dynamic`/`.dynstr`, so the shrink lemmas don't apply —
   the per-section disjointness invariants on `eo` genuinely BREAK and `encode`'s
   `prepLayoutForEncode`/`growEOFWith` re-lays-out the file to produce the
   disjoint normalized form.  **The two `mapDynamicOp` growers are now FULLY
   DERIVED** (`OpToElfFactorGrow.lean` + `GrowEOFDisjointOfBase.lean`): the
   keystone grow driver `tierD_roundtrip_of_grown_eo` HYPOTHESIZES the normalized
   form's `spliceRegionsDisjoint` (`hSplice`) and derives the rest from `eo`, and
   `GrowEOFDisjointOfBase.lean` DERIVES that `hSplice` from the no-op base —
   `noDefaultLib`/`addDebugTag` (which APPEND a DT_FLAGS_1/DT_DEBUG entry,
   `.dynamic` +≤1, dynstr unchanged) now close with `hSplice` derived, carrying
   only the no-op base's 6 structural invariants + 2 honest offset side
   conditions.  The mechanism: a `mapDynamicOp` grower widens ONE section at its
   FIXED offset, so size-independent invariants transport verbatim and
   `headerSectionDisjoint`/`phdrSectionDisjoint` survive via the LEFT disjunct
   given the dynamic section sits after the header / phdr table;
   `shdrSectionDisjoint`/`sectionsNonOverlapping` are re-established by
   `growEOFWith`.  **The `growDynstrDynamicOp` growers now have Tier-D capstones
   too** (`OpToElfFactorGrowDynstr.lean`, PLAN-GROWING-OPS §3 Commit 5, LANDED):
   `addNeeded` / `modifyRPath.set` / `modifySoname.set` (both `.dynstr` and
   `.dynamic` grow, so `toElfFile_mapDynamicOp_factor` does NOT apply directly).
   The DERIVED **Strategy-A two-field factoring** collapses "two fields" to ONE
   via the `rfl` identity `addNeeded typed lib h = { tg with dynamic :=
   tg.dynamic.map (·.pushNeeded off) }` (the dynstr growth + rebases ABSORBED
   into the base `tg := (typed.growDynstr lib).1`), so NO parallel
   `.strtab`-commutation suite was needed; keystone
   `toElfFile_dynamicMapMono_factor` generalizes `toElfFile_mapDynamicOp_factor`
   to a MONOMORPHIC `g` on `.dynamic`, reusing `innerChain_factor_general`
   verbatim.  The three capstones instantiate `tierD_roundtrip_of_grown_eo`, so
   they HYPOTHESIZE `hSplice` (unlike the `mapDynamicOp` growers, whose `hSplice`
   is derived).  REMAINING (the next concrete task, deferred — see
   `PLAN-GROWING-OPS.md`): DERIVE `hSplice` for these dynstr growers — a
   TWO-grown-section analogue of
   `Adapter.mapDynamicOp_spliceRegionsDisjoint_of_base` (the `.dynstr` section
   grows too); `toElfFile_addNeeded_content_at_dynamicIdx` is the building block,
   but the establisher is NOT done.  (The other `growDynstrDynamicOp`-shaped ops
   — `addRpathEntry`, `setInterpreter`, `replaceNeeded` grow path,
   `renameDynamicSymbols` — would reuse the same keystone but are not yet wired
   up.)

### §5.1 success criteria

1. `lake build` clean, zero `sorry`s; 54/54 shell tests.
2. At least one shrinking op (`removeRpath`/`removeNeeded`) has its `eo`
   structural invariants DERIVED rather than hypothesized — i.e. a
   `parse (encode (toElfFile …)) = .ok …` with no structural-invariant
   hypotheses (a "file < 2^64" precondition on the 4 position bounds is OK).
   **DONE for all four shrinking ops** — `removeRpath` / `modifyRPath.remove` /
   `removeNeeded` / `modifySoname.remove` (`OpToElfFactor.lean`), via the generic
   `mapDynamicOp f` capstone.  The shrink family is complete; the two
   `mapDynamicOp` growers (`addDebugTag`/`noDefaultLib`) are also FULLY DERIVED
   (`GrowEOFDisjointOfBase.lean` derives `hSplice` from the no-op base; the
   capstones carry only the no-op base's 6 structural invariants + 2 honest
   offset side conditions).  The `growDynstrDynamicOp` growers (`addNeeded`,
   `modify{RPath,Soname}.set`) now have Tier-D capstones too
   (`OpToElfFactorGrowDynstr.lean`) — the two-field factoring is DERIVED, but the
   capstones still HYPOTHESIZE `hSplice`.  **So every growing op named in
   PLAN-GROWING-OPS now has a Tier-D capstone.**  Next is to DERIVE `hSplice` for
   the dynstr growers — the TWO-grown-section establisher.
3. STATUS.md + ROADMAP.md updated; refresh this prompt.

=====================================================================
## TASK §5.2 — strengthen weak `_observable` theorems (SMALL WARM-UP)
=====================================================================

Pure typed-algebra; no layout/encoder reasoning.  Each mutating op should
have an observable theorem that an adversarial identity function FAILS.
The §5.2 table in ROADMAP.md flags the weak/missing rows: `removeNeeded`
(weak — identity on files without the lib), `addDebugTag` (weak — identity
on files already having DT_DEBUG), `noDefaultLib` (`?`), `modifyRPath.set`
(`?`), `modifySoname.set` (`?`).  Read an existing strong example
(`setOsAbi_*`, `clearSymbolVersion_*`, `addNeeded_*` in `Elf/Ops/`) and the
combinators in `Elf/ObservableCombinators.lean`, then add a
post-condition theorem per weak op stating the observable change precisely
(e.g. `noDefaultLib` ⇒ `flags1` has the DF_1_NODEFLIB bit `0x800` set —
see `DynamicSection.setNoDefaultLib`; `modifyRPath.set` ⇒ `rpath = some
<the new offset>`).  Files: `Elf/Ops/*.lean`.

=====================================================================
## TASK §4.2 — trailing-array DSL field kind + forward roundtrips
=====================================================================

Typed-side completeness; does NOT affect the byte roundtrip (`.verneed`/
`.hash`/`.gnu.hash` are stored as `.raw` at the byte layer).  Read
`research/RESEARCH-SCHEMA-DSL.md` §"DSL v3" (the design sketch) and
`Patchelf/Elf/SchemaDSL.lean` (the `elf_schema` elaborator) +
`Patchelf/Elf/Schemas.lean` (the 7 invocations + the 3 hand-written
writers: `Verneed`, `SysVHashTable`, `GnuHashTable`).  Add a `trailing
Array<SubType>` field kind so those become pure DSL invocations, then emit
the forward roundtrips `Verneed.write_decode` (needs canonicalizing
`vna_next`/`vn_next`/`vn_cnt`), `SysVHashTable_decode_write`,
`GnuHashTable_decode_write`.  ~150–200 LOC each.  Independent of §5.1.

=====================================================================
## TASK §3.5b — PT_GNU_STACK append when missing (SMALL FEATURE GAP)
=====================================================================

C++-parity: `set-execstack` on a binary WITHOUT a PT_GNU_STACK phdr is
currently a no-op (`Ops/Execstack.lean` only maps over existing phdrs);
C++ appends one.  The phdr-array-grow machinery from §3.5a is in place;
appending is mechanically like `freshPtLoad` in `GrowEOF.lean` — construct a
PT_GNU_STACK phdr (PF_R | PF_W, zero offset/size) and bump `phnum`.  Add a
shell test mirroring 53/54.  Lowest priority; do only if a use case needs it.
```

---

## Notes for the human (not the agent)

This prompt was broadened from a §5.1-only handoff to cover **all** open
roadmap items so a fresh-context agent can take the whole remaining queue.
Priority/size ordering: §5.1 (large, the substance) ≫ §4.2 (medium,
independent typed-side) > §5.2 (small warm-up) > §3.5b (small, optional).

State of §5.1 (the deep one): Obligations A/B/C are closed; the
content-preservation getElem-dispatch wall is cracked; four of eight
residual `EncodePreconditions` fields are derived; the reusable
shrink-monotonicity layout core and the `Id`-forIn loop-size bridges are
landed; the full `eo`-level driver `tierD_roundtrip_of_eo_facts` is in place.

**`removeRpath` is now fully discharged** (`Patchelf/Elf/OpToElfFactor.lean`):
its op-output structural invariants are DERIVED, not hypothesized — criterion
2 met.  Both formerly-open lemmas landed: (1) the `patchDynamicEntries`
output-size bound, shipped as the *relative* form
`patchDynamicEntries_stripRpath_size_le` on a **compositional
`patchDynamicEntries` refactor** (pure loop fold + explicit tail appends,
byte-identical, 54/54 tests) — the refactor dissolved the brittle
desugared-`__do_jp` navigation outright, so neither the originally-feared
join-point walk nor `mvcgen` was needed; and (2) the
`toElfFile`-as-single-`updateSectionContent` factoring
(`toElfFile_removeRpath_factor`), via a per-apply commutation suite that
pushes the lone `.dynamic` update out through the outer `applyX` chain.  A
design note worth recording: the *relative* size bound (op output vs. no-op
output on the same `byteDyn`) is the right target — it's what the shrink
lemmas consume and needs no parse-balance preconditions, unlike the absolute
`≤ byteDyn.size` (so the NEEDED-balance worry was moot).

State of §5.1 (later): all four shrinking ops are DERIVED via the generic
`mapDynamicOp f` machinery (`removeRpath`, `modifyRPath.remove`, `removeNeeded`,
`modifySoname.remove`); and the two `mapDynamicOp` GROWERS
(`addDebugTag`/`noDefaultLib`) are now FULLY DERIVED too.  The keystone grow
driver `tierD_roundtrip_of_grown_eo` (`Patchelf/Elf/OpToElfFactorGrow.lean`)
HYPOTHESIZES the normalized form's `spliceRegionsDisjoint` (`hSplice`), but the
new module `Patchelf/Elf/GrowEOFDisjointOfBase.lean` (commit `bfafd42`,
PLAN-GROWING-OPS §3 Commit 3 — the "very-high-risk" item) DERIVES that `hSplice`
from the no-op base: a `mapDynamicOp` grower widens ONE section at its FIXED
offset, so the size-independent invariants transport verbatim and
`headerSectionDisjoint`/`phdrSectionDisjoint` survive via the LEFT disjunct given
2 honest offset side conditions (the dynamic section sits after the header / phdr
table, WEAKER than the shrink path's `hSizeBound`).  Establisher
`spliceRegionsDisjoint_of_grown_base` + corollary
`Adapter.mapDynamicOp_spliceRegionsDisjoint_of_base`; the two capstones
`toElfFile_{addDebugTag,noDefaultLib}_tierD_roundtrip_derived` MOVED into that
module and were UPGRADED to derive `hSplice` (no longer hypothesize it) — their
surface is now the no-op base's 6 structural invariants (same as the shrink
capstones) + the 2 offset side conditions.  The generic driver
`tierD_roundtrip_of_grown_eo` STAYS hypothesizing `hSplice` (reused by the dynstr
growers).

State of §5.1 (latest, commit `c9bf8ce`): the dynstr-growing
`growDynstrDynamicOp` growers `addNeeded` / `modifyRPath.set` /
`modifySoname.set` now have Tier-D capstones too
(`Patchelf/Elf/OpToElfFactorGrowDynstr.lean`, PLAN-GROWING-OPS §3 Commit 5).  The
genuinely-new **Strategy-A two-field factoring** is DERIVED: the key insight that
collapses "two fields" to one is `addNeeded typed lib h = { tg with dynamic :=
tg.dynamic.map (·.pushNeeded off) }` by `rfl`, where `tg := (typed.growDynstr
lib).1` ABSORBS the entire dynstr growth + dynsym/dynamic rebases into the base
`toElfFile template tg`, so the only delta is a single `.dynamic` update at
`iDyn` and NO parallel `.strtab`-commutation suite was needed.  Keystone
`toElfFile_dynamicMapMono_factor` generalizes `toElfFile_mapDynamicOp_factor` to
a MONOMORPHIC `g` on `.dynamic` (reusing `innerChain_factor_general` verbatim);
the three capstones
`toElfFile_{addNeeded,modifyRPath_set,modifySoname_set}_tierD_roundtrip_derived`
instantiate `tierD_roundtrip_of_grown_eo`, so — UNLIKE the `mapDynamicOp`
growers, whose `hSplice` is derived — they still HYPOTHESIZE `hSplice`
(first-cut caliber).  113 lake jobs (was 112), 54/54 tests, no `sorryAx`.  Every
growing op named in PLAN-GROWING-OPS now has a Tier-D capstone.

Open §5.1 (the ONLY remaining growing-ops item; deferred — see
`PLAN-GROWING-OPS.md`): DERIVE `hSplice` for the dynstr growers — a
TWO-grown-section analogue of `Adapter.mapDynamicOp_spliceRegionsDisjoint_of_base`
(the `.dynstr` section grows too, in addition to `.dynamic`).  The building block
`toElfFile_addNeeded_content_at_dynamicIdx` (content-at-`iDyn` corollary) is
landed in `OpToElfFactorGrowDynstr.lean`, but the two-grown-section establisher is
NOT done.
