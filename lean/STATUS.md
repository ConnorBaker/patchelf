# patchelf (Lean 4 port) — status and known gaps

> **Layout work landed.** The PT_LOAD / DT_* coherence gap
> (formerly the central correctness bug) is closed by `growEOF`
> + `syncDtAddrTagsInFile` + a pre-write validator
> (`Patchelf/Elf/{GrowEOF,Validate}.lean`). `set-rpath` on real
> Linux ET_DYN binaries now produces output that runs.
>
> **§3.5a fully landed.** Fresh-PT_LOAD allocation handles both
> the in-place sub-case (binaries with phdr-table headroom) and
> the relocatePht sub-case (binaries packed tight against the
> first section, e.g. coreutils `ls`).  Empirically verified on
> real `ls` and synthetic BSS-heavy fixtures.  Tests 53–54 cover
> both paths.
>
> **§1.1 parser side landed.** `Parser.parseLoadable` returns
> `LoadableElfFile` carrying `IsLoadable` + `shdrSectionDisjoint`
> + `sectionFileInSomePtLoad`.  Per-clause `ParseError` variants
> classify loader-coherence failures.  CLI's `validate`
> subcommand cross-checks `parseLoadable` against `validateBytes`.
>
> **§1.2 `_preserves_valid` ladder complete.** All seven byte-layer
> `IsValid` preservation theorems shipped:
> `syncDtStrszInFile`, `syncDtAddrTagsInFile`,
> `layoutForEncoding`, `growEOFWithMainBody`,
> `growEOFWithFreshPtLoad`, `growEOFWithFreshPtLoadReloc`, and
> the user-facing top-level `growEOFWith_preserves_valid`.  Built
> on a new `PlaceFold.placeFold_value_witness` abstraction in
> `LayoutEngine.lean`.
>
> **§1.2 `_preserves_loadable` ladder complete — through the full
> pipeline.** All four `growEOFWith` branches plus the top-level
> dispatch shipped: `layoutForEncoding_preserves_loadable`
> (no-PT_LOAD branch), `growEOFWithMainBody_preserves_loadable`,
> `growEOFWithFreshPtLoad_preserves_loadable`,
> `growEOFWithFreshPtLoadReloc_preserves_loadable`, and the
> top-level `growEOFWith_preserves_loadable`.  Built on new per-phdr
> facts about `updatePhdrsAfterMove` (PT_LOAD / PT_INTERP /
> PT_DYNAMIC, threading the `i = lastIdx` filesz/memsz update) plus
> a `retargetPtPhdr_*` family for the relocate branch.  Lifted to
> the **full pre-encode pipeline, end-to-end**: both passes preserve
> loadability — `syncDtStrszInFile_preserves_loadable` (the DT_STRSZ
> resync, first pass) and `syncDtAddrTagsInFile_preserves_loadable`
> (the DT_* address rewrite, inside `prepLayoutForEncode`) — composing
> via `prepLayoutForEncodeWith_preserves_loadable` into the capstone
> `prepLayout_syncDtStrsz_preserves_loadable` (`Encoder.lean`).  By
> `encode_eq` that IS the IR `encodeBody` serializes, so the encoder's
> entire pre-write transform provably takes a loadable input to a
> loadable output (`IsValid + sectionsNonOverlapping +
> ptInterpAgreement + ptDynamicAgreement + segmentCongruence`).
>
> **§5.1 op-level Tier D — open core closed; shrinking ops round-trip.**
> The historical `Adapter.toElfFile` dependent-type obstacle is resolved
> (the `applyX` helpers were un-bundled to take typed *fields*, with the
> dependent index `ds` free).  Tier-1 ops (`setOsAbi`, `modifyExecstack`)
> have full `_preserves_loadable`.  The three "open core" obligations on
> the encoder-normalized form `en := prepLayoutForEncode (syncDtStrszInFile
> eo)` are now closed:
> * **A — `syncOk`** (`syncOk_of_normalized`): `syncDtStrszInFile`
>   establishes `dynStrszCoherent` by construction (DT_STRSZ ← `dynstr`
>   byte length, needs `< 2^64`), and the layout pre-pass preserves it
>   (`growEOFWith_dynamic`/`_dynstr` + `syncDtAddrTagsInFile` is identity
>   on DT_STRSZ — not an address tag).
> * **B — `hIdem`** (`encode_eq_encode_normalized`): re-normalizing `en`
>   is a no-op (`syncOk` + layout idempotence from `en.spliceRegionsDisjoint`),
>   so `encode eo = encode en` via `encode_eq` twice.
> * **C — residual `EncodePreconditions`** (`encodePreconditions_of_layoutNormalized`):
>   `syncOk` (A) + `spliceDisjoint` (§1.3a scaffold) +
>   `identValid`/`sizeFit`/`nullEmpty`/`headerFit_entry` all DERIVED — the
>   last four via the pipeline's per-section `content`/`shdrSize`/`type` +
>   `header.ident`/`entry` preservation (the `growEOFWith` content-map
>   getElem-dispatch wall is cracked: state preservation as a bound-free
>   `map (·.content)` equation, `cases pageSize?` to kill the `match
>   pageSize?` entanglement, then `simp only []; repeat' split`).  Only the
>   4 position-bound families (`headerFit_phoff`/`shoff`, `phdrFit`,
>   `shdrFit`) remain hypotheses — genuinely non-derivable for an encoder
>   output (unbounded `roundUp` offsets), the sanctioned "file < 2^64"
>   intervention.
>
> Composed driver `tierD_roundtrip` / `tierD_roundtrip_of_valid` /
> `tierD_roundtrip_of_eo_facts` glues A+B+C + the §1.2 validity capstone
> (`prepLayout_syncDtStrsz_preserves_valid`) into
> `parse (encode eo) = .ok ⟨en, _⟩`.
>
> **§5.1 structural invariants now DERIVED for all four shrinking ops, via
> generic `mapDynamicOp f` machinery.**  Module `Patchelf/Elf/OpToElfFactor.lean`
> discharges the 6 structural disjointness invariants + section-0-NULL on the op
> output *without* hypothesizing them: it factors `toElfFile template
> (mapDynamicOp typed f)` as a single `(toElfFile template typed).updateSectionContent
> iDyn (.dynamic newDyn)` on the NO-OP adapter output (`toElfFile_mapDynamicOp_factor`
> — pushing the lone `.dynamic` update out through the shared
> `applyVersym…applyInterp` chain + the header/phdrs override, all five outer
> applies commuting since they target sections ≠ the dynamic index), shows the
> no-op's dynamic content is `patchDynamicEntries (template bytes) typed.dynamic`
> (`toElfFile_content_at_dynamicIdx`, a `calc`/`.trans` chain — `rw` on the giant
> `applyX` term whnf-times-out even at 1M heartbeats), and transports the
> invariants via `SectionOps.updateSectionContent_*Disjoint_shrink` using a
> per-`f` *relative* size bound `(patch byteDyn (f d)).size ≤ (patch byteDyn d).size`
> (`mapDynamicOp_structural_transport`, taking that bound as `hSizeBound`).  The
> generic capstone `toElfFile_mapDynamicOp_tierD_roundtrip_derived`:
> `parse (encode (toElfFile template (mapDynamicOp typed f))) = .ok …` with NO
> structural-invariant hypotheses on the op output — only the *no-op output's*
> structural invariants (template-/parser-derivable, the precondition any op
> needs) plus the sanctioned eo-level remainder (`IsValid`, phnum bound, dynstr
> witness + `< 2^64` fit, the four derived-field facts, the four `< 2^64`
> position bounds).
>
> **All four shrinking ops instantiate it** (each `mapDynamicOp e f`
> definitionally, so the capstone closes by `exact`):
> * `toElfFile_removeRpath_tierD_roundtrip_derived` (`f := ·.stripRpath`) — the
>   §5.1 regression gate; statement + axioms unchanged across the genericization.
> * `toElfFile_modifyRPath_remove_tierD_roundtrip_derived` (same `f`, reusing
>   `patchDynamicEntries_stripRpath_size_le`) — free second op.
> * `toElfFile_removeNeeded_tierD_roundtrip_derived` (`f := ·.filterNeededBy
>   lib.toUTF8`) — needs the only genuinely new proof: the size bound
>   `patchDynamicEntries_filterNeededBy_size_le` (Adapter.lean), via a
>   POTENTIAL-function lockstep relation `NeededRel` = `result.size +
>   (needed.size − cursor)` (the op/no-op NEEDED cursors run UNEQUAL, unlike
>   `stripRpath`'s cursor-equal `ShrinkRel`) + `appendSurplusNeeded_size_exact`
>   + the `tail_filterNeeded` composition.
> * `toElfFile_modifySoname_remove_tierD_roundtrip_derived` (`f := ·.removeSoname`,
>   bound `patchDynamicEntries_removeSoname_size_le` — a `ShrinkRel`-shaped variant
>   tracking the four non-soname applied-flags, soname being the diverging tail).
>
> The earlier `toElfFile_{removeRpath,removeNeeded}_tierD_roundtrip` (in
> `OpAdapterPreservation.lean`) still ship taking their `eo` facts directly as
> hypotheses.
>
> **§5.1 growing ops — the `mapDynamicOp` growers are now FULLY DERIVED
> (`hSplice` no longer hypothesized).**  Module `Patchelf/Elf/OpToElfFactorGrow.lean`
> ships the keystone grow driver; the new module
> `Patchelf/Elf/GrowEOFDisjointOfBase.lean` PROMOTES the growing-ops `hSplice`
> from a HYPOTHESIS to a DERIVED fact for the two `mapDynamicOp` growers
> (`addDebugTag`/`noDefaultLib`) — PLAN-GROWING-OPS §3 Commit 3, the
> "very-high-risk" item, LANDED.  A growing op widens one section's `encodedSize`
> at its ORIGINAL offset, so the three per-section disjointness invariants on `eo`
> genuinely BREAK and the shrink-monotonicity core (which needs `newDyn.size ≤
> oldDyn.size`) cannot apply; `encode`'s `prepLayoutForEncode`/`growEOFWith`
> RE-LAYS-OUT the file (flags the overlapping grown sections stale, relocates
> them), so the NORMALIZED form is `spliceRegionsDisjoint` even though `eo` is
> not.  The keystone driver `tierD_roundtrip_of_grown_eo` is identical to
> `tierD_roundtrip_of_eo_facts` EXCEPT it HYPOTHESIZES the normalized form's
> `spliceRegionsDisjoint` (`hSplice`); every other `EncodePreconditions` field is
> DERIVED from `eo` via the `*_normalized_of_eo` helpers + `tierD_roundtrip_of_valid`.
>
> **The new derivation.**  A `mapDynamicOp` grower widens ONE section (the
> dynamic section) at its FIXED offset (`updateSectionContent` preserves
> `.offset`).  Of the 6 structural invariants
> `prepLayoutForEncode_produces_spliceRegionsDisjoint` consumes: section-0-NULL +
> the 3 header/table clauses are size-INDEPENDENT (transport verbatim);
> `headerSectionDisjoint`/`phdrSectionDisjoint` survive growth via the LEFT
> disjunct (a section AFTER a region stays disjoint when it grows at a fixed
> offset) — needing only that the dynamic section sits at/after the ELF header
> and at/after the phdr table (two honest offset side conditions, true for every
> real ELF, WEAKER than the shrink path's `hSizeBound`); `shdrSectionDisjoint` +
> `sectionsNonOverlapping` genuinely break, but `growEOFWith` RE-ESTABLISHES
> exactly those, so they are NOT preconditions.  `GrowEOFDisjointOfBase.lean`
> ships the establisher `spliceRegionsDisjoint_of_grown_base` (`namespace
> Patchelf.Elf`) + the `mapDynamicOp`-level corollary
> `Adapter.mapDynamicOp_spliceRegionsDisjoint_of_base` (mirror of
> `mapDynamicOp_structural_transport`, reusing the `RemoveRpathFactorData`
> bundle) + supporting lemmas (`IntervalDisjoint_grow_right_of_le`,
> `ElfFile.updateSectionContent_sectionInterval_grow` — the grow analogue of
> `_sectionInterval_shrink` — and `_headerSectionDisjoint_grow` /
> `_phdrSectionDisjoint_grow`).  Both establisher and corollary are pure
> `[propext, Classical.choice, Quot.sound]` (no bv_decide).
>
> **The two capstones `toElfFile_{addDebugTag,noDefaultLib}_tierD_roundtrip_derived`
> MOVED into `GrowEOFDisjointOfBase.lean` and were UPGRADED:** they NO LONGER
> hypothesize `hSplice` — they DERIVE it via the corollary, so their surface is
> now the no-op base's 6 structural invariants (the same surface the SHRINK
> capstones use) + the 2 offset side conditions.  Axioms: standard `[propext,
> Classical.choice, Quot.sound]` + 3 bv_decide, no `sorryAx`.  The generic driver
> `tierD_roundtrip_of_grown_eo` STAYS in `OpToElfFactorGrow.lean` and KEEPS its
> hypothesized `hSplice` (still needed by `addNeeded`, which can't yet derive it).
>
> **§5.1 growing ops — the dynstr growers now have a Tier-D capstone too
> (hSplice HYPOTHESIZED; the two-field factoring DERIVED).**  Module
> `Patchelf/Elf/OpToElfFactorGrowDynstr.lean` ships Tier-D round-trips for the
> `growDynstrDynamicOp` growers `addNeeded` / `modifyRPath .set` /
> `modifySoname .set` (dynstr AND dynamic both grow) — PLAN-GROWING-OPS §3
> Commit 5, LANDED.  The genuinely-new artifact is the **Strategy-A two-field
> factoring**: the key insight collapses the "two fields" to one —
> `addNeeded typed lib h = { tg with dynamic := tg.dynamic.map (·.pushNeeded
> off) }` by `rfl`, where `tg := (typed.growDynstr lib).1` is the base with
> dynstr grown + dynsym/dynamic rebased, so the ENTIRE dynstr growth is ABSORBED
> into the base `toElfFile template tg` and the only delta is a single
> `.dynamic` update at `iDyn` — NO parallel `.strtab`-commutation suite was
> needed.  The keystone `toElfFile_dynamicMapMono_factor` generalizes
> `toElfFile_mapDynamicOp_factor` to a MONOMORPHIC `g` on `.dynamic` (the
> grow-dynstr mutator is `ds`-monomorphic, tied to `off : Fin tg.dynstr.size`;
> the factoring only touches `.dynamic` as `Option.map`, so it reuses
> `innerChain_factor_general` verbatim).  Per-op factorings
> `toElfFile_{addNeeded,modifyRPath_set,modifySoname_set}_factor` + the
> content-at-`iDyn` corollary `toElfFile_addNeeded_content_at_dynamicIdx`
> (building block for a future hSplice derivation) are `[propext, Quot.sound]`.
> The three capstones
> `toElfFile_{addNeeded,modifyRPath_set,modifySoname_set}_tierD_roundtrip_derived`
> instantiate `tierD_roundtrip_of_grown_eo` and so HYPOTHESIZE the normalized
> form's `spliceRegionsDisjoint` (`hSplice`, first-cut caliber) — `[propext,
> Classical.choice, Quot.sound]` + 3 bv_decide, no `sorryAx`.
>
> **So every growing op named in PLAN-GROWING-OPS now has a Tier-D round-trip
> capstone.**  The `mapDynamicOp` growers (`addDebugTag`/`noDefaultLib`) are
> FULLY DERIVED — `hSplice` derived from the no-op base, carrying only the 2
> honest offset side conditions.  The `growDynstrDynamicOp` growers (`addNeeded`,
> `modifyRPath.set`, `modifySoname.set`) have capstones LANDED but still
> HYPOTHESIZE `hSplice` (the two-field factoring is fully derived).  **The ONLY
> remaining §5.1 growing-ops item:** DERIVE `hSplice` for the dynstr growers —
> this needs a TWO-grown-section analogue of
> `mapDynamicOp_spliceRegionsDisjoint_of_base` (the `.dynstr` section grows too);
> `toElfFile_addNeeded_content_at_dynamicIdx` is the building block, but the
> establisher is NOT done.  See ROADMAP §5.1.  The reusable shrink-monotonicity
> core (`SectionOps.updateSectionContent_*Disjoint_shrink`) + the
> `Adapter.{foldl_proj_size_le_add,idForIn_proj_size_le}` loop-size bridges are
> landed.  **Fresh-agent handoff covering ALL remaining work**
> (§5.1 + §3.5b + §4.2; §5.2 now closed):
> [`../research/PICKUP-PROMPT-OP-TIER-D.md`](../research/PICKUP-PROMPT-OP-TIER-D.md).
> The growing-ops half of §5.1 has a dedicated design plan,
> [`../research/PLAN-GROWING-OPS.md`](../research/PLAN-GROWING-OPS.md).
>
> **Tests: 54/54 shell tests passing; 113/113 Lean build jobs;
> zero `sorry`s.**

This document records the **current state** of the Lean 4 patchelf
port — what works, what doesn't, what's verified, what isn't.

For the **architectural model** (three-layer stack, validity ladder,
pipeline, op convention, verification surface), see
[`ARCHITECTURE.md`](ARCHITECTURE.md).

For **forward-looking work items**, see [`research/ROADMAP.md`](../research/ROADMAP.md).

For a **complete inventory** of every theorem/definition by file, see
[`INVENTORY.md`](INVENTORY.md).

---

## What works end-to-end

The CLI is built on `lean4-cli` and is **subcommand-shaped** (e.g.
`patchelf set-rpath /a foo`), a deliberate divergence from C++
patchelf's argv-order flag stack. See `Patchelf/CLI.lean` for the
top-level command tree.

All 14 mutating ops plus 6 print ops work against real ELF fixtures:

| Subcommand | Status | Notes |
|---|---|---|
| `set-os-abi <abi> <file>` | works | numeric or canonical name |
| `print-os-abi <file>` | works | |
| `set-execstack` / `clear-execstack <file>` | works | no-op when no PT_GNU_STACK |
| `print-execstack <file>` | works | prints `execstack: X/-/?` |
| `remove-rpath <file>` | works | filter-shaped dyn mutation |
| `remove-needed <lib> <file>` | works | |
| `remove-soname <file>` | works | |
| `print-rpath` / `print-needed` / `print-soname` / `print-interpreter <file>` | works | `print-soname` emits nothing when DT_SONAME absent |
| `set-rpath [-f] <path> <file>` | works | retag existing or insert new |
| `add-rpath [-f] <path> <file>` | works | composes with existing rpath |
| `shrink-rpath [-f] [--allowed-prefixes p:...] <file>` | works | FS-existence filter by default; prefix filter with flag |
| `add-needed <lib> <file>` | works | inserts at FRONT of `.dynamic` (matches C++) |
| `replace-needed <old> <new> <file>` | works | reuse-offset fast path + grow path |
| `set-soname <soname> <file>` | works | |
| `set-interpreter <path> <file>` | works | single unified op (no in-slot/grow split) |
| `add-debug-tag <file>` | works | |
| `no-default-lib <file>` | works | |
| `rename-dynamic-symbol <old> <new> <file>` | works | rejects binaries with `.gnu.hash` |
| `rename-dynamic-symbols <map-file> <file>` | works | |
| `clear-symbol-version <sym> <file>` | works | retargets matching versym entries to VER_NDX_GLOBAL |
| `validate <file>` | works | runs the pre-write validator on a file as-is |
| `roundtrip <file>` | works | parse + re-encode (no semantic mutation; useful for codec testing) |
| `parse <file>` | works | brief structural summary on stdout |

`-f` is `--force-rpath` (emit DT_RPATH instead of DT_RUNPATH);
declared per-subcommand on the rpath ops.

**Per-subcommand flags on every mutating op** (injected by
`mutatingFlagsExt` in CLI.lean; read-only subcommands reject these):

- `--output PATH` / `-o` — write target override (default: in-place).
- `--no-validate` — skip the loader-coherence validator (UNSAFE; see
  `Validate.lean`).
- `--page-size N` — override the layout engine's PT_LOAD alignment
  (e.g. `0x10000` for AArch64). Threaded through `encodeWith` →
  `growEOFWith`.
- `--debug` — emit `  -> ...`-prefixed trace lines on stderr via
  `Patchelf.Log` (fully wired through `runWith` and
  `writeWithValidation`).

Global: `--help` / `--version` / `help <cmd>`; `@file` argument
resolution in `Main.resolveArg`.

Multi-op invocations: chain CLI calls via the shell
(`patchelf set-rpath /a foo && patchelf add-needed libbar.so foo`).
The single-process multi-op CLI was retired with the lean4-cli
migration.

**Test status:** all 54 shell tests in `tests/cases/` pass.

`/tmp/lean-pe-fixtures/hello` and `/tmp/lean-pe-fixtures/greeter`
(real glibc-linked binaries) are used by integration tests 50–52
(`replace-needed --vn-file`, `rename-dynamic-symbol` on `.gnu.hash`,
`rename-dynamic-symbol` with bucket-changing relocs).  When absent,
those tests skip gracefully (exit 77).

---

## Codebase size

For the file-by-file architecture, see
[`ARCHITECTURE.md` § File map](ARCHITECTURE.md#file-map). For the
exhaustive declaration inventory, see
[`INVENTORY.md`](INVENTORY.md).

Total Lean source: ~22,460 LOC. Distribution by category:

| Category | LOC | What it is |
|---|---|---|
| Verification (`ByteRoundtrip` + `ByteLevel` + `LayoutEngine` + `Basic` + `AdapterRoundtrip`) | ~6,090 | Tier D `parse_encode_roundtrip` infrastructure + unified `PlaceFold` scaffolding |
| DSL + op-layer infra (`SchemaDSL` + `Schemas` + `Adapter` + `ObservableCombinators`) | ~2,340 | `elf_schema` elaborator + 7 invocations + bridge |
| Wire codec + types (Splice, Layout, Decode, Parser, ParseHeader, Reader, Writer, Serialize, DynamicParse/Encode) | ~1,670 | Reader/Writer + Splice + parsing primitives + per-clause ParseError |
| Typed-section types (DynamicSection, StringSection, SymbolSection, ValidElfFile, InterpSection, AuxSections) | ~630 | Typed algebra + StringSection lookup roundtrip |
| Layout pipeline + validator (`Encoder` + `GrowEOF` + `Validate`) | ~3,740 | growEOF + syncDtAddrTagsInFile + pre-write validator + `prepLayoutForEncodeWith_produces_spliceRegionsDisjoint` chain + the end-to-end `_preserves_loadable` ladder |
| `SectionOps` | ~420 | `updateSectionContent` + projection / index-preservation / typed-accessor preservation helpers |
| 14 ops (`Elf/Ops/*.lean`) | ~1,080 | mutating operations |
| Op-level Tier D (`OpAdapterPreservation`) | ~440 | Tier-1 op `_preserves_loadable` + phdrs-map helpers + the Tier-2/3 round-trip scaffold, Obligation-C package, `tierD_roundtrip` drivers, and the two shrinking-op round-trips (§5.1) |
| Op→`toElfFile` factoring (`OpToElfFactor`) | ~1000 | Generic `mapDynamicOp f` structural-invariant derivation: `updateSectionContent` algebra + the 3 `applyTypeOpt_*` generic outer-apply lemmas (4× collapse) + `toElfFile_mapDynamicOp_factor` + `mapDynamicOp_structural_transport` + the generic capstone `_mapDynamicOp_tierD_roundtrip_derived`, instantiated for all 4 shrinking ops: `removeRpath` / `modifyRPath.remove` / `removeNeeded` / `modifySoname.remove` (§5.1) |
| Op→`toElfFile` GROWING-op Tier-D (`OpToElfFactorGrow`) | ~110 | The grow driver `tierD_roundtrip_of_grown_eo` (hypothesizes the normalized form's `spliceRegionsDisjoint`, derives every other `EncodePreconditions` field from `eo`) — still needed by the dynstr growers (§5.1) |
| Growing-op `hSplice` derivation (`GrowEOFDisjointOfBase`) | ~300 | DERIVES the `mapDynamicOp` growers' `hSplice` from the no-op base: `spliceRegionsDisjoint_of_grown_base` + `Adapter.mapDynamicOp_spliceRegionsDisjoint_of_base` + the grow-interval lemmas, plus the two upgraded (no-longer-`hSplice`-hypothesizing) capstones `toElfFile_{addDebugTag,noDefaultLib}_tierD_roundtrip_derived` (§5.1) |
| Op→`toElfFile` dynstr-GROWER Tier-D (`OpToElfFactorGrowDynstr`) | ~360 | Two-field (dynstr + dynamic) factoring + Tier-D round-trip for the `growDynstrDynamicOp` growers `addNeeded` / `modifyRPath.set` / `modifySoname.set`: the keystone `toElfFile_dynamicMapMono_factor` (monomorphic-`g` generalization of `toElfFile_mapDynamicOp_factor`; the dynstr growth is absorbed into the base, collapsing two fields to one `.dynamic` update) + the per-op factorings + `toElfFile_addNeeded_content_at_dynamicIdx` + the three capstones `toElfFile_{addNeeded,modifyRPath_set,modifySoname_set}_tierD_roundtrip_derived` (hSplice HYPOTHESIZED, the factoring DERIVED) (§5.1) |
| CLI + Main + Log | ~990 | lean4-cli subcommand tree + stderr trace logger |
| Tactic (`SpliceSimproc*`) | ~200 | `simp_splice` macro + `[splice_simp]` simp set |
| Misc (root, ElfFile, DynamicLemmas) | ~980 | structural |

`ByteRoundtrip.lean` (~3,000 LOC), `SchemaDSL.lean` (~1,200 LOC), and
`LayoutEngine.lean` (~1,000 LOC after the `PlaceFold` unification) are
the largest files.  Every file builds; zero `sorry`.

---

## Invariants and theorems

### Byte-layer `IsValid` (8 clauses, decidable)

`header_counts`, `sections_wf`, `strtabs_wf`, `dynamic_wf`,
`dynsym_wf`, `content_wf`, `types_distinct`, `names_unique`.  See
`ElfFile.lean` for clause definitions.  Typed-algebra ops don't
carry `_preserves_valid` theorems — `ValidElfFile` is typed, not
predicate-bundled, so the type itself IS the invariant.

### `IsLoadable` and `IsFullyValid`

`IsLoadable` adds non-overlapping sections + PT_INTERP/PT_DYNAMIC
phdr offset agreement + PT_LOAD alignment congruence.
`IsFullyValid` further adds `dynamicAddressCoherent` — a single
record covering DT_STRTAB / DT_SYMTAB / DT_HASH / DT_GNU_HASH /
DT_VERNEED address-coherence plus DT_STRSZ size-coherence (the
latter is the `strsz_size` field of `dynamicAddressCoherent`,
not a separate clause).

`IsLoadable` is consumed by `Validate.IsLoadableBytes` at the CLI
write boundary AND by `Parser.parseLoadable`, which returns a
typed `LoadableElfFile` carrying the four `IsLoadable` clauses
plus `shdrSectionDisjoint` and `sectionFileInSomePtLoad`.  Existing
`Parser.parse` is unchanged and still returns the weaker
`ParsedElf`; the CLI's `validate` subcommand cross-checks both
paths.  The layout pass's `_preserves_loadable` ladder is complete
(`growEOFWith_preserves_loadable`); per-op `_preserves_loadable`
theorems remain open (see ROADMAP §1.2 / §5.1).

### Tier D: `parse_encode_roundtrip` — UNCONDITIONAL

`Patchelf.Elf.parse_encode_roundtrip (e : ParsedElf)
(hPre : EncodePreconditions e.elf) : parse (encode e.elf) = .ok e`.

This is a **codec-asymmetry guard for encoder/parser refactors**, not
a "byte-level correctness" theorem in any user-facing sense.  It rules
out the silent bug class where the encoder writes pattern A and the
parser reads pattern B with A ≠ B such that the round-trip cancels in
shell tests.  It does NOT catch wire-format / spec disagreement
(`e_machine` set to a value the kernel rejects but Lean's parser
accepts) or any post-write loader-coherence violation — those live
in `Validate.IsLoadableBytes`, run at write time.

The byte-level codec is verified end-to-end under the
`EncodePreconditions` bundle (10 explicit, decidable preconditions —
8 conceptual clauses plus the 3 `headerFit_*` fields).  All
decoder-inverse facts are proved:

- `parseHeader_encode` — header parser succeeds and recovers `e.header`.
- `phdrs_decode_encode` — `decodePhdrs` recovers `e.phdrs`.
- `shdrs_decode_encode` — `decodeShdrs` recovers `e.sections.map toShdr`.
- `section_decode_encode` — for every section, `decodeSectionContent`
  on `(toShdr s)` recovers `s.content`.

`EncodePreconditions e` packages 10 fields:
- `syncOk` — `syncDtStrszInFile e = e` (DT_STRSZ already in sync).
- `spliceDisjoint` — all 4 splice region kinds are pairwise disjoint.
  Subsumes `layoutAlreadyValid e = true` via
  `layoutAlreadyValid_of_spliceRegionsDisjoint`; the derived
  `EncodePreconditions.layoutOk` view exposes the bool form.
- `identValid` — ELF magic + class + data ident bytes are spec-valid.
- `sizeFit` — each `s.shdrSize < UInt64.size`.  For non-NOBITS
  sections this is `encodedSize`; for NOBITS it's the declared
  `memSize` carried on `SectionContent.nobits` (so the shdr table
  preserves the BSS allocation size after a parse/encode roundtrip).
- `nullEmpty` — SHT_NULL sections have `.raw ByteArray.empty` content.
- `headerFit_{entry,phoff,shoff}` — each ElfHeader wrap_nat field's
  `.val` fits in UInt64 (parser-derivable: came from `(readU64 ...).toNat`).
- `phdrFit` — every ProgramHeader wrap_nat field fits in UInt64.
- `shdrFit` — every Section's wrap_nat fields fit in UInt64.

The previously-required `typesMatch` field is gone after the
SectionContent IR migration: `Section.type` is now derived from
`content.type`, and `SectionContent.raw` carries a structural proof
that its `sh_type` is non-structural — so the type↔content invariant
holds by construction with no external predicate.

**Parser-output → EncodePreconditions bridge.**
`encodePreconditions_of_parser bs shdrs e` derives 9 of 10 fields
(everything except `spliceDisjoint`) from parser-output structural
facts plus `e.phdrs = decodePhdrs ...` and `shdrs = decodeShdrs ...`.
Callers supply `spliceDisjoint` directly — the parser doesn't
enforce pairwise region disjointness (and shouldn't; overlapping
sections are spec-valid).  See ROADMAP item 1.3a for the per-clause
helper inventory.

**Encoder-output `spliceDisjoint`** is discharged by
`Encoder.prepLayoutForEncodeWith_produces_spliceRegionsDisjoint`:
given the 5 structural input invariants (`headerPhdrDisjoint` /
`headerShdrDisjoint` / `phdrShdrDisjoint` / `headerSectionDisjoint` /
`phdrSectionDisjoint`) plus `hSection0Null`, the encoder's full
layout pre-pass outputs `spliceRegionsDisjoint`.  Composes:

* `GrowEOF.growEOFWith_produces_spliceRegionsDisjoint` — discharges
  all 3 branches (fast path / fallback / main path) via the unified
  `LayoutEngine.PlaceFold.{placeStep, placeFold, Placement,
  PairDisjoint, FoldInv}` scaffolding.  `layoutForEncoding` and
  `growEOFWith`'s `appendStaleSections` are specializations of the
  same fold parameterized over `verbatim`, `transform`, `baseOffset`.
* `GrowEOF.syncDtAddrTagsInFile_preserves_spliceRegionsDisjoint` —
  the second pre-encode pass preserves the predicate (it only
  rewrites `.dynamic` content via `Array.map`, preserving array
  `.size` hence `encodedSize`).

This is the primitive for op-level Tier D (ROADMAP §5.1) but is not
sufficient on its own — see ROADMAP §5.1 for the dependent-type
obstacle that surfaces when threading typed-side ops through
`Adapter.toElfFile`.

**Per-content forward roundtrips**: 5 of 6 `SectionContent` cases
(`raw`, `strtab`, `versym`, `dynsym`, `dynamic`) have explicit
`decodeX_encode_X` lemmas in `ByteRoundtrip.lean`; `nobits` writes
no bytes so the dispatch is trivial.  The `.dynamic` case uses
loop-induction via `decodeDynamic_writeArray_eq` + a strengthened
`dynamicTerminated` invariant (DT_NULL bookend + no early null)
split out from `dynamicWellFormed`.

**Per-struct forward roundtrips**: all 7 fixed-layout structs
(`ElfIdent`, `ElfHeader`, `ProgramHeader`, `SectionHeader`,
`DynEntry`, `Symbol`, `Vernaux`) have `_decode_write` lemmas
DSL-emitted from `elf_schema` declarations.  Window-form decoder
bridges (`decoder_eq_slice`) for `decodeHeader`, `decodePhdr`,
`decodeShdr`, `decodeSym`, `decodeDynEntry` decouple per-byte
preservation from buffer shape.

`Encoder.encodeBody` and `Encoder.encode` are `@[irreducible]` (with
`_eq` unfolding lemmas); removing the attribute makes per-byte access
proofs time out at >32M heartbeats.

`.verneed` / `.hash` / `.gnu.hash` flow through
`section_decode_encode` as `.raw bs` (demoted at the byte layer).
The typed-section algebra constructs them via `Adapter.ofElfFile`'s
on-demand decode.  Forward `Verneed.write_decode` for the typed-side
roundtrip is pending; ROADMAP item 4.2.

Axiom dependencies: `[propext, Classical.choice, Quot.sound]` plus 4
`bv_decide` axioms for the readU/writeU primitives. No `sorryAx`.

### Typed-algebra invariants and observables

For the structural picture (why `ValidElfFile` makes byte-layer
`IsValid` clauses vacuous, why DT_* coherence tags disappear, the
`<op> + _observable + _*_preserved` convention), see
[`ARCHITECTURE.md` § Layer 3](ARCHITECTURE.md#layer-3--typed-section-algebra)
and [§ Op convention](ARCHITECTURE.md#op-convention).

**Proved status:** every op in `Elf/Ops/` has at least one
`_observable` theorem stating its post-condition. The
`growDynstrDynamicOp_observable` and `mapDynamicOp_observable`
combinators in `ObservableCombinators.lean` supply the shared
skeleton; each op proves its op-specific `P` predicate inline.

### Adapter round-trip

`Elf/AdapterRoundtrip.lean` carries 8 preservation theorems:
`toElfFile_{header,phdrs}`, `ofElfFile_{header,phdrs,dynstr,versym}`,
and composed `roundtrip_{header,phdrs}`.  Imported by `Patchelf.lean`
so the theorems ship in the default build target.

---

## Encoder pipeline

For the diagram, see
[`ARCHITECTURE.md § Encoder pipeline (zoom-in)`](ARCHITECTURE.md#encoder-pipeline-zoom-in).
`Encoder.encode` and `Encoder.encodeWith pageSize?` (`Encoder.lean`)
implement:

1. **`syncDtStrszInFile`** — rewrite every DT_STRSZ entry's `value` to
   `.dynstr.bytes.size`. No-op if either `.dynamic` or `.dynstr` is
   absent.
2. **`prepLayoutForEncodeWith pageSize?`** — identity when
   `layoutAlreadyValid e = true` (preserves byte-for-byte stability on
   no-growth ops). Otherwise composes:
   1. **`growEOFWith pageSize?`** (`GrowEOF.lean`) — append-at-end
      strategy: identify "stale" sections (those whose `[offset,
      offset + encodedSize)` overlaps another section or the shdr
      table), append each to a new region rounded up from the last
      PT_LOAD's `(p_offset + p_memsz, p_vaddr + p_memsz)` to
      `max(pageSize?, maxPtLoadAlign)`. Each moved section gets
      matching `(offset, addr)` deltas so `p_offset ≡ p_vaddr
      (mod p_align)` survives. The last PT_LOAD's `filesz`/`memsz` are
      extended to cover the appended region; PT_INTERP/PT_DYNAMIC and
      `header.shoff` get retargeted at the moved sections.
      `pageSize?` defaults to auto-detection from existing PT_LOAD
      `p_align` values; passing `0x10000` is the AArch64 path.
      Falls back to `layoutForEncoding` (which doesn't preserve
      PT_LOAD coverage) when `canExtendLastPtLoad` rejects — typically
      because the last PT_LOAD has a large BSS that the appended
      region would clobber. The validator (step 3 below) rejects the
      resulting bytes at write time.
   2. **`syncDtAddrTagsInFile`** — rewrite `.dynamic`'s
      DT_STRTAB / DT_SYMTAB / DT_HASH / DT_GNU_HASH / DT_VERNEED /
      DT_VERSYM / DT_JMPREL / DT_REL / DT_RELA tags to point at the
      moved sections' new addresses (analog of C++ patchelf's
      DT_* update block). DT_JMPREL/REL/RELA look up by section
      name (`.rela.plt`, `.rel.dyn`, `.rela.dyn`).
3. **`encodeBody`** — allocate `zeroBytes (encodedFileSize e)`,
   splice header at 0, phdr table at `phoff`, shdr table at `shoff`,
   then each non-NOBITS non-NULL section at its offset.
4. **Pre-write validator (`Validate.lean`)** — at the CLI's I/O
   boundary, the post-encode bytes are re-parsed and checked against
   `IsLoadableBytes` (decidable: `IsValid + sectionsNonOverlapping +
   shdrSectionDisjoint + ptInterpAgreement + ptDynamicAgreement +
   segmentCongruence + sectionFileInSomePtLoad`). On failure the CLI
   exits 5 with the failing clause on stderr; the file is unchanged
   on disk. `--no-validate` opts out (UNSAFE).

`Encoder.encode` is `@[irreducible]`; use `encode_eq` for
propositional unfolding.

`SectionContent.nobits` carries `(memSize : Nat)` so the shdr table's
`size` field survives the parse/encode roundtrip even though no bytes
are written. `Section.shdrSize` returns `encodedSize` for non-NOBITS
and `memSize` for NOBITS.

---

## Known gaps and divergences

See `research/ROADMAP.md` for the full prioritized list.  Highlights:

### PT_LOAD layout — closed for the common case

The previous `layoutForEncoding` repack stomped on PT_LOAD coverage
when sections moved.  `growEOF` (`GrowEOF.lean`, ~4,228 LOC including
the `_produces_spliceRegionsDisjoint` proof, the
`syncDtAddrTagsInFile_preserves_spliceRegionsDisjoint` lemma, and the
full `_preserves_valid` + `_preserves_loadable` ladders)
replaces it as the primary layout strategy: stale sections are
appended at file end, the last PT_LOAD's `filesz`/`memsz` are
extended to cover them, and `(offset, addr)` deltas are kept equal
so segment congruence survives.  `syncDtAddrTagsInFile` rewrites the
matching DT_* address tags.  `set-rpath` on real ET_DYN binaries
(e.g. `/usr/bin/hello`) now produces output that runs.

**Large-BSS binaries: full coverage.**  When `canExtendLastPtLoad`
rejects (BSS-heavy last PT_LOAD), `growEOFWith` now dispatches to
one of two fresh-PT_LOAD strategies:

* **In-place** (`growEOFWithFreshPtLoad`): when `canAddFreshPtLoad`
  accepts (room for one more 56-byte phdr in the existing slot),
  append a brand-new PT_LOAD covering the moved sections.  Phdr
  table stays put; `header.phnum` bumps by 1.  Proven via
  `growEOFWithFreshPtLoad_produces_spliceRegionsDisjoint`.
* **Relocate-PHT** (`growEOFWithFreshPtLoadReloc`): when there is
  no in-place room (phdr table packed tight against the first
  section, e.g. coreutils `ls` with `.note.gnu.build-id` at
  `0x350` immediately after the phdr table), move the phdr table
  itself to the appended region.  Updates `header.phoff`,
  retargets the PT_PHDR program header, allocates a new PT_LOAD
  covering both the relocated phdrs and the moved sections.
  Proven via `growEOFWithFreshPtLoadReloc_produces_spliceRegionsDisjoint`
  — crucially, this needs no precondition beyond the standard
  structural input invariants, since the relocated phdr region
  sits past `currentFileEnd` by construction.

Tests: `tests/cases/53-cli-set-rpath-bss-heavy.sh` (in-place),
`tests/cases/54-cli-set-rpath-relocate-pht.sh` (real `coreutils ls`).

### Priority 1 gaps (verification depth)

- **Parser establishes `IsLoadable` — landed (typed entry point).**
  `Parser.parseLoadable` returns `LoadableElfFile`, bundling the 4
  `IsLoadable` clauses plus `shdrSectionDisjoint` and
  `sectionFileInSomePtLoad`.  Per-clause `ParseError` variants
  (`sectionsOverlapping`, `ptInterpAgreementFailed`, etc.) classify
  loader-coherence failures.  Op-level `_preserves_loadable`
  theorems remain open; pick up under §5.1.
- **Pre-encode passes — `_preserves_valid` and `_preserves_loadable` both complete.**
  All seven byte-layer `IsValid` preservation theorems shipped:
  `syncDtStrszInFile_preserves_valid`,
  `syncDtAddrTagsInFile_preserves_valid`,
  `syncDtAddrTagsInFile_preserves_spliceRegionsDisjoint`,
  `layoutForEncoding_preserves_valid`,
  `growEOFWithMainBody_preserves_valid`,
  `growEOFWithFreshPtLoad_preserves_valid`,
  `growEOFWithFreshPtLoadReloc_preserves_valid`, and the
  user-facing top-level `growEOFWith_preserves_valid`.

  `_preserves_loadable` ladder also complete:
  `layoutForEncoding_preserves_loadable` (no-PT_LOAD branch),
  `growEOFWithMainBody_preserves_loadable`,
  `growEOFWithFreshPtLoad_preserves_loadable`,
  `growEOFWithFreshPtLoadReloc_preserves_loadable`, and the
  top-level `growEOFWith_preserves_loadable`.  Built on per-phdr
  facts about `updatePhdrsAfterMove`
  (`_pt_load_offset_vaddr_align`, `_pt_interp`, `_pt_dynamic`,
  `_type`) — which handle the `i = lastIdx` filesz/memsz update
  crossed with the PT_INTERP/PT_DYNAMIC type tests by `subst`-ing
  the index witness rather than rewriting it — plus a
  `retargetPtPhdr_*` family + composed `retarget_update_*` facts
  for the relocate branch's extra `retargetPtPhdr` layer.  Fresh
  PT_LOAD congruence: offset/vaddr both `roundUp _ align`, so both
  `≡ 0 (mod align)`.

  Lifted to the full pre-encode pipeline, end-to-end.  Both
  pre-encode passes preserve loadability:
  `syncDtAddrTagsInFile_preserves_loadable` (`GrowEOF.lean`, the
  DT_* address rewrite inside `prepLayoutForEncode`) and
  `syncDtStrszInFile_preserves_loadable` (`Encoder.lean`, the
  first-pass DT_STRSZ resync).  Both only same-size-`map` the
  `.dynamic` section, so they preserve `phdrs` verbatim and
  per-section `(type, offset, encodedSize)` everywhere; the four
  clauses transport directly (the dynstr precondition →
  `iDyn ≠ shstrndx` is the same one `_preserves_valid` needs).
  Composition: `growEOFWith_dynstr` +
  `syncDtAddrTagsInFile_preserves_loadable` →
  `prepLayoutForEncodeWith_preserves_loadable`; then
  `syncDtStrszInFile`'s precondition-lifting lemmas (`_header`,
  `_dynstr`, `_{headerPhdr,headerSection,phdrSection}Disjoint`,
  `_section0Null`) chain it with the first pass into the capstone
  `prepLayout_syncDtStrsz_preserves_loadable` — which, by
  `encode_eq`, is exactly the IR `encodeBody` serializes.
- **`spliceDisjoint` for encoder output — DONE.**
  `Encoder.prepLayoutForEncodeWith_produces_spliceRegionsDisjoint`
  is the composed API the op-level Tier D proofs consume.  See
  §"Tier D" above for the supporting chain.
- **Op-level Tier D — open core CLOSED; all four shrinking ops' structural invariants DERIVED.**
  The `Adapter.toElfFile` dependent-type obstacle is resolved (the
  `applyX` helpers take typed *fields*, dependent index `ds` free).
  `Patchelf/Elf/OpAdapterPreservation.lean` ships
  `toElfFile_{setOsAbi,modifyExecstack}_preserves_loadable` (Tier 1)
  plus `isValid_of_phdrs_map` / `isLoadable_of_phdrs_map`.

  The other 12 ops change byte-level `.dynamic` size, so their raw
  adapter output isn't laid out — `encode`'s `growEOFWith` restores
  it.  Their target is the full Tier D round-trip on the
  encoder-normalized form `en := prepLayoutForEncode (syncDtStrszInFile
  eo)` (what `encodeBody` serializes, per `encode_eq`).  All three
  "open core" obligations on `en` are now closed:
  * **A → `syncOk`** — `syncOk_of_normalized` (`ByteRoundtrip.lean`):
    establishment `syncDtStrszInFile_establishes_dynStrszCoherent`
    (`Encoder.lean`) + preservation `prepLayoutForEncode_preserves_dynStrszCoherent`
    (`growEOFWith_dynamic` + `syncDtAddrTagsInFile_preserves_dynStrszCoherent`,
    GrowEOF.lean).
  * **B → `hIdem`** — `encode_eq_encode_normalized` (`ByteRoundtrip.lean`)
    via `renormalize_eq_self` + `prepLayoutForEncode_{dynstr,eq_self_of_spliceRegionsDisjoint}`
    (`Encoder.lean`).
  * **C → residual `EncodePreconditions`** —
    `encodePreconditions_of_layoutNormalized`
    (`OpAdapterPreservation.lean`): `syncOk` (A) + `spliceDisjoint`
    (§1.3a) + `identValid`/`sizeFit`/`nullEmpty`/`headerFit_entry` all
    DERIVED from the matching facts on `eo`, via per-section
    `content`/`shdrSize`/`type` + `header.{ident,entry}` preservation
    through the whole pre-encode pipeline.  The `growEOFWith`
    content-preservation getElem-dispatch (`growEOFWith_sections_content`,
    GrowEOF.lean) is unblocked via a bound-free `map (·.content)` equation
    (`cases pageSize?` then `simp only []; repeat' split`).  Only the 4
    position-bound families (`headerFit_phoff`/`shoff`, `phdrFit`,
    `shdrFit`) remain hypotheses — `< 2^64` bounds genuinely non-derivable
    for the `roundUp`-laid-out encoder output (the sanctioned "file < 2^64"
    intervention; runtime `Validate.IsLoadableBytes` guards the
    pathological case).

  Composed drivers `tierD_roundtrip` / `tierD_roundtrip_of_valid` /
  `tierD_roundtrip_of_eo_facts` glue A+B+C + the validity capstone
  `prepLayout_syncDtStrsz_preserves_valid` into
  `parse (encode eo) = .ok ⟨en, _⟩`.  The `_of_eo_facts` driver states its
  ENTIRE surface on `eo`: validity, the 6 structural disjointness invariants
  + section-0-NULL (transported through `syncDtStrszInFile` via
  `spliceRegionsDisjoint_of_structural_eo`), the four eo-level derived-field
  facts, and only the 4 residual `< 2^64` position bounds on the normalized
  form.  Shipped worked examples:
  `toElfFile_{removeRpath,removeNeeded}_tierD_roundtrip`.

  Reusable layout core for the per-op structural discharge:
  `SectionOps.updateSectionContent_*Disjoint_shrink` +
  `_section0Null` — a `.dynamic`-shrink (`newDyn.size ≤ oldDyn.size`)
  preserves all 6 disjointness clauses + section-0-NULL (monotone in the
  section's `encodedSize`).

  **All four shrinking ops: structural invariants now DERIVED** via generic
  `mapDynamicOp f` machinery (`Patchelf/Elf/OpToElfFactor.lean`).  The factoring
  `eo = (toElfFile template typed).updateSectionContent iDyn (.dynamic newDyn)`
  is `toElfFile_mapDynamicOp_factor` (generic over `f`), with the no-op output's
  dynamic content identified by `toElfFile_content_at_dynamicIdx`; the transport
  `mapDynamicOp_structural_transport` derives the 6 invariants + section-0-NULL
  on `eo` from the no-op output's, taking the lone per-`f` fact `hSizeBound :
  (patch byteDyn (f d)).size ≤ (patch byteDyn d).size`.  The generic capstone
  `toElfFile_mapDynamicOp_tierD_roundtrip_derived` is instantiated by:
  * `removeRpath` (`f := ·.stripRpath`) — size bound
    `patchDynamicEntries_stripRpath_size_le` (the relative op-vs-no-op form,
    provable with no parse-balance preconditions; proved on a compositional
    `patchDynamicEntries` refactor — pure loop fold `patchStep` + explicit
    tail-append helpers `appendSurplusNeeded`/`appendUnless`, byte-identical to
    the old `Id.run do … while … unless` block, confirmed by 54/54 shell tests).
    The capstone `toElfFile_removeRpath_tierD_roundtrip_derived` keeps its EXACT
    statement + axioms (the §5.1 regression gate); only its body became a
    one-line instantiation.
  * `modifyRPath.remove` (same `f`) — free second op, reuses the stripRpath bound.
  * `removeNeeded` (`f := ·.filterNeededBy lib.toUTF8`) — the only genuinely new
    proof: `patchDynamicEntries_filterNeededBy_size_le`, via a POTENTIAL-function
    lockstep relation `NeededRel` = `result.size + (needed.size − cursor)` (the
    op/no-op NEEDED cursors run UNEQUAL, since the filter consumes loop entries —
    unlike `stripRpath`'s cursor-equal `ShrinkRel`) + the surplus-exact lemma
    `appendSurplusNeeded_size_exact` + the `tail_filterNeeded` composition (all 5
    `unless`-blocks unchanged, monotone in the surplus base, collapsing to the
    loop-end potential).
  * `modifySoname.remove` (`f := ·.removeSoname`) — bound
    `patchDynamicEntries_removeSoname_size_le`, a `ShrinkRel`-shaped variant
    (`ShrinkRelSoname` tracks the four non-soname applied-flags; the soname tail
    block is the one that clears).  Closes the shrinking-op family 4/4.

  The 4× type-based outer-apply duplication
  (`apply{Versym,SysvHash,GnuHash,Verneed}_*`) is collapsed to 3 generic lemmas
  `applyTypeOpt_{dynamic_comm,dynamicIdx,content_at}` keyed on `ty ≠ SHT_DYNAMIC`,
  with the per-type applies as one-line wrappers.  The `Adapter.{foldl_proj_size_le_add,
  idForIn_proj_size_le}` bridges (loop-only `≤ init + as.size` bound) are landed
  but unused by the relative-bound proofs — kept for the absolute-bound route a
  growing op might need.

  **Growing ops — the `mapDynamicOp` growers are now FULLY DERIVED**
  (`Patchelf/Elf/OpToElfFactorGrow.lean` + `Patchelf/Elf/GrowEOFDisjointOfBase.lean`).
  A growing op widens a section's `encodedSize` at its original offset, so the
  three per-section disjointness invariants on `eo` genuinely BREAK and the
  shrink core (`newDyn.size ≤ oldDyn.size`) cannot apply.  `encode`'s
  `prepLayoutForEncode`/`growEOFWith` re-lays-out the file (flags the
  overlapping grown sections stale, relocates them), so the NORMALIZED form is
  `spliceRegionsDisjoint` even though `eo` is not.  The keystone grow driver
  `tierD_roundtrip_of_grown_eo` is identical to `tierD_roundtrip_of_eo_facts`
  except it HYPOTHESIZES that normalized-form `spliceRegionsDisjoint`
  (`hSplice`) and derives every other `EncodePreconditions` field from `eo` via
  the `*_normalized_of_eo` helpers + `tierD_roundtrip_of_valid`.

  `GrowEOFDisjointOfBase.lean` PROMOTES `hSplice` from a hypothesis to a DERIVED
  fact for the two `mapDynamicOp` growers (PLAN-GROWING-OPS §3 Commit 3, the
  "very-high-risk" item, LANDED).  Mechanism: a `mapDynamicOp` grower widens
  ONE section at its FIXED offset; section-0-NULL + the 3 header/table clauses
  are size-independent (transport verbatim);
  `headerSectionDisjoint`/`phdrSectionDisjoint` survive via the LEFT disjunct
  (a section AFTER a region stays disjoint when it grows at a fixed offset) —
  needing only that the dynamic section sits after the ELF header and after the
  phdr table (`hDynAfterHeader`/`hDynAfterPhdr`, two honest offset side
  conditions, true for every real ELF, WEAKER than the shrink path's
  `hSizeBound`); `shdrSectionDisjoint` + `sectionsNonOverlapping` break but
  `growEOFWith` RE-ESTABLISHES them.  Establisher
  `spliceRegionsDisjoint_of_grown_base` + corollary
  `Adapter.mapDynamicOp_spliceRegionsDisjoint_of_base` (mirror of
  `mapDynamicOp_structural_transport`, reusing `RemoveRpathFactorData`); both
  pure `[propext, Classical.choice, Quot.sound]`.  The two capstones
  `toElfFile_{addDebugTag,noDefaultLib}_tierD_roundtrip_derived` MOVED here and
  were UPGRADED: they NO LONGER hypothesize `hSplice` — they DERIVE it via the
  corollary, so their surface is the no-op base's 6 structural invariants (same
  as the SHRINK capstones) + the 2 offset side conditions.  Axioms `[propext,
  Classical.choice, Quot.sound]` + 3 bv_decide, no `sorryAx`.  The driver
  `tierD_roundtrip_of_grown_eo` STAYS in `OpToElfFactorGrow.lean` and KEEPS its
  hypothesized `hSplice` (still needed by `addNeeded`).

  **Dynstr growers — Tier-D capstones LANDED, hSplice HYPOTHESIZED**
  (`Patchelf/Elf/OpToElfFactorGrowDynstr.lean`, PLAN-GROWING-OPS §3 Commit 5).
  `addNeeded` / `modifyRPath.set` / `modifySoname.set` use `growDynstrDynamicOp`
  (dynstr AND dynamic both grow).  The genuinely-new artifact is the
  **Strategy-A two-field factoring**, DERIVED: the key insight that collapses
  the "two-field" problem to ONE field is `addNeeded typed lib h = { tg with
  dynamic := tg.dynamic.map (·.pushNeeded off) }` by `rfl`, where `tg :=
  (typed.growDynstr lib).1` is the base with dynstr grown + dynsym/dynamic
  rebased — the ENTIRE dynstr growth is ABSORBED into the base `toElfFile
  template tg`, leaving a single `.dynamic` update at `iDyn`, so NO parallel
  `.strtab`-commutation suite was needed.  The keystone
  `toElfFile_dynamicMapMono_factor` generalizes `toElfFile_mapDynamicOp_factor`
  to a MONOMORPHIC `g : DynamicSection tg.dynstr → DynamicSection tg.dynstr`
  (the grow-dynstr mutator is `ds`-monomorphic, tied to `off : Fin
  tg.dynstr.size`; the factoring only touches `.dynamic` as `Option.map`, so it
  reuses `innerChain_factor_general` verbatim); the three growers then differ
  only in `g` (`pushNeeded off` / `setRpathTag fr off` / `setSonameOff off`).
  Per-op factorings `toElfFile_{addNeeded,modifyRPath_set,modifySoname_set}_factor`
  + the content-at-`iDyn` corollary `toElfFile_addNeeded_content_at_dynamicIdx`
  (the building block for a future hSplice derivation) are `[propext,
  Quot.sound]`.  The three capstones
  `toElfFile_{addNeeded,modifyRPath_set,modifySoname_set}_tierD_roundtrip_derived`
  (REAL ops' parse∘encode round-trip) instantiate `tierD_roundtrip_of_grown_eo`
  and so HYPOTHESIZE the normalized form's `spliceRegionsDisjoint` (`hSplice`,
  first-cut caliber) — UNLIKE the `mapDynamicOp` growers, whose `hSplice` is
  derived.  `[propext, Classical.choice, Quot.sound]` + 3 bv_decide, no
  `sorryAx`.

  **So all growing ops named in PLAN-GROWING-OPS now have a Tier-D capstone.**
  The shrinking-op family is COMPLETE (4/4); the `mapDynamicOp` growers are
  FULLY DERIVED (`addDebugTag`/`noDefaultLib`, carrying only the 2 offset side
  conditions atop the no-op-base surface the shrink ops use); the
  `growDynstrDynamicOp` growers have capstones LANDED with the two-field
  factoring derived but `hSplice` still hypothesized.  **The ONLY remaining
  §5.1 growing-ops item:** DERIVE `hSplice` for the dynstr growers — a
  TWO-grown-section analogue of `mapDynamicOp_spliceRegionsDisjoint_of_base`
  (the `.dynstr` section grows too); `toElfFile_addNeeded_content_at_dynamicIdx`
  is the building block, but the establisher is NOT done.

### Priority 2 gaps (test / spec coverage)

(All landed: `addDebugTag_observable_strong`,
`removeNeeded_needed_size_lt`, and shell test 00.  See ROADMAP §2.)

**§5.2 op-observable completeness — DONE.**  Every mutating op now has an
adversary-rejecting observable.  Final gaps closed: `noDefaultLib_observable_strong`
(present→`v|||DF_1_NODEFLIB` ∨ absent→`DF_1_NODEFLIB` case-split, mirroring
`addDebugTag_observable_strong`) + `modify{RPath,Soname}_set_preserves`
(non-corruption companions — the `.set` ops already rejected identity via the
`dynstr.lookup off = name` clause; these add the "touches only its slot,
preserves `needed.size`/`flags1`/`debug`" axis).  All `[propext, Quot.sound]`.

### Priority 3 gaps (C++ patchelf parity)

- **`.gnu.hash` rebuild** in `rename-dynamic-symbols` — DONE.
  `Patchelf/Elf/GnuHashRebuild.lean` mirrors C++
  `rebuildGnuHashTable`; `Ops/RenameDynamicSymbols.lean` exposes
  `gnuHashRebuildOp` as a CLI post-pass.  Reorders dynsym + versym;
  rewrites bloom/buckets/chain.  Returns the dynsym permutation
  for the reloc remap.  See ROADMAP §3.3.
- **Relocation symbol-index remap** — DONE.
  `Patchelf/Elf/RelocRemap.lean` walks SHT_REL/SHT_RELA section
  bytes, applies the dynsym permutation to every entry's `r_info`
  high-32-bit symbol index.  Tested on a real glibc binary: rename
  forces bucket movement, relocations correctly retarget, binary
  still runs.
- **`.gnu.version_r vn_file` update in `replace-needed`** — DONE.
  `Patchelf/Elf/Ops/ReplaceNeeded.lean` exposes
  `VerneedSection.rewriteVnFile`; both `replaceNeededReuse` and
  `replaceNeeded` thread it through.  See ROADMAP §3.4.
- **PT_GNU_STACK append** when missing — `Ops/Execstack.lean` only
  maps over existing PT_GNU_STACK phdrs; C++ appends when absent.
  Synthesizing a new phdr requires growing the phdr table; bundle
  with §3.5a below.  See ROADMAP §3.5b.
- **Allocate a fresh PT_LOAD when extension is unsafe** — DESIGN
  READY, IMPL OPEN.  `growEOFWith` bails to `layoutForEncoding`
  (caught by the validator with exit 5) when `canExtendLastPtLoad`
  rejects.  C++ patchelf's `rewriteSectionsLibrary` allocates a
  new PT_LOAD; that path needs phdr-table growth.  Complete
  porting plan in
  [`../research/REWRITE-FRESH-PT-LOAD-DESIGN.md`](../research/REWRITE-FRESH-PT-LOAD-DESIGN.md):
  ~530 LOC, ~3 days for the in-place sub-case, +~150 LOC for the
  `relocatePht` sub-case.  This is the only feature gap that
  blocks a real binary class today (BSS-heavy ELFs like coreutils
  `ls`).  See ROADMAP §3.5a.  Fresh-agent pickup prompt at
  [`../research/PICKUP-PROMPT-FRESH-PT-LOAD.md`](../research/PICKUP-PROMPT-FRESH-PT-LOAD.md).

### Recent work (2026-05)

**§5.1 dynstr growers' Tier-D LANDED — every growing op now has a capstone
(commit `c9bf8ce`).**  New module `Patchelf/Elf/OpToElfFactorGrowDynstr.lean`
(~360 LOC, registered via a `public import` in `Patchelf.lean` after
`OpToElfFactorGrow`) ships Tier-D round-trips for the `growDynstrDynamicOp`
growers `addNeeded` / `modifyRPath.set` / `modifySoname.set` (dynstr AND dynamic
both grow) — PLAN-GROWING-OPS §3 Commit 5.  The genuinely-new artifact is the
**Strategy-A two-field factoring**, DERIVED.  Key insight collapsing "two fields"
to one: `addNeeded typed lib h = { tg with dynamic := tg.dynamic.map
(·.pushNeeded off) }` by `rfl`, where `tg := (typed.growDynstr lib).1` is the
base with dynstr grown + dynsym/dynamic rebased — the ENTIRE dynstr growth is
ABSORBED into the base `toElfFile template tg`, so the only delta is a single
`.dynamic` update at `iDyn` and NO parallel `.strtab`-commutation suite was
needed.  Keystone `toElfFile_dynamicMapMono_factor` generalizes
`toElfFile_mapDynamicOp_factor` to a MONOMORPHIC `g` on `.dynamic` (the
grow-dynstr mutator is `ds`-monomorphic, tied to `off : Fin tg.dynstr.size`; the
proof only touches `.dynamic` as `Option.map`, reusing `innerChain_factor_general`
verbatim); per-op factorings `toElfFile_{addNeeded,modifyRPath_set,modifySoname_set}_factor`
+ corollary `toElfFile_addNeeded_content_at_dynamicIdx` (building block for a
future hSplice derivation) are `[propext, Quot.sound]`.  The three capstones
`toElfFile_{addNeeded,modifyRPath_set,modifySoname_set}_tierD_roundtrip_derived`
(REAL ops' parse∘encode round-trip) instantiate `tierD_roundtrip_of_grown_eo`,
so they HYPOTHESIZE the normalized form's `spliceRegionsDisjoint` (`hSplice`,
first-cut caliber) — UNLIKE the `mapDynamicOp` growers, whose `hSplice` is now
derived.  `[propext, Classical.choice, Quot.sound]` + 3 bv_decide, no `sorryAx`;
113 lake jobs (was 112), 54/54 tests.  **Every growing op named in
PLAN-GROWING-OPS now has a Tier-D capstone.**  The ONLY remaining §5.1
growing-ops item: DERIVE `hSplice` for these dynstr growers — a TWO-grown-section
analogue of `mapDynamicOp_spliceRegionsDisjoint_of_base` (the `.dynstr` section
grows too); `toElfFile_addNeeded_content_at_dynamicIdx` is the building block,
but the establisher is NOT done.

**§5.1 `mapDynamicOp` growers' `hSplice` DERIVED — growers now fully derived
(commit `bfafd42`).**  New module `Patchelf/Elf/GrowEOFDisjointOfBase.lean`
(~300 LOC, registered via a `public import` in `Patchelf.lean`) PROMOTES the
growing-ops `hSplice` from a HYPOTHESIS to a DERIVED fact for the two
`mapDynamicOp` growers (`addDebugTag`/`noDefaultLib`) — PLAN-GROWING-OPS §3
Commit 3, the "very-high-risk" item.  A `mapDynamicOp` grower widens ONE section
(the dynamic section) at its FIXED offset; section-0-NULL + the 3 header/table
clauses transport verbatim (size-independent), the two per-section clauses
survive via the LEFT disjunct (a section after a region stays disjoint when it
grows at a fixed offset — needs only `hDynAfterHeader`/`hDynAfterPhdr`, two
honest offset side conditions WEAKER than the shrink path's `hSizeBound`), and
`shdrSectionDisjoint`/`sectionsNonOverlapping` are re-established by
`growEOFWith` so they are not preconditions.  Establisher
`spliceRegionsDisjoint_of_grown_base` + corollary
`Adapter.mapDynamicOp_spliceRegionsDisjoint_of_base` (mirror of
`mapDynamicOp_structural_transport`, reusing `RemoveRpathFactorData`) + grow
lemmas (`IntervalDisjoint_grow_right_of_le`,
`ElfFile.updateSectionContent_sectionInterval_grow` /
`_headerSectionDisjoint_grow` / `_phdrSectionDisjoint_grow`) — establisher +
corollary pure `[propext, Classical.choice, Quot.sound]`.  The two capstones
`toElfFile_{addDebugTag,noDefaultLib}_tierD_roundtrip_derived` MOVED here from
`OpToElfFactorGrow.lean` and were UPGRADED: they NO LONGER hypothesize `hSplice`
— their surface is the no-op base's 6 structural invariants (same as the SHRINK
capstones) + the 2 offset side conditions; `[propext, Classical.choice,
Quot.sound]` + 3 bv_decide, no `sorryAx`.  The generic driver
`tierD_roundtrip_of_grown_eo` STAYS in `OpToElfFactorGrow.lean` and KEEPS its
hypothesized `hSplice` (still needed by `addNeeded`).  112 lake jobs (was 111),
54/54 tests.  Still open: the dynstr-growing `growDynstrDynamicOp` ops
(`addNeeded`, `modify{RPath,Soname}.set`, Commit 5).

**§5.1 growing-ops Tier-D keystone + `addDebugTag`/`noDefaultLib` landed.**
New module `Patchelf/Elf/OpToElfFactorGrow.lean` (~210 LOC, registered via a
`public import` in `Patchelf.lean`) ships the FIRST Tier-D round-trips for
GROWING ops.  The keystone driver `tierD_roundtrip_of_grown_eo` mirrors
`tierD_roundtrip_of_eo_facts` but HYPOTHESIZES the normalized form's
`spliceRegionsDisjoint` (`hSplice`) — which a grown `eo` cannot supply, since its
widened section overlaps a neighbor — and the layout pass
(`prepLayoutForEncode`/`growEOFWith`) re-lays-out the file to produce the disjoint
normalized form; every other `EncodePreconditions` field stays derived from `eo`.
The two `mapDynamicOp` growers (dynstr unchanged, `.dynamic` +≤1) instantiate it
by `exact`: `toElfFile_{addDebugTag,noDefaultLib}_tierD_roundtrip_derived`.  All
three theorems `[propext, Classical.choice, Quot.sound]` + 3 bv_decide, no
`sorryAx`; 111 lake jobs (the new module added one), 54/54 tests.  Deferred to
dedicated sessions: the grow-tolerant `growEOFWith` disjointness lemma that would
DERIVE `hSplice` (PLAN-GROWING-OPS Commit 3), and the dynstr-growing
`growDynstrDynamicOp` ops' two-field factoring (`addNeeded`,
`modify{RPath,Soname}.set`, Commit 5).

**§5.1 `OpToElfFactor` genericized over `mapDynamicOp f` + removeNeeded landed.**
Five commits taking the `removeRpath`-specific factoring generic: (1) structural
cleanup (24 namespace blocks → 2, dead-field/param removal); (2) collapse the 4×
type-based outer-apply duplication into 3 `applyTypeOpt_*` generic lemmas;
(3) genericize the factoring + transport + capstone over an arbitrary `f`
(`toElfFile_mapDynamicOp_factor`, `mapDynamicOp_structural_transport`,
`toElfFile_mapDynamicOp_tierD_roundtrip_derived`); (4) re-derive `removeRpath` as
an instantiation (statement + axioms byte-identical — the regression gate held)
and add `modifyRPath.remove` as a free second op; (5) `removeNeeded` — the payoff
— landing the one new proof (`patchDynamicEntries_filterNeededBy_size_le` via the
`NeededRel` potential function) + its capstone instantiation.  A sixth commit
added `modifySoname.remove` (`patchDynamicEntries_removeSoname_size_le`, a
`ShrinkRel` variant), closing the shrinking-op family 4/4 — confirming the
predicted ~1-size-bound cost of each additional shrink shape.

**§5.1 `removeRpath` structural derivation (earlier).** Two commits: (1) a
compositional `patchDynamicEntries` refactor (pure loop fold + explicit
tail appends, byte-identical to the old do-block) unblocking the relative
output-size bound `patchDynamicEntries_stripRpath_size_le`; (2) the new
`OpToElfFactor.lean` module factoring `removeRpath`'s `toElfFile` output as
a single `.dynamic`-shrink on the no-op output and transporting the 6
structural disjointness invariants + section-0-NULL to it, yielding the
capstone `toElfFile_removeRpath_tierD_roundtrip_derived` —
`parse (encode (toElfFile … (removeRpath …))) = .ok …` with the op-output
structural invariants DERIVED, not hypothesized (§5.1 criterion 2).

**Cleanup pass.** Six commits removing mechanical duplication:
`addRpathEntry := modifyRPath … .set` alias; `applyOpt` combinator
folding 7 `applyX` definitions in `Adapter.lean`;
`discharge_ofElfFile_proj` macro folding 4 byte-identical proofs
in `AdapterRoundtrip.lean`; `printHandler`/`dynHandler`/`noPreHandler`
combinators in `CLI.lean` plus `isReadOnlyName` derivation
(killing the `readOnlySubcommands` drift surface); ByteRoundtrip
simp-set lifting 9 dead width-lift theorems; SectionOps trim of 6
dead theorems; `simp_splice` discharger extension to chain through
`writeArray_*_size` simps (4 region preservation proofs collapsed
by ~88 LOC each).  Total: ~−260 LOC; no regressions.

**Feature-gap pass.** Three commits closing the most-impactful C++
parity gaps that don't require multi-day phdr-table-growth work:
`vn_file` rewrite in `replace-needed` (§3.4), GNU hash rebuild
(§3.3), reloc symbol-index remap.  Plus a complete porting plan
([`../research/REWRITE-FRESH-PT-LOAD-DESIGN.md`](../research/REWRITE-FRESH-PT-LOAD-DESIGN.md))
for §3.5a (fresh PT_LOAD allocation), the only remaining
real-binary gap.
