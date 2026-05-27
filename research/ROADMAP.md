# Deferred-Work Roadmap

Forward-looking ledger of work deferred from the Lean 4 `patchelf`
port.  Current state of landed work is in
[`lean/STATUS.md`](../lean/STATUS.md); this document is the
forward-looking view.

> **Layout + validator landed.** The PT_LOAD coherence work designed
> in [`REWRITE-PHASE-3-DESIGN.md`](REWRITE-PHASE-3-DESIGN.md) shipped
> in a minimal form: `growEOF` + `syncDtAddrTagsInFile` (replacing
> `layoutForEncoding` as the primary layout strategy) plus a
> decidable pre-write validator (`Patchelf/Elf/Validate.lean`) that
> the CLI runs before every write.  CLI also migrated to lean4-cli
> subcommands.  This closes ROADMAP §3.6 and §3.7 outright; renders
> §3.1 obsolete; reduces §3.5 to "PT_GNU_STACK append" (a different
> phdr-table-growth subset).  Items §1.1, §1.2, §5.1 remain open
> under the design doc's broader unification arc.

---

## Picking up work (for fresh agents)

**Build and test from `lean/`:**
```sh
nix develop ../.#lean -c lake build              # expect a clean build
nix develop ../.#lean -c bash tests/run.sh       # 49/49 shell tests expected
grep -rn "sorry\b" Patchelf/                     # zero matches expected
```

**Recommended pickup order:**

- **`prepLayoutForEncodeWith_produces_spliceRegionsDisjoint` — DONE.**
  `Encoder.lean` exposes the composed theorem the op-level Tier D
  proofs consume: under the 5 structural input invariants
  (`headerPhdrDisjoint` / `headerShdrDisjoint` / `phdrShdrDisjoint` /
  `headerSectionDisjoint` / `phdrSectionDisjoint`) plus
  `hSection0Null`, the encoder's full layout pre-pass
  (`prepLayoutForEncodeWith pageSize? e`) outputs `spliceRegionsDisjoint`.
  Composes `growEOFWith_produces_spliceRegionsDisjoint` (`GrowEOF.lean`,
  discharges all 3 branches via the unified `PlaceFold.{placeStep,
  placeFold, Placement, PairDisjoint, FoldInv}` scaffolding —
  `layoutForEncoding` and `appendStaleSections` are specializations
  parameterized on `verbatim`, `transform`, `baseOffset`) and
  `syncDtAddrTagsInFile_preserves_spliceRegionsDisjoint`.
  Item 5.1 (op-level Tier D) is now unblocked.
- **Items 1.1 and 1.2** can land independently and unlock op-level
  preservation theorems.  1.1's decidable predicate already exists in
  `Validate.lean`; the unfinished work is parser-side threading.  1.2's
  `syncDtStrszInFile_preserves_valid` is the worked example — the three
  remaining preservations should reuse the same SectionOps helpers.
- **Item 3.5a (allocate fresh PT_LOAD)** unblocks the BSS-heavy binary
  class that `growEOFWith` currently bails on.  Estimated ~600 LOC
  including the validator-passing proof.
- **Item 4.2** is an independent typed-side completeness item;
  `.verneed` is stored as `.raw` at the byte layer, so the
  byte-roundtrip doesn't depend on it.

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

#### 1.1 Parser: establish `IsLoadable`, not just `IsValid`

**Severity:** structural gap.  Partially mitigated at the I/O
boundary: `Patchelf/Elf/Validate.lean` provides decidable
`IsLoadableBytes` and the CLI runs `validateBytes` before every
write (exit 5 on failure, file unchanged).  This is the *runtime*
safety net.  The *static* gap remains: `Parser.parse` still returns
`ParsedElf` carrying only `IsValid`, no op carries an
`_preserves_loadable` theorem, and no proof connects parser output
to validator success.

**What to do:** extend `Parser.parse` to return
`LoadableElfFile` (or an enhanced `ValidElfFile` with an optional
`IsLoadable` field).  Check `sectionsNonOverlapping`,
`ptInterpAgreement`, `ptDynamicAgreement`, `segmentCongruence`,
`shdrSectionDisjoint`, `sectionFileInSomePtLoad` at the end of
parse when `IsValid` holds.  On failure return a new `ParseError`
subclass (not `shdrIdxMismatch`).

**Downstream:** once `parse` establishes `IsLoadable`, make every op
preserve it via an `_preserves_loadable` theorem.  Most ops will
preserve all clauses definitionally; the interesting ones are
`setInterpreter` (PT_INTERP agreement after changing interp offset)
and any op whose post-encode would route through `growEOFWith`'s
BSS-collision fallback.

**Estimated cost:** ~500 LOC (parser extension + 14 op preservation
theorems + per-clause Decidable instances refined for better error
classification).  The decidable predicate is already in
`Validate.lean`; this work is mostly threading.

#### 1.2 Pre-encode passes: `_preserves_valid` theorems

**Status:** `syncDtStrszInFile_preserves_valid` (`Encoder.lean`)
landed.  Three remain:

- `growEOFWith_preserves_valid` — offsets change, shoff changes,
  last PT_LOAD `filesz`/`memsz` extend, PT_INTERP/PT_DYNAMIC track
  moved sections.  None of the 8 IsValid clauses depend on offsets;
  the deeper claim — `_preserves_loadable` — is more interesting
  and the actual point of `growEOF` existing.
- `syncDtAddrTagsInFile_preserves_valid` — rewrites `.dynamic`'s
  DT_STRTAB/SYMTAB/HASH/GNU_HASH/VERNEED/VERSYM/JMPREL/REL/RELA
  entries' `value` to section addresses; `dynamic_wf`'s string-ref
  predicate isn't an address tag, so it survives by the same
  argument as `syncDtStrszInFile`.
- `layoutForEncoding_preserves_valid` — the BSS-collision fallback;
  same shape as `growEOFWith` but doesn't preserve PT_LOAD coverage.

**Estimated cost:** ~200 LOC each.  `growEOFWith_preserves_loadable`
is the load-bearing one and probably ~500 LOC.

**Supporting infrastructure landed.** `Patchelf/Elf/SectionOps.lean`
exposes the helpers `growEOFWith` / `syncDtAddrTagsInFile`'s
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

#### 1.3a `EncodePreconditions` from parser output — 10 of 11 done

`encodePreconditions_of_parser bs shdrs e` derives all fields except
`spliceDisjoint` from parser-output structural facts.  Per-clause
helpers:

| Clause | Helper | Caller-supplied side condition |
|---|---|---|
| `identValid` | `identBytesValid_of_parseHeader_ok` | `parseHeader bs = .ok e.header` |
| `typesMatch` | `sectionsFromShdrs_typeContentMatch` | `e.sections = sectionsFromShdrs bs shdrs` |
| `nullEmpty` | `sectionFromShdr_null_empty` | per SHT_NULL shdr: `sh.size.val = 0` |
| `sizeFit` | `sectionFromShdr_encodedSize_le` | per shdr: `sh.size.val < UInt64.size` |
| `syncOk` | `syncDtStrszInFile_eq_id` | `e.dynStrszCoherent` |
| `headerFit_{entry,phoff,shoff}` | `parseHeader_byte_facts` + `(readU64 _ _).toNat_lt` | `parseHeader bs = .ok e.header` |
| `phdrFit` | per-element `Decode.decodePhdrs_getElem` + `toNat_lt` | `e.phdrs = decodePhdrs bs ...` |
| `shdrFit` | per-element `Decode.decodeShdrs_getElem` + `toNat_lt` | `shdrs = decodeShdrs bs ...` |

`spliceDisjoint` is the missing field.  Parser-side: not
derivable, since overlapping sections are spec-valid and the parser
shouldn't enforce pairwise region disjointness.

Encoder-output side: **DONE.**
`GrowEOF.growEOFWith_produces_spliceRegionsDisjoint` discharges all 3
branches (fast path / fallback / main) under structural input
invariants `headerPhdrDisjoint` / `headerShdrDisjoint` /
`phdrShdrDisjoint` / `headerSectionDisjoint` / `phdrSectionDisjoint`
plus `hSection0Null`.  The unified `PlaceFold` scaffolding in
`LayoutEngine.lean` is parameterized over `verbatim`, `transform`,
and `baseOffset`, so `layoutForEncoding`'s and `growEOFWith`'s
splice-disjointness proofs share one fold-induction skeleton; client
specializations exhibit a `TransformSpec` (field-preservation
contract) and a `VerbatimWitness` (NULL/NOBITS-or-bound + pairwise
disjoint for verbatim entries).  The remaining gap to *unconditional*
Tier D is op-level: each op must establish the 5 input invariants on
its output (parser-derivable for any op that doesn't widen the file
or move sections; the layout-touching ops route through `growEOFWith`
which preserves them).

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

#### 3.3 `.gnu.hash` rebuild in `rename-dynamic-symbols`

The current op rejects binaries with `.gnu.hash` (op precondition).
GNU hash is more complex than SysV (bloom filter + bucket offsets +
chain tail). Adding it: ~150 LOC on top of the existing SysV rebuild.

#### 3.4 `.gnu.version_r` update in `replace-needed`

The `replace-needed` op updates `.dynamic` and grows `.dynstr`
but doesn't rewrite matching `vn_file` fields in
`.gnu.version_r`.  Real-world impact minor (dynamic linkers
resolve versions via Verdef, not vn_file).  Would roughly triple
the `replaceNeeded_preserves_*` proof size.

#### 3.5a Allocate a fresh PT_LOAD when extension is unsafe

`growEOFWith`'s safety gate (`canExtendLastPtLoad`) rejects when
extending the last PT_LOAD's `filesz`/`memsz` would clobber
already-allocated BSS or fall outside the existing alignment.  In
that case, `growEOFWith` falls back to `layoutForEncoding`'s
unaware repack and the pre-write validator catches the resulting
non-loadable bytes (exit 5).  C++ patchelf's `rewriteSectionsLibrary`
allocates a brand-new PT_LOAD by growing the phdr table; that's
the strictly more general fix and unblocks the BSS-heavy binary
class (e.g. coreutils `ls`).  Estimated ~600 LOC: phdr-table-grow
in `growEOFWith` + corresponding splice-pipeline updates +
preservation argument.

#### 3.5b PT_GNU_STACK append when missing

`set-execstack` on a binary without PT_GNU_STACK phdr is currently
a no-op (`Ops/Execstack.lean` only maps over existing phdrs);
C++ appends.  Adding it shares the phdr-table-growth machinery
with §3.5a and is best done together.

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

#### 5.1 Op-level byte roundtrip lemmas — UNBLOCKED, NON-TRIVIAL

A stronger replacement for the existing `_preserves_valid` lemmas:
prove `parse (encode (op e)) = .ok ⟨prepLayoutForEncode
(syncDtStrszInFile (op e)), _⟩` for each op.

`spliceDisjoint` is discharged by
`Encoder.prepLayoutForEncodeWith_produces_spliceRegionsDisjoint`
(landed; see §1.3a) — each op needs to establish the 5 structural
input invariants on its own output (`headerPhdrDisjoint` etc.),
which are parser-derivable for any op that doesn't widen the file.

**Obstacle for op-level Tier D, discovered.**  `Adapter.toElfFile`
threads `typed : ValidElfFile` through dependent-type-bearing
matches (e.g., `applyDynamic`'s match on
`typed.dynamic : Option (DynamicSection typed.dynstr)`).  When `op`
is `setOsAbi` — which only changes `header.ident.osAbi` — the
record-update form `{ typed with header := ... }` doesn't reduce
inside the dependent matches even though `(setOsAbi abi).dynstr =
typed.dynstr` holds by `rfl`.  The result: `Adapter.toElfFile
template (typed.setOsAbi abi)` is *not* `rfl`-equal to
`Adapter.toElfFile template typed`, blocking the obvious
"non-section ops are sections-trivial" argument.

Workarounds for op-level Tier D, in increasing complexity:
* (a) Rephrase `Adapter.toElfFile`'s applies to take separate
  arguments instead of `typed : ValidElfFile`, e.g.
  `applyDynamic (e : ElfFile) (dyn? : Option (DynamicSection ds))
  (ds : StringSection) : ElfFile`.  Removes the dependent typing
  problem at the cost of a wider call surface.  Estimated ~200 LOC
  refactor.
* (b) Prove an explicit `Adapter.toElfFile`-congruence lemma family
  (one per op): `toElfFile_<op>_eq` showing
  `Adapter.toElfFile template (op typed) =
   { Adapter.toElfFile template typed with header := ... }` directly
  (not via `rfl`).  Each op gets a custom proof; ~50 LOC per op.
* (c) Define op-level Tier D in a "structural transport" style:
  prove `EncodeCompatible (toElfFile template typed) (toElfFile
  template (op typed))` (where `EncodeCompatible` says headers agree
  modulo the op's specific change) and a single `EncodePreconditions.transport`.
  Was attempted; the `syncOk` clause's full ElfFile-equality made the
  proof tangled under the dependent-type issues.

For ops that *do* modify section content (most: `addNeeded`,
`removeNeeded`, `setRpath`, `replaceNeeded`, etc.) the picture is
different because they do change `sections`; these need their own
`_preserves_spliceDisjoint` proofs anyway, and the dependent-type
complication only affects "no-op" sections-trivial ops like
`setOsAbi`, `noDefaultLib`, `addDebugTag`.

Recommend revisiting this item after picking up §1.1 (Parser
establishes `IsLoadable`) — that pins down where the input
invariants come from, and may suggest a cleaner shape for the op
preservation theorems.

#### 5.2 Op-level `_observable` completeness

Every mutating op should have at least one observable theorem that
an adversarial identity function fails.  Current status per op:

| Op | Observable | Adversarial-identity rules out? |
|---|---|---|
| setOsAbi | yes + preserves_everything_else | yes (changed + no-other-fields-changed) |
| modifyExecstack | yes (set + clear) | yes (PF_X set on all PT_GNU_STACK) |
| removeRpath | yes | partial (∀ i, tag ≠ rpathish) |
| removeNeeded | yes | weak (identity on files without lib) |
| clearSymbolVersion | yes (cleared + preserved_other) | yes |
| setInterpreter | yes | yes (.interp = encoded path) |
| addDebugTag | yes | weak (identity on files with DT_DEBUG) |
| noDefaultLib | yes | ? |
| addNeeded | yes | yes (`needed[0]` points at appended dynstr name; matches C++ front-insert) |
| addRpathEntry | yes | yes |
| modifyRPath.remove / .set | yes / ? | partial |
| modifySoname.delete / .set | yes / ? | partial |
| replaceNeeded / replaceNeededReuse | yes / yes | yes |
| renameDynamicSymbols | yes | yes (`.st_name` points at appended `.dynstr` entry) |

Strengthening the "weak" rows is tracked in §2.1.

#### 5.3 `SectionOps.lean` flatness — DONE

The 530-LOC preservation infrastructure had zero external callers
(the typed-section algebra's `Fin ds.size` indexing made it
obsolete) and was deleted.  `SectionOps.lean` is now 52 LOC:
`ElfFile.updateSectionContent` plus 3 `@[simp]` projection lemmas.

#### 5.4 Splice/extract simp set + tactic — DONE

`Patchelf/Elf/Tactic/SpliceSimproc{Attr,,Test}.lean` provide the
`[splice_simp]` simp set and a `simp_splice` macro
(`simp (discharger := splice_disch) only [splice_simp]`, where
`splice_disch` rewrites splice-buffer sizes and then runs `omega`).
The simp set is extensible via `@[splice_simp]`; new
`readUN_splice_*` or buffer-size lemmas attach without touching the
tactic file.

Original §5.4 estimate (~800 LOC bucket-1 collapse) was overstated;
actual delta was ~25 LOC across 3 splice-cascade sites in
`ByteRoundtrip.lean`.  The remaining bucket-1 LOC is structural
plumbing (per-section foldl preservation, disjointness extraction
from `spliceRegionsDisjoint`, buffer-size aliases) that isn't
splice-cascade-shaped.

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
