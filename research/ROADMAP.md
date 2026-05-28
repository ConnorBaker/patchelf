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
> Items §1.2 (only `_preserves_loadable` remaining) and §5.1
> remain open.  §3.5a fully landed (both in-place and relocatePht
> sub-cases — see below).  §1.1 parser side landed.  §1.2's
> `_preserves_valid` ladder fully landed (top-level
> `growEOFWith_preserves_valid` lands by composing four branches);
> only the load-bearing `growEOFWith_preserves_loadable` remains.
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

**Recommended pickup order:**

- **§3.5a both sub-cases — LANDED.**
  In-place (`growEOFWithFreshPtLoad`): handles binaries with
  phdr-table headroom.  Test 53 covers it.
  RelocatePht (`growEOFWithFreshPtLoadReloc`): moves the phdr
  table itself to the appended region for binaries packed tight
  against the first section.  Test 54 covers `coreutils ls`.
- **§1.3a `prepLayoutForEncodeWith_produces_spliceRegionsDisjoint` — DONE.**
  `Encoder.lean` exposes the composed theorem.  See §1.3a for details.
  This was intended to unblock §5.1 (op-level Tier D), but a
  dependent-type obstacle in `Adapter.toElfFile` was discovered when
  attempting the worked example — see §5.1 for details and three
  workaround paths.
- **§1.1 (Parser establishes `IsLoadable`)** is the most natural
  next pickup *for verification depth*.  Independent of §5.1's
  obstacle.  Threads the structural input invariants through the
  parser → `ParsedElf` bridge; the decidable predicate already
  exists in `Validate.lean`.  Recommended before revisiting §5.1 —
  clarifies the input-invariant chain.
- **§1.2 (pre-encode `_preserves_valid` theorems)** — three
  preservation theorems remain.  `syncDtAddrTagsInFile_preserves_spliceRegionsDisjoint`
  landed (different from `_preserves_valid`); the byte-layer `IsValid`
  preservations for `growEOFWith`, `syncDtAddrTagsInFile`, and
  `layoutForEncoding` are still open.  Reuse `SectionOps` helpers.
- **§4.2** is an independent typed-side completeness item;
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
`growEOFWith`'s fresh-PT_LOAD or relocatePht branches.  Pick up
under §1.2.

#### 1.2 Pre-encode passes: `_preserves_valid` theorems

**Status:** `syncDtStrszInFile_preserves_valid` (`Encoder.lean`)
and `syncDtAddrTagsInFile_preserves_valid` (`GrowEOF.lean`) landed.
Two byte-layer `IsValid` preservations remain:

- `growEOFWith_preserves_valid` — offsets change, shoff changes,
  last PT_LOAD `filesz`/`memsz` extend, PT_INTERP/PT_DYNAMIC track
  moved sections.  None of the 8 IsValid clauses depend on offsets;
  the deeper claim — `_preserves_loadable` — is more interesting
  and the actual point of `growEOF` existing.
- `syncDtAddrTagsInFile_preserves_valid` — DONE.
  `Patchelf/Elf/GrowEOF.lean`.  Mirrors
  `syncDtStrszInFile_preserves_valid`'s structure (aux + outer
  wrapper), with `e.dynstr = some ds` as a precondition (needed to
  derive `iDyn ≠ shstrndx` — `IsValid` alone doesn't force shstrndx
  to point at a strtab).  Real ELFs always satisfy the precondition;
  the runtime validator catches pathological inputs.

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

**`_preserves_loadable` partially landed.**
`layoutForEncoding_preserves_loadable` (`LayoutEngine.lean`)
shipped — covers the no-PT_LOAD branch of `growEOFWith`'s
dispatch.  Built on per-phdr `relocatePhdr_*` lemmas
(`_type`, `_align`, `_vaddr`, `_of_not_interp_dynamic`,
`_pt_interp`, `_pt_dynamic`).

Remaining open: the three `growEOFWith*` branches (main body,
fresh-PT_LOAD in-place, relocate) plus the top-level
`growEOFWith_preserves_loadable` dispatch.  These need per-phdr
facts for `updatePhdrsAfterMove` analogous to the
`relocatePhdr_*` lemmas, but the function is structurally more
involved: the `if i = lastIdx` branch updates filesz/memsz
(preserving type/offset/vaddr/align) which then crosses the
PT_INTERP / PT_DYNAMIC type-test if-then-else.  Tactic threading
is finicky — the proof needs careful `cases lastIdx?` +
`by_cases hLI : i = lastIdx` + `if_pos`/`if_neg` + the
record-update preservation through `phLast`-type identity.

For PT_LOAD-only segmentCongruence, the cleanest approach is a
per-PT_LOAD lemma `updatePhdrsAfterMove_pt_load_offset_vaddr_align`
that bypasses the PT_INTERP/PT_DYNAMIC tests via type-disjointness.
For the agreement clauses, lemmas `updatePhdrsAfterMove_pt_interp` /
`_pt_dynamic` mirror `relocatePhdr_pt_interp` / `_pt_dynamic` but
need to handle the lastIdx pre-update.
- `layoutForEncoding_preserves_valid` — the BSS-collision fallback;
  same shape as `growEOFWith` but doesn't preserve PT_LOAD coverage.

**Estimated cost:** ~200 LOC each.  `growEOFWith_preserves_loadable`
is the load-bearing one and probably ~500 LOC.

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
