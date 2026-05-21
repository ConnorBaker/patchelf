# Deferred-Work Roadmap

Forward-looking ledger of work deferred from the Lean 4 `patchelf`
port.  Current state of landed work is in
[`lean/STATUS.md`](../lean/STATUS.md); this document is the
forward-looking view.

> **Active design work.** The next major arc is designed in
> [`REWRITE-PHASE-3-DESIGN.md`](REWRITE-PHASE-3-DESIGN.md), which
> supersedes several entries below (§1.1, §1.2, §3.5, §3.6, §5.1;
> see the design doc's §8c for explicit dispositions of all
> ROADMAP §3.x items). The design doc is the load-bearing
> planning document for the validator + atomic write work, the
> (possibly skipped) unification refactor, and the
> `LayoutPlan` / `apply` / loader-coherent layout machinery.
> Three open compression decisions are tracked in the design
> doc's §8a; this ROADMAP will be rewritten once the validator
> work lands and the compression path is chosen.

---

## Picking up work (for fresh agents)

**Build and test from `lean/`:**
```sh
nix develop ../.#lean -c lake build              # 92/92 jobs expected
nix develop ../.#lean -c bash tests/run.sh       # 49/49 shell tests expected
grep -rn "sorry\b" Patchelf/                     # zero matches expected
```

**Recommended pickup order:**

- **Item 5.1's mechanical bridge** — 1.3a's structural piece is in
  place.  Op-level Tier D is now mechanical: per-op
  `_preserves_spliceDisjoint` follows from
  `layoutForEncoding_produces_spliceRegionsDisjoint` plus an
  `Adapter.toElfFile`-shape preservation argument.  ~14 ops × ~100 LOC.
- **Items 1.1 and 1.2** can land independently and unlock op-level
  preservation theorems.
- **Item 4.2** is an independent typed-side completeness item;
  `.verneed` is stored as `.raw` at the byte layer, so the
  byte-roundtrip doesn't depend on it.

**Patterns to know before touching Tier D / encoder proofs:**

- `Encoder.encode` and `Encoder.encodeBody` are `@[irreducible]`;
  use the `_eq` companion lemmas for unfolding.  Removing the
  attribute will time out per-byte access proofs at >32M
  heartbeats.
- For do-blocks that need proof navigation, rewrite to explicit
  `if-then-else` (the `Id.run do` form elaborates to lambda
  continuations that resist `simp [bind]`).  See
  `Parse.parseHeader` and `LayoutEngine.layoutAlreadyValid` for
  precedent.
- For loop-based decoders (`decodeDynamic`), use two-state
  foldl/loop induction — see `decodeDynamic_writeArray_eq` for
  the template.

---

## Deferred work, prioritized

### Priority 1 — Unblock tiers above IsValid

#### 1.1 Parser: establish `IsLoadable`, not just `IsValid`

**Severity:** structural gap. `IsLoadable` and `IsFullyValid` exist
as decidable predicates but are **never established by `parse`, never
preserved by any op, and never consumed by any other module.** They
are currently pure decoration.

**What to do:** extend `Parser.parse` to return
`LoadableElfFile` (or an enhanced `ValidElfFile` with an optional
`IsLoadable` field).  Check `sectionsNonOverlapping`,
`ptInterpAgreement`, `ptDynamicAgreement`, `segmentCongruence` at
the end of parse when `IsValid` holds.  On failure return a new
`ParseError` subclass (not `shdrIdxMismatch`).

**Downstream:** once `parse` establishes `IsLoadable`, make every op
preserve it via an `_preserves_loadable` theorem.  Most ops will
preserve all 4 clauses definitionally; the interesting ones are
`setInterpreter` (PT_INTERP agreement after changing interp offset;
encoder's `layoutForEncoding` handles this but op-level doesn't).

**Estimated cost:** ~500 LOC (parser extension + 14 op preservation
theorems + per-clause Decidable instances refined for better error
classification).

#### 1.2 Pre-encode passes: `_preserves_valid` theorems

**Severity:** latent correctness gap. `syncDtStrszInFile` and
`layoutForEncoding` in Encoder/LayoutEngine have no preservation
theorems — they're pure functions that LOOK like they preserve
`IsValid`, but nothing proves it.

**What to do:** prove
- `syncDtStrszInFile_preserves_valid` (content_wf holds because
  rewriting DT_STRSZ entries' values doesn't change isStringRef
  tags; dynamic_wf transfers since string-ref tags aren't DT_STRSZ;
  other clauses via `IsValid.of_sections_and_header_key_eq` modulo
  one content update).
- `layoutForEncoding_preserves_valid` (harder: offsets change, shoff
  changes, PT_INTERP/PT_DYNAMIC phdrs rewrite. All 8 IsValid clauses
  survive because they don't depend on offsets.  Or prove
  `IsLoadable` preservation instead since offsets are load-relevant).

**Estimated cost:** ~200 LOC each.

#### 1.3 Unconditional Tier D — DONE

`ByteRoundtrip.parse_encode_roundtrip` is unconditional under
`EncodePreconditions` (11 fields; 9 conceptual clauses, with
`headerFit_*` exploded into 3 separate fields covering
Nat-wrapper-to-`UInt64`-fit conditions; `phdrFit`, `shdrFit` for
`wrap_nat` fields).  All 4 witness field theorems proven.  See
`STATUS.md` §Tier D.

#### 1.3a Establish `EncodePreconditions` from realistic inputs — 10 of 11 done

`encodePreconditions_of_parser bs shdrs e` derives 10 of 11 fields
(9 conceptual clauses; the `headerFit_*` row in the table below
expands into 3 separate fields covering the Nat-wrapper-to-UInt64
fit conditions) from parser-output structural facts via these
helpers:

| Clause | Helper | Caller-supplied side condition |
|---|---|---|
| `identValid` | `identBytesValid_of_parseHeader_ok` (composes `parseHeader_byte_facts` + `identBytesValid_of_decodeHeader` + `identBytesValid_of_header`) | `parseHeader bs = .ok e.header` |
| `typesMatch` | `sectionsFromShdrs_typeContentMatch` | `e.sections = sectionsFromShdrs bs shdrs` |
| `nullEmpty` | `sectionFromShdr_null_empty` | per SHT_NULL shdr: `sh.size.val = 0` |
| `sizeFit` | `sectionFromShdr_encodedSize_le` | per shdr: `sh.size.val < UInt64.size` |
| `syncOk` | `syncDtStrszInFile_eq_id` | `e.dynStrszCoherent` |
| `headerFit_{entry,phoff,shoff}` | unfold `parseHeader_byte_facts` + `(readU64 _ _).toNat_lt` | `parseHeader bs = .ok e.header` |
| `phdrFit` | per-element via `Decode.decodePhdrs_getElem` + `(readU64 _ _).toNat_lt` | `e.phdrs = decodePhdrs bs ...` |
| `shdrFit` | per-element via `Decode.decodeShdrs_getElem` + `(readU64 _ _).toNat_lt` | `shdrs = decodeShdrs bs ...` |

Two refactors enabled the bridges: `Parse.parseHeader` rewritten
from `do` to explicit if-then-else (so the byte-fact bridge could
navigate via `by_cases + rw [if_neg]`), and `dynamicWellFormed`
split into `dynamicTerminated` + `dynamicStringRefsValid` (so the
sync proof doesn't depend on `.dynstr` presence).

**Structural piece DONE.**
`LayoutEngine.layoutForEncoding_produces_spliceRegionsDisjoint`
proves `(layoutForEncoding e).spliceRegionsDisjoint` unconditionally
under two parser-derivable preconditions:
- `hSection0Null`: `e.sections[0].type = SHT_NULL` (ELF spec; IsValid).
- `hHeaderPhdr`: `Layout.ehdrSize ≤ e.header.phoff.val` (header
  doesn't overlap phdr table; phoff = 64 in practice).

Architecture: private `Placement` (per-entry inheritance + offset
bounds) + `PairDisjoint` (pairwise non-overlap, in `sectionsNonOverlapping`'s
disjunct order) + bundled `LayoutInv` foldl motive.  ~561 LOC.
The `subst hSize` trick eliminates the `i` vs `state.1.size` mismatch
in `placement_step_new`; thereafter `Array.getElem_push_eq` applies
directly without dependent-getElem motive issues.  Layout-engine
arithmetic in unbounded `Nat` (the wrappers' representation) was a
prerequisite.

**Remaining gap (parser-output bridge wiring):** the encoder is
`encode e = encodeBody (if layoutAlreadyValid e' then e' else
layoutForEncoding e')` where `e' = syncDtStrszInFile e`.  For
`parse (encode e) = .ok e` to follow, BOTH branches need
spliceRegionsDisjoint.  Already-valid branch needs the extra 5
sub-clauses beyond what `layoutAlreadyValid` checks (header-phdr,
header-shdr, phdr-shdr, header-section, phdr-section).  Real ELFs
satisfy all 7, but the parser doesn't enforce pairwise region
disjointness on output.

The honest theorem for arbitrary parser output is
`parse (encode e) = .ok ⟨e'', _⟩` where `e''` is the post-pipeline
file (= `e'` if already valid, else `layoutForEncoding e'`).  This
is op-level Tier D (item 5.1).

### Priority 2 — Test coverage + spec strengthening

#### 2.1 Missing / weak observable theorems

- ~~**`renameDynamicSymbols`** has NO observable theorem.~~
  CLOSED: `renameDynamicSymbols_observable` landed at
  `Patchelf/Elf/Ops/RenameDynamicSymbols.lean:123` (asserts post-op
  `.dynsym[i].st_name` points at the appended new name in
  `.dynstr` for every renamed symbol; companion lemmas
  `_dynstr`, `_dynsym_isSome`, `_gnuHash` cover supporting state).
- **`addDebugTag_observable`** is too weak: satisfied by identity on
  files that already have DT_DEBUG. Should strengthen to: either
  DT_DEBUG was already present OR the post-op dynamic has one more
  entry than input.
- **`removeNeeded_observable`**: similarly weak.

#### 2.2 Smoke roundtrip test

Add a shell test that does `patchelf --print-os-abi fixture >
/dev/null && cmp fixture fixture.backup` — proves identity byte
roundtrip via CLI.  Catches regressions where encoder mutates bytes
gratuitously.

### Priority 3 — Feature parity with C++ patchelf

#### 3.1 Multi-op canonical ordering

Our CLI applies ops in argv order. C++ patchelf.cc:2445-2500 uses
a fixed canonical order (prints first, then mutations).  ~30 LOC
of sorting logic in `Main.runOps`.

#### 3.2 `shrinkRPath` filesystem probing

C++'s `shrinkRPath` checks the filesystem for each rpath directory
and filters accordingly.  Our `--shrink-rpath` accepts a pure
prefix whitelist via `--allowed-rpath-prefixes`.  Filesystem
probing at the Main.lean layer is possible (crosses the pure Ops
boundary; belongs in Main).

#### 3.3 `.gnu.hash` rebuild in `--rename-dynamic-symbols`

The current op rejects binaries with `.gnu.hash` (op precondition).
GNU hash is more complex than SysV (bloom filter + bucket offsets +
chain tail). Adding it: ~150 LOC on top of the existing SysV rebuild.

#### 3.4 `.gnu.version_r` update in `--replace-needed`

The `--replace-needed` op updates `.dynamic` and grows `.dynstr`
but doesn't rewrite matching `vn_file` fields in
`.gnu.version_r`.  Real-world impact minor (dynamic linkers
resolve versions via Verdef, not vn_file).  Would roughly triple
the `replaceNeeded_preserves_*` proof size.

#### 3.5 PT_GNU_STACK append when missing

`--set-execstack` on a binary without PT_GNU_STACK phdr is currently
a no-op. C++ patchelf appends the phdr. Adding it requires extending
`layoutForEncoding` to grow the phdr table.


#### 3.6 `--page-size <N>` actually used

Currently accepted and stored in `Options` but never consumed.
`layoutForEncoding` aligns by `section.addralign` only, not by page
size. C++ patchelf aligns PT_LOAD segments to page size; we would
need to extend the layout pass to do so.

#### 3.7 `--debug` verbose trace output

`--debug` is accepted but produces no trace output. The CLI doesn't
thread a debug flag into per-op diagnostic prints.

#### 3.8 Per-clause `ParseError` classification

`Parser.parse` on IsValid failure throws a generic
`shdrIdxMismatch`. Per-clause classification would surface specific
violations (e.g. `dynamicMissingNull`, `dynsymOffsetOutOfBounds`).
The 8 clauses are each decidable — a match-on-failing-clause could
produce targeted errors.

### Priority 4 — DSL extensions

#### 4.1 ~~`decode ∘ write = id` emission~~ — DONE

The DSL's forward-direction emission is in place.  All 7
fixed-layout schemas (`ElfIdent`, `ElfHeader`, `ProgramHeader`,
`SectionHeader`, `DynEntry`, `Symbol`, `Vernaux`) have
`X_decode_write : decode (X.write x) 0 = x` theorems generated
automatically by the `elf_schema` command.  These are consumed by
`section_decode_encode`'s per-content discharges.

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

#### 5.1 Op-level byte roundtrip lemmas — UNBLOCKED

Currently each op proves `_preserves_valid` (structural).  A stronger
version would prove `parse (encode (op e)) = .ok ⟨layoutForEncoding
(syncDtStrszInFile (op e)), _⟩` — the op-level Tier D.

**1.3a's structural piece is in place.**  Each op gets:
- `identValid`, `typesMatch`, `nullEmpty`, `sizeFit`, `headerFit_*`,
  `phdrFit`, `shdrFit` from a fresh `Adapter.toElfFile` traversal (all
  preserved by op shape; not from `IsValid`).
- `syncOk` directly because `encode` runs `syncDtStrszInFile`
  unconditionally as its first step.
- `spliceDisjoint` from
  `layoutForEncoding_produces_spliceRegionsDisjoint`.

~14 ops × ~100 LOC each, mostly mechanical.

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
| addNeeded | yes | yes (new DT_NEEDED exists) |
| addRpathEntry | yes | yes |
| modifyRPath.remove / .set | yes / ? | partial |
| modifySoname.delete / .set | yes / ? | partial |
| replaceNeeded / replaceNeededReuse | yes / yes | yes |
| renameDynamicSymbols | yes | yes (`.st_name` points at appended `.dynstr` entry; landed `Ops/RenameDynamicSymbols.lean:123`) |

All ops now have observable theorems; the remaining Priority-2
gap is observable *strength* (some satisfied by identity on no-op
inputs — addDebugTag/removeNeeded), not observable existence.

#### 5.3 `SectionOps.lean` flatness — DONE

Resolved by deletion.  An audit found the entire 530-LOC
preservation infrastructure had zero external callers:
`updateSectionContent_preserves_structural` plus its 8+ per-clause
helpers, the four `_of_updateSectionContent_of_ne` content-accessor
preservations, and the IsValid bundling helper.  The typed-section
algebra's `Fin ds.size` indexing made the infrastructure obsolete
by construction.  `SectionOps.lean` is now 51 LOC: just
`ElfFile.updateSectionContent` def + 3 actively-used `@[simp]`
projection lemmas.

---

## Out of scope (not on the roadmap)

- **Cross-endian / ELF32.** The port models little-endian ELF64 only.
- **Architecture-specific relocations.** The port doesn't handle
  architecture-specific dynamic relocation types.
- **Shared-object creation from relocatable objects.** The port
  operates on existing ELF files; it doesn't link.

---

## Architectural appendix

The byte-layer IR (`ElfFile`, `Section`, `SectionContent`), encode
pipeline, parse pipeline, and section-decoding dispatch are
documented in `lean/STATUS.md` §Architecture and §Encoder pipeline.
This appendix covers only the typed-section algebra, which `STATUS.md`
summarizes but doesn't expand.

### Typed-section algebra

```
ValidElfFile
├── header   : ElfHeader
├── phdrs    : Array ProgramHeader
├── dynstr   : StringSection
├── dynsym   : Option (SymbolSection dynstr)  -- indexed by dynstr
├── dynamic  : Option (DynamicSection dynstr) -- ditto
├── versym   : Option (Array UInt16)
├── verneed  : Option VerneedSection
├── sysvHash : Option SysVHashSection
├── gnuHash  : Option GnuHashSection
└── interp   : Option InterpSection

DynamicSection ds
├── needed   : Array (Fin ds.size)     -- DT_NEEDED offsets
├── rpath    : Option (Fin ds.size)    -- DT_RPATH
├── runpath  : Option (Fin ds.size)    -- DT_RUNPATH
├── soname   : Option (Fin ds.size)    -- DT_SONAME
├── flags1   : Option UInt64           -- DT_FLAGS_1 (not a strref)
├── debug    : Option UInt64           -- DT_DEBUG
└── unstructured : Array DynEntry      -- everything else (preserved verbatim)
```

Cross-section bounds invariants (e.g. "every DT_NEEDED value is
`< dynstr.size`") are type-level: `Fin ds.size` in every
string-ref field.  `rebase` lifts a `DynamicSection ds` to
`DynamicSection ds'` when `ds.size ≤ ds'.size` via
`Array.map Fin.castLE` — a numeric no-op that preserves the
typed offsets across `.dynstr` growth.

DT_STRTAB / DT_SYMTAB / DT_HASH / DT_GNU_HASH / DT_VERNEED /
DT_STRSZ are NOT stored.  They're derived at encode time via
`DynamicSection.assembleEntries` + a `LayoutCtx`.  The byte layer's
`dynStrszCoherent` and `dynAddressCoherentForTag × 5` clauses
vanish.
