# Pickup prompt: ROADMAP §5.1 — op-level Tier D for the Tier 2/3 ops

Single-shot handoff for a fresh agent with shell access, the Lean
build environment, and repo read access, but no other context.  Paste
the fenced block below into that agent.

The §1.1 (parser establishes `IsLoadable`) and §1.2
(`growEOFWith_preserves_loadable`, lifted end-to-end to
`prepLayout_syncDtStrsz_preserves_loadable`) ladders are fully closed.
The `Adapter.toElfFile` dependent-type obstacle that blocked §5.1 is
resolved (un-bundling refactor).  Tier-1 ops (`setOsAbi`,
`modifyExecstack`) have full `_preserves_loadable`.  A reusable Tier-D
scaffold is in place.  What remains is the substantive open core: the
residual encode-precondition obligations on the *normalized* form, for
the 12 Tier-2/3 ops.

---

```
You are picking up ROADMAP §5.1 in the patchelf Lean 4 port:
op-level Tier D (byte round-trip) for the 12 "Tier 2/3" mutating ops.
The dependent-type obstacle is already resolved, Tier-1 ops are done,
and a reusable scaffold exists.  Your job is to close the remaining
"open core" obligations and apply them to the Tier 2/3 ops.

## First reads, in this order

1. `/home/cbaker2/ext-sources/patchelf/lean/STATUS.md` — top banner +
   "Invariants and theorems".
2. `/home/cbaker2/ext-sources/patchelf/research/ROADMAP.md` §5.1 — the
   tier map and the precise list of remaining obligations.
3. `/home/cbaker2/ext-sources/patchelf/lean/Patchelf/Elf/OpAdapterPreservation.lean`
   — the whole file.  This is your home base: the Tier-1 worked
   examples, the reusable `isValid_of_phdrs_map` /
   `isLoadable_of_phdrs_map` helpers, and the Tier-2/3 scaffold
   (`encode_roundtrip_via_normalized`, `spliceRegionsDisjoint_of_structural`).
4. `/home/cbaker2/ext-sources/patchelf/lean/Patchelf/Elf/ByteRoundtrip.lean`
   — `EncodePreconditions` (line ~1907), `parse_encode_roundtrip`
   (~2022), `encodePreconditions_of_parser` (~2535), and
   `syncDtStrszInFile_eq_id` (~2257).  These define the obligations.
5. `/home/cbaker2/ext-sources/patchelf/lean/Patchelf/Elf/Encoder.lean`
   — `syncDtStrszInFile` (~98), `prepLayoutForEncodeWith`/`encode`
   (~496/513), `encode_eq` (~766), the §1.2 pipeline loadable theorems
   (~848-920), and the `syncDtStrszInFile_*` accessor family (~553+).

## Working directory and environment

    cd /home/cbaker2/ext-sources/patchelf/lean
    nix develop ..#lean -c lake build              # baseline; expect 109 jobs clean
    nix develop ..#lean -c bash tests/run.sh       # 54/54 shell tests
    grep -rnE "(:= *sorry|by *sorry| sorry$)" Patchelf/   # zero; keep it

`lake build` from cold is a few minutes — set a generous timeout.
Develop new lemmas in a scratch file (`Patchelf/Scratch.lean`) that
`import`s the relevant module for a fast feedback loop, then transplant
into the real file.  DELETE the scratch file before committing.

## The core problem (read carefully — it's subtle)

A mutating op runs in the typed layer; `Adapter.toElfFile template
(op typed)` maps it back to a byte-layer `ElfFile`.  Call that `eo`.

KEY FACT: for all ops except `setOsAbi`/`modifyExecstack`, `eo` is NOT
laid out.  `patchDynamicEntries` (the positional `.dynamic` rebuilder
in `Adapter.lean`) changes the byte-level entry count — its trailing
`unless flags1Applied` / `unless debugApplied` / NEEDED-append blocks
can ADD entries (so even `noDefaultLib`/`addDebugTag` grow `.dynamic`),
and `removeRpath`/`removeNeeded` DROP entries.  Either way the
`.dynamic` section's `encodedSize` changes, so downstream section
offsets no longer match and `eo.spliceRegionsDisjoint` is FALSE.

Therefore `parse_encode_roundtrip` (which needs the encoded file to be
already laid out + DT_STRSZ-coherent) does NOT apply to `eo` directly.

What DOES round-trip is the encoder's normalized form
`en := prepLayoutForEncode (syncDtStrszInFile eo)` — the structure
`encodeBody` actually serializes (`encode_eq : encode e = encodeBody
(prepLayoutForEncode (syncDtStrszInFile e))`).  `encode`'s own
`growEOFWith` pass re-lays-out the grown file.

The scaffold `Adapter.encode_roundtrip_via_normalized` already reduces
the per-op round-trip
    `parse (encode eo) = .ok ⟨en, hValEn⟩`
to three obligations on `en`:
  (1) `hValEn : en.IsValid`
  (2) `hPreEn : EncodePreconditions en`
  (3) `hIdem  : encode eo = encode en`     (pre-pass idempotence)

## What to build (the open core), in dependency order

### Obligation A — `dynStrszCoherent` establishment + preservation (→ `syncOk`)

`EncodePreconditions.syncOk` is `syncDtStrszInFile en = en`, which
`syncDtStrszInFile_eq_id` derives from `en.dynStrszCoherent`.  So prove
`en.dynStrszCoherent`.  Sub-lemmas (none exist yet):

* `syncDtStrszInFile_establishes_dynStrszCoherent (e) :
  (syncDtStrszInFile e).dynStrszCoherent` — `syncDtStrszInFile` rewrites
  every DT_STRSZ entry's value to `.dynstr.bytes.size`, so its output
  is coherent by construction.  Watch the no-op branches (no `.dynamic`
  or no `.dynstr` → `dynStrszCoherent` holds vacuously).
* `prepLayoutForEncode_preserves_dynStrszCoherent` — `growEOFWith` and
  `syncDtAddrTagsInFile` must not disturb DT_STRSZ.  `syncDtAddrTagsInFile`
  only touches address tags (`syncDtAddrEntry`), and `growEOFWith` only
  moves sections / rewrites offsets, not `.dynamic` *values* except via
  `syncDtAddrTagsInFile`.  Reuse the `syncDtAddrEntry_tag` /
  `_dynamic`-content lemmas in `GrowEOF.lean`.
  CAUTION: `growEOFWith` can change `.dynstr` offset but `dynStrszCoherent`
  compares against `.dynstr.bytes.size` (the byte length), which is
  layout-invariant — confirm this.

### Obligation B — pre-pass idempotence (→ `hIdem`)

`encode eo = encode en` where `en = prepLayoutForEncode (syncDtStrszInFile
eo)`.  Via `encode_eq` twice, this reduces to
    `prepLayoutForEncode (syncDtStrszInFile en) = en`
i.e. re-normalizing `en` is a no-op.  Two parts:
* `syncDtStrszInFile en = en` — that's `syncOk` (Obligation A).
* `prepLayoutForEncode en = en` — `prepLayoutForEncodeWith` is identity
  when `layoutAlreadyValid en = true`
  (`prepLayoutForEncode_of_layoutAlreadyValid`), and
  `layoutAlreadyValid_of_spliceRegionsDisjoint` derives that from
  `en.spliceRegionsDisjoint`, which you get from
  `spliceRegionsDisjoint_of_structural` (already landed) — BUT only
  after `syncDtStrszInFile en = en` lets you equate `en` with
  `prepLayoutForEncode (syncDtStrszInFile en)`.  Mind the ordering;
  this is slightly circular-looking but unfolds cleanly once
  `dynStrszCoherent en` is in hand.

### Obligation C — residual `EncodePreconditions` fields on `en`

`identValid`, `sizeFit`, `nullEmpty`, `headerFit_*`, `phdrFit`,
`shdrFit`.  These are NOT parser-derivable (`en` is an encoder output).
Most are structural and should follow from the §1.2 accessor-
preservation lemmas already in `GrowEOF.lean`/`Encoder.lean`:
* `identValid` — ident bytes come from `header.ident`, preserved by the
  whole pipeline (header is preserved except shoff/phoff/phnum).
* `nullEmpty` / `sizeFit` / `shdrFit` — per-section; `growEOFWith` only
  appends `roundUp`-bounded regions and preserves per-section
  type/content (hence `encodedSize`/`shdrSize`).  The `< UInt64.size`
  bounds need the file to stay under 2^64 — reasonable to take as an
  explicit hypothesis on the op input if it can't be derived.
* `headerFit_*` / `phdrFit` — header/phdr wrap_nat fields; `growEOFWith`
  sets shoff/phoff via `roundUp` and bumps phnum — bound these.

Consider packaging C as a single lemma
`encodePreconditions_of_layoutNormalized (e) (… structural hyps …) :
EncodePreconditions (prepLayoutForEncode (syncDtStrszInFile e))` that
composes A + B + C, so each op just supplies the structural hyps.

### Then: apply to the 12 ops

For each Tier 2/3 op, prove its `toElfFile` output satisfies the 5
structural input invariants (`headerPhdrDisjoint`, `headerShdrDisjoint`,
`phdrShdrDisjoint`, `headerSectionDisjoint`, `phdrSectionDisjoint`) +
`hSection0Null` on `syncDtStrszInFile eo`.  These ARE parser-derivable
for ops that don't widen the file past `currentFileEnd` (the op only
rewrites existing section content + maybe grows `.dynstr`/`.dynamic`
within the existing layout, which `growEOFWith` then relocates).  Feed
them to `spliceRegionsDisjoint_of_structural` + the Obligation-C
package + the scaffold.

Op list (all in `Patchelf/Elf/Ops/`): `noDefaultLib`, `addDebugTag`,
`removeRpath`, `removeNeeded`, `clearSymbolVersion`, `addNeeded`,
`modifyRPath`, `addRpathEntry`, `modifySoname`, `setInterpreter`,
`replaceNeeded`, `renameDynamicSymbols`.  Start with a SHRINKING op
(`removeRpath` or `removeNeeded`) — smaller `.dynamic`, no dynstr
growth, simplest structural-invariant story.

## Tactics / gotchas (learned the hard way)

- DEPENDENT MOTIVE: `rw [hEq] at hj ⊢` fails ("motive is not type
  correct") when `hj`/the goal carry a length bound depending on the
  rewritten term.  Use `simp only [hEq] at hj ⊢` instead — it handles
  the dependent bound.  Same family: `subst` an index/option witness
  rather than `rw`-ing it (see the §1.2 `updatePhdrsAfterMove_*`
  proofs and the `lean-subst-not-rw-dependent-motive` memory).
- SCRATCH vs IN-FILE: a `simp only [hCond, ↓reduceIte]` `if`-cascade
  reduction may fire in the real file but NOT in a standalone scratch
  importing the olean (different match-discriminant elaboration).
  Develop sub-lemmas in scratch; transplant dispatch-shaped proofs into
  the file before judging them.
- The Tier-1 pattern (`OpAdapterPreservation.lean`): a
  `toElfFile_<op>_eq` commutation lemma by `rfl` (enabled by the
  un-bundled `toElfFile`), then transport.  Tier 2/3 ops will NOT
  commute by `rfl` (sections change), so they go through the
  `encode_roundtrip_via_normalized` scaffold instead.

## Hard constraints

- No `sorry`s, even temporarily.  If blocked, document the obstacle as
  `-- TODO §5.1: <what you tried, what failed>` and stop with a writeup.
- Don't weaken or delete any existing theorem/test.  109 lake jobs must
  build; 54 shell tests must pass.
- Don't re-introduce the `toElfFile` bundling (it would re-block Tier 1).
- Keep `Adapter.toElfFile`'s outer `{ e with header := …, phdrs := … }`
  shape — `toElfFile_header`/`_phdrs` are `rfl` and load-bearing.

## Success criteria

1. `lake build` clean, zero `sorry`s; 54/54 shell tests.
2. Obligations A + B + C closed (or the genuinely-blocked ones
   documented with a precise writeup).
3. At least the shrinking ops (`removeRpath`, `removeNeeded`) have a
   full `parse (encode (toElfFile … (op typed))) = .ok ⟨en, _⟩`
   round-trip via the scaffold.  Ideally all 12.
4. STATUS.md + ROADMAP.md updated; replace/refresh this pickup prompt.

## Output

Small focused commits in the existing style (`git log --oneline -15`):
ideally one per obligation (A, B, C) then one per op (or per op
cluster).  Each commit names what landed + file paths.  `#print axioms`
on the headline theorem should show only `[propext, Classical.choice,
Quot.sound]` plus the 4 `bv_decide` readU/writeU axioms — no `sorryAx`.
```

---

## Notes for the human (not the agent)

Why this is the honest state and not "all 14 ops done": only `setOsAbi`
and `modifyExecstack` leave byte-level section positions fixed.  The
other 12 grow/shrink the `.dynamic` section, so their adapter output
isn't laid out and the meaningful guarantee is the full Tier-D
round-trip through `growEOFWith` — which needs the normalized-form
`EncodePreconditions` builder that doesn't exist yet (Obligations A–C).
That's a real multi-lemma sub-project, deliberately deferred rather
than rushed.

If the agent reports Obligation C's `< UInt64.size` bounds as
underivable, the right intervention is to add an explicit
"file stays under 2^64" precondition on the op input — every real ELF
satisfies it, and the runtime validator (`Validate.IsLoadableBytes`)
already guards the pathological case at write time.
