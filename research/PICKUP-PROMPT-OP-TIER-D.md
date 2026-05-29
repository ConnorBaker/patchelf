# Pickup prompt: ROADMAP §5.1 — per-op fact discharge for the Tier 2/3 ops

Single-shot handoff for a fresh agent with shell access, the Lean build
environment, and repo read access, but no other context.  Paste the
fenced block below into that agent.

The §1.1 / §1.2 ladders are fully closed.  The `Adapter.toElfFile`
dependent-type obstacle is resolved.  Tier-1 ops have full
`_preserves_loadable`.  **The three §5.1 "open core" obligations
(A `syncOk`, B `hIdem`, C residual `EncodePreconditions`) are now
CLOSED**, composed into the `tierD_roundtrip` / `tierD_roundtrip_of_valid`
driver, and applied to the two shrinking ops (`removeRpath`,
`removeNeeded`) as full byte round-trips.  Obligation C now DERIVES
`identValid`/`sizeFit`/`nullEmpty`/`headerFit_entry` (the
content-preservation getElem-dispatch wall is CRACKED); only the 4
position-bound families remain hypotheses.  What remains is the **per-op
fact discharge**: each op currently *takes its `eo` facts as hypotheses*
(validity + 6 structural input invariants + the 4 residual `< 2^64`
position bounds); the next step is deriving the validity + structural
invariants mechanically from the typed op + template.

---

```
You are picking up ROADMAP §5.1 in the patchelf Lean 4 port: per-op fact
discharge for the 12 "Tier 2/3" mutating ops.  The three open-core
obligations are CLOSED and composed into a driver; Obligation C derives
all four in-principle-derivable residual fields; the two shrinking ops
already round-trip.  Your job is to discharge the per-op `eo` facts
(validity + 6 structural input invariants) from the typed op + template
instead of taking them as hypotheses.

## First reads, in this order

1. `/home/cbaker2/ext-sources/patchelf/lean/STATUS.md` — top banner +
   the "Op-level Tier D — open core CLOSED" bullet under "Known gaps".
2. `/home/cbaker2/ext-sources/patchelf/research/ROADMAP.md` §5.1 — the
   obligation breakdown + "Remaining per-op work" + the two `-- TODO §5.1`
   sub-obstacles.
3. `/home/cbaker2/ext-sources/patchelf/lean/Patchelf/Elf/OpAdapterPreservation.lean`
   — the WHOLE file.  Home base.  Read in order:
     * Tier-1 worked examples (`toElfFile_setOsAbi_*`, `_modifyExecstack_*`).
     * `encode_roundtrip_via_normalized` + `spliceRegionsDisjoint_of_structural`
       (the scaffold).
     * `encodePreconditions_of_layoutNormalized` (Obligation C package —
       read its docstring + the `-- TODO §5.1` block carefully).
     * `tierD_roundtrip` / `tierD_roundtrip_of_valid` (the composed drivers).
     * `toElfFile_{removeRpath,removeNeeded}_tierD_roundtrip` (worked
       examples — note what they take as HYPOTHESES; that is your work).
4. `/home/cbaker2/ext-sources/patchelf/lean/Patchelf/Elf/Encoder.lean`
   — Obligation A establishment (`syncDtStrszInFile_establishes_dynStrszCoherent`,
   `~683`), preservation (`prepLayoutForEncode_preserves_dynStrszCoherent`,
   `prepLayout_syncDtStrsz_dynStrszCoherent`), Obligation B helpers
   (`prepLayoutForEncode_{dynstr,eq_self_of_spliceRegionsDisjoint}`), and
   the validity capstone (`prepLayout_syncDtStrsz_preserves_valid`).
5. `/home/cbaker2/ext-sources/patchelf/lean/Patchelf/Elf/GrowEOF.lean`
   — the accessor families you'll compose: `growEOFWith_{dynamic,dynstr,
   sections_size,header_ident,header_entry}` (top-level dispatch),
   `syncDtAddrTagsInFile_{dynamic_eq,dynstr,preserves_dynStrszCoherent}`,
   per-branch `_sections_{content,type,addralign,entsize}` for all 4
   layout branches.
6. `/home/cbaker2/ext-sources/patchelf/lean/Patchelf/Elf/Adapter.lean`
   `toElfFile` (`~372`) — how `eo = toElfFile template (op typed)` is
   built (apply section edits to template, then set header/phdrs from
   typed).

## Working directory and environment

    cd /home/cbaker2/ext-sources/patchelf/lean
    nix develop ..#lean -c lake build              # baseline; expect 109 jobs clean
    nix develop ..#lean -c bash tests/run.sh       # 54/54 shell tests
    grep -rnE "(:= *sorry|by *sorry| sorry$)" Patchelf/   # zero; keep it

`lake build` from cold is a few minutes — set a generous timeout.
Develop new lemmas in a scratch file (`Patchelf/Scratch.lean`) that
`import`s the relevant module for a fast feedback loop, then transplant
into the real file.  DELETE the scratch file before committing.

## What the driver gives you, and what each op still owes

`tierD_roundtrip_of_valid eo hVal hPhdrFit hDs hFit hPreEn` produces the
full round-trip `parse (encode eo) = .ok ⟨prepLayoutForEncode
(syncDtStrszInFile eo), _⟩`.  The arguments an op must supply about its
byte output `eo := toElfFile template (op typed)`:

  * `hVal  : eo.IsValid`
  * `hPhdrFit : (eo.phdrs.size + 1) < UInt16.size`  (trivial — real phnum
    is already a UInt16; `eo.phdrs = typed.phdrs` by `toElfFile_phdrs`)
  * `hDs   : eo.dynstr = some ds`,  `hFit : ds.bytes.size < UInt64.size`
  * `hPreEn : EncodePreconditions (prepLayoutForEncode (syncDtStrszInFile eo))`
    — build via `encodePreconditions_of_layoutNormalized`, which itself
    wants the 6 structural input invariants on `syncDtStrszInFile eo`
    (`hS0`/`hHP`/`hHS`/`hPS`/`hHSec`/`hPSec`) + the 8 residual fit fields.

The shrinking-op theorems take all of these as hypotheses.  YOUR JOB is
to replace them with derivations from the typed op + template.

## Recommended attack order

### Step 1 — `hVal`, `hPhdrFit`, `hDs`, `hFit` (cheap, do first)

These are the easy four.  `toElfFile_phdrs`/`_header` are `rfl`, so
`eo.phdrs = typed.phdrs` and `hPhdrFit` is `typed`'s phnum bound (a
`UInt16`, so `.size + 1 < UInt16.size` follows from `phnum.toNat =
phdrs.size` in `headerCountsConsistent` if you carry it, or just take it
— it is genuinely about the typed file, not the layout).  `eo.IsValid`:
the typed algebra guarantees the structural invariants; look at whether
`toElfFile`'s output already has an `IsValid` witness or build one from
`ValidElfFile`'s fields + the `AdapterRoundtrip` theorems.  `eo.dynstr`:
trace `toElfFile`'s `applyDynstr` — `eo.dynstr = some typed.dynstr` (or
the grown dynstr); `hFit` is the "file < 2^64" precondition on the op
input (add it explicitly if not derivable).

### Step 2 — the 6 structural input invariants (the substance)

`headerPhdrDisjoint` / `headerShdrDisjoint` / `phdrShdrDisjoint` /
`headerSectionDisjoint` / `phdrSectionDisjoint` + `hSection0Null` on
`syncDtStrszInFile eo`.  `syncDtStrszInFile` preserves all of these
(accessor lemmas exist: `syncDtStrszInFile_{header,phdrs,sections_*,
section0Null,headerPhdrDisjoint,headerSectionDisjoint,phdrSectionDisjoint}`
in Encoder.lean — note `headerShdrDisjoint`/`phdrShdrDisjoint` may need
new ones), so reduce to the invariants on `eo`.  For a SHRINKING op
(`removeRpath`/`removeNeeded`): `eo`'s `.dynamic` is smaller, every other
section keeps its offset/size, and the file does not widen past
`currentFileEnd` — so these transport from the template's invariants
(parser-derivable: a freshly-parsed ELF that `parseLoadable` accepted
satisfies them).  This is the per-op `_produces_spliceRegionsDisjoint`
the ROADMAP describes.  Start here with `removeRpath`.

### Step 3 — residual fields (ALREADY DONE; the 4 position bounds stay)

`identValid` / `sizeFit` / `nullEmpty` / `headerFit_entry` are now DERIVED
by `encodePreconditions_of_layoutNormalized` from the matching facts on
`eo` (`{identValid,sizeFit,nullEmpty,headerFit_entry}_normalized_of_eo`,
`ByteRoundtrip.lean`).  The getElem-dispatch wall that previously blocked
this is cracked: `growEOFWith_sections_content` (and `_shdrSize`/`_type`)
are derived from the bound-free `growEOFWith_sections_map_content`
(`map (·.content)`) equation — proved by `rw [growEOFWith.eq_1]; cases
pageSize?` (kills the `match pageSize?` entanglement) `; simp only []`
(zeta-reduces the `have`s) `; repeat' split; all_goals first | rfl |
exact <branch>`.  The `prepLayout_syncDtStrsz_sections_{shdrSize,type}` +
`_header_{ident,entry}` pipeline lemmas thread these through both
pre-encode passes (via the `prepLayoutForEncode e = syncDtAddrTagsInFile
(growEOFWith none e)` rewrite-the-getElem-term idiom).  The 4 position
bounds (`headerFit_phoff/shoff`, `phdrFit`, `shdrFit`) STAY hypotheses —
genuinely non-derivable; keep the "file < 2^64" precondition.  So an op no
longer supplies any residual `en` facts — it supplies `eo.IsValid`,
`eo`-level `identValid`/`sizeFit`/`nullEmpty`/`headerFit_entry`, the dynstr
witness, the 6 structural invariants, and the 4 `en` position bounds.

### Then: the other 10 ops

`noDefaultLib`, `addDebugTag`, `clearSymbolVersion`, `addNeeded`,
`modifyRPath`, `addRpathEntry`, `modifySoname`, `setInterpreter`,
`replaceNeeded`, `renameDynamicSymbols`.  Growing ops (dynstr/`.dynamic`
append) need the per-op `growEOFWith` layout reasoning for Step 2; the
§1.2 `updatePhdrsAfterMove_*` / `retargetPtPhdr_*` families are reusable.

## Tactics / gotchas (learned the hard way)

- DEPENDENT MOTIVE: `cases`/`rw`/`unfold … at hj` fails ("motive is not
  type correct") when `hj` carries a length bound depending on the
  rewritten term.  For projection dispatches, do the `by_cases hLay`/
  `cases hLast`/`by_cases hExt`/`by_cases hAdd` ladder WITHOUT a
  dependent `hj` in context (see `growEOFWith_dynstr`).  See the
  `lean-subst-not-rw-dependent-motive` memory.
- DISPATCH LEAF CLOSER: a layout-branch leaf is sometimes closed by
  `simp only [hExt, …, ↓reduceIte]` alone (structure-projection reduces
  to `rfl`) and sometimes needs the per-branch lemma.  Use
  `simp only [...] <;> first | rfl | exact <branch_lemma> …` — the `<;>`
  applies the closer to 0-or-1 resulting goals, tolerating both.
- SCRATCH vs IN-FILE: dispatch-shaped `simp only [hCond, ↓reduceIte]`
  cascades fire in the real file but NOT in a standalone scratch
  importing the olean.  Develop sub-lemmas in scratch; transplant
  dispatch-shaped proofs into the file before judging them.

## Hard constraints

- No `sorry`s, even temporarily.  If blocked, document as
  `-- TODO §5.1: <what you tried, what failed>` and stop with a writeup.
- Don't weaken or delete any existing theorem/test.  109 lake jobs must
  build; 54 shell tests must pass.
- Don't re-introduce the `toElfFile` bundling.
- Keep `Adapter.toElfFile`'s outer `{ e with header := …, phdrs := … }`
  shape — `toElfFile_header`/`_phdrs` are `rfl` and load-bearing.

## Success criteria

1. `lake build` clean, zero `sorry`s; 54/54 shell tests.
2. At least one shrinking op (`removeRpath` or `removeNeeded`) has its
   per-op `eo` structural invariants (Step 2) DERIVED rather than
   hypothesized, closing the gap between `tierD_roundtrip_of_valid`'s
   `hPreEn` and a genuine self-contained `parse (encode (toElfFile …)) =
   .ok …` with no structural-invariant hypotheses (a "file < 2^64"
   precondition on the 4 position bounds is fine).
3. STATUS.md + ROADMAP.md updated; refresh this pickup prompt.

(Step 3's residual-field derivation — `sizeFit`/`nullEmpty`/`identValid`/
`headerFit_entry` — is already DONE; the getElem-dispatch wall is cracked.)

## Output

Small focused commits in the existing style (`git log --oneline -15`).
`#print axioms` on the headline op theorem should show only
`[propext, Classical.choice, Quot.sound]` plus the 3 `bv_decide`
readU/writeU axioms — no `sorryAx`.
```

---

## Notes for the human (not the agent)

Two sessions closed the substantive open core (Obligations A/B/C),
cracked the `growEOFWith` content-preservation getElem-dispatch (the
dependent-motive wall — solved with a bound-free `map (·.content)`
equation + `cases pageSize?`), and DERIVED four of the eight residual
`EncodePreconditions` fields (`identValid`/`sizeFit`/`nullEmpty`/
`headerFit_entry`) on the normalized form.  The composed `tierD_roundtrip`
driver + full round-trips for the two shrinking ops are in place, with
only the 4 position-bound families (`headerFit_phoff`/`shoff`, `phdrFit`,
`shdrFit`) taken as the sanctioned "file < 2^64" precondition.  What's
left is honest plumbing: each op still *assumes* its `eo` validity +
structural invariants rather than *deriving* them from the typed op.  For
shrinking ops this is parser-derivable transport; for growing ops it needs
the per-op `growEOFWith` layout reasoning.  Deferred rather than rushed.
