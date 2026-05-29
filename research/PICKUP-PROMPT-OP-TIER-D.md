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
`removeNeeded`) as full byte round-trips.  What remains is the **per-op
fact discharge**: each op currently *takes its `eo` facts as
hypotheses* (validity + 6 structural input invariants + residual `< 2^64`
fit bounds); the next step is deriving them mechanically from the typed
op + template.

---

```
You are picking up ROADMAP §5.1 in the patchelf Lean 4 port: per-op fact
discharge for the 12 "Tier 2/3" mutating ops.  The three open-core
obligations are CLOSED and composed into a driver; the two shrinking ops
already round-trip.  Your job is to (a) discharge the per-op `eo` facts
from the typed op instead of taking them as hypotheses, and/or (b) clear
the two documented sub-obstacles so the residual-fit surface shrinks.

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

### Step 3 — the residual fit/validity fields (clear the sub-obstacles)

`identValid` / `sizeFit` / `nullEmpty` / `headerFit_entry` ARE derivable
through the pipeline (content/header preservation) — the blocker is a
robust `growEOFWith_sections_content` getElem-dispatch.  Two documented
sub-obstacles (see `-- TODO §5.1` in OpAdapterPreservation.lean):
  1. `cases hLast : lastPtLoadIdx e.phdrs` (needed to expose the layout
     branch) fails with "motive not type correct" when a
     `hj : j < (growEOFWith …).sections.size` hypothesis is in context.
  2. The projection dispatches (`growEOFWith_dynstr`, `_header_ident`)
     work because `cases hLast` SUBSTITUTES `lastPtLoadIdx`, after which
     the let-bound layout discriminants match the copy-pasted `hExt` form;
     a standalone branch-equation lemma can't reproduce that match (the
     `match pageSize?` aux function differs).
  Promising routes: (a) revert `hj` to a `∀`-binder before `cases hLast`
  (tried — `split` then over-splits the irrelevant `match pageSize?`,
  renaming `pageSize?`); (b) a `getElem`-transport helper keyed on a
  proven `growEOFWith pe = <branch>` equation closed by `subst` (the
  whole-ElfFile branch equation resisted `rfl` due to inlined-vs-call
  elaboration — investigate `Array.ext`/per-field instead); (c) prove
  `sizeFit`/`nullEmpty` from `eo`'s versions + the per-branch
  `_sections_content` lemmas threaded through `syncDtStrszInFile`'s
  `_sections_encodedSize`.  Once `growEOFWith_sections_content` lands,
  `sizeFit` follows (shdrSize is content-determined) and `nullEmpty` /
  `identValid` follow similarly; shrink `encodePreconditions_of_layoutNormalized`'s
  hypothesis list accordingly.  The position bounds (`headerFit_phoff/shoff`,
  `phdrFit`, `shdrFit` addr/offset) STAY hypotheses — genuinely
  non-derivable; keep the "file < 2^64" precondition.

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
   precondition is fine).
3. Ideally: Step 3 sub-obstacle cleared (`growEOFWith_sections_content`)
   so `sizeFit`/`nullEmpty`/`identValid` are derived, shrinking the
   residual hypothesis surface.
4. STATUS.md + ROADMAP.md updated; refresh this pickup prompt.

## Output

Small focused commits in the existing style (`git log --oneline -15`).
`#print axioms` on the headline op theorem should show only
`[propext, Classical.choice, Quot.sound]` plus the 3 `bv_decide`
readU/writeU axioms — no `sorryAx`.
```

---

## Notes for the human (not the agent)

This session closed the substantive open core (Obligations A/B/C) and
shipped the composed `tierD_roundtrip` driver + full round-trips for the
two shrinking ops, with the position/size `< 2^64` bounds taken as the
sanctioned explicit precondition.  What's left is honest plumbing: each
op still *assumes* its `eo` validity + structural invariants + residual
fits rather than *deriving* them from the typed op.  For shrinking ops
this is parser-derivable transport; the residual-fit derivation is gated
on a `growEOFWith_sections_content` getElem-dispatch that hit a genuine
Lean dependent-motive wall (documented as `-- TODO §5.1`), so it was
deferred rather than rushed.
