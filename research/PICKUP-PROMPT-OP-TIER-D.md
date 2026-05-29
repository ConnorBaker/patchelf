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
    nix develop ..#lean -c lake build              # baseline; expect 109 jobs clean
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
- Don't weaken or delete any existing theorem/test.  109 lake jobs must
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
taking them as hypotheses.  Start with `removeRpath` (simplest shrinking op).

### Tier-D readers (after orientation)

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
   the template's parser-derived invariants — IF you supply two op-specific
   lemmas:

   (a) **`patchDynamicEntries` output-size bound**:
       `(patchDynamicEntries byteDyn (stripRpath/filterNeededBy … typed)).size
       ≤ byteDyn.size`.  The LOOP portion is de-risked: `idForIn_proj_size_le`
       bridges the `Id.run do … forIn` loop to a `≤ (π result).size +
       byteDyn.size` bound given a per-step ≤1-growth on the `result`
       projection (a finite `match d.tag` case-split — every arm pushes ≤1).
       WHAT REMAINS: bound the trailing `while` + 5 `unless` append blocks in
       the desugared do-block (brittle `__do_jp` navigation — consider
       refactoring `patchDynamicEntries` to expose loop + appends
       compositionally, or `mvcgen`), and for the TIGHT `≤ byteDyn.size` use
       the NEEDED-balance (`typed.needed.size = #DT_NEEDED in byteDyn`, from
       the `ofElfFile`/parse relationship — so the `while` adds 0).
       `Ops/RemoveNeeded.lean`'s `removeNeeded_needed_size_le` (via
       `Array.size_filter_le`) is the typed side.

   (b) **factor `eo = toElfFile template (op typed)` as
       `base.updateSectionContent iDyn (.dynamic newDyn)`** with `newDyn =
       patchDynamicEntries (template.dynamic) (op typed).dynamic` and `base`'s
       other sections verbatim from `template`, so the shrink lemmas apply.
       `toElfFile` is a chain of `applyX` `updateSectionContent`s; for a
       shrinking op only `applyDynamic` changes a size-relevant section
       (`applyDynstr` rewrites `.dynstr` but `removeRpath` doesn't grow it).

   GROWING ops (`addNeeded`, `addRpathEntry`, `modifyRPath.set`,
   `modifySoname.set`, `setInterpreter`, `replaceNeeded` grow path,
   `renameDynamicSymbols`, and even `noDefaultLib`/`addDebugTag` which can
   APPEND a DT_FLAGS_1/DT_DEBUG entry) widen `.dynamic`/`.dynstr`, so the
   shrink lemmas don't apply — they need per-op `growEOFWith` layout
   reasoning (the §1.2 `updatePhdrsAfterMove_*` / `retargetPtPhdr_*`
   families are reusable).  Do these AFTER the shrinking ops.

### §5.1 success criteria

1. `lake build` clean, zero `sorry`s; 54/54 shell tests.
2. At least one shrinking op (`removeRpath`/`removeNeeded`) has its `eo`
   structural invariants DERIVED rather than hypothesized — i.e. a
   `parse (encode (toElfFile …)) = .ok …` with no structural-invariant
   hypotheses (a "file < 2^64" precondition on the 4 position bounds is OK).
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
(e.g. `noDefaultLib` ⇒ `flags1` has the DF_1_NODELETE-ish bit set;
`modifyRPath.set` ⇒ `rpath = some <the new offset>`).  Files: `Elf/Ops/*.lean`.

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
landed; the full `eo`-level driver `tierD_roundtrip_of_eo_facts` is in
place; the two shrinking ops round-trip (taking their `eo` facts as
hypotheses).  The only genuinely open §5.1 piece is the per-op DISCHARGE of
those `eo` facts — concretely two lemmas for a shrinking op: a
`patchDynamicEntries` output-size bound (loop de-risked; trailing
`while`/`unless` join-point navigation + the NEEDED-balance remain) and the
`toElfFile`-as-single-`updateSectionContent` factoring.  Deferred rather
than rushed, because the desugared-`do` join-point navigation is brittle and
warrants either a `patchDynamicEntries` refactor or `mvcgen`.
