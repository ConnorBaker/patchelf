# Pickup prompt: ROADMAP §3.5a fresh PT_LOAD allocation

Single-shot agent prompt for picking up the fresh PT_LOAD allocation
work in the patchelf Lean 4 port (ROADMAP §3.5a).  Paste the
fenced block below into a fresh agent that has shell access, build
environment, and read access to the repo, but no other context.

The design doc this prompt references
([`REWRITE-FRESH-PT-LOAD-DESIGN.md`](REWRITE-FRESH-PT-LOAD-DESIGN.md))
is the spec; this file is just the prompt that points an agent at it
with the right framing and guardrails.

---

```
You are picking up ROADMAP §3.5a in the patchelf Lean 4 port: implementing
fresh PT_LOAD allocation for binaries where `growEOFWith`'s "extend the last
PT_LOAD" strategy is unsafe (the BSS-heavy binary class — e.g. coreutils
`ls`, ~0x97000 bytes of BSS).  Today these binaries fall back to
`layoutForEncoding`'s unaware repack and the pre-write validator catches
the resulting non-loadable bytes (exit 5).  Your job is to add a fourth
branch that allocates a brand-new PT_LOAD covering the moved sections.

## First reads, in this order

1. `/home/cbaker2/ext-sources/patchelf/lean/STATUS.md` — current state of
   the Lean port (top banner, "What works end-to-end", "Priority 3 gaps").
2. `/home/cbaker2/ext-sources/patchelf/research/ROADMAP.md` — read
   "Picking up work" and §3.5a in detail.
3. `/home/cbaker2/ext-sources/patchelf/research/REWRITE-FRESH-PT-LOAD-DESIGN.md`
   — this is your spec.  Read in full.  The "Pickup checklist" at the
   bottom is your task list.

Existing precedent to mirror: `growEOFWithMainBody` in
`Patchelf/Elf/GrowEOF.lean:896` and its proof
`growEOFWithMainBody_produces_spliceRegionsDisjoint` at line 934.  Your
new code is structurally analogous — same `PlaceFold` scaffolding from
`Patchelf/Elf/LayoutEngine.lean`, different placement strategy.

## Working directory and environment

    cd /home/cbaker2/ext-sources/patchelf/lean
    nix develop ..#lean -c lake build              # baseline must be clean
    nix develop ..#lean -c bash tests/run.sh       # 52/52 shell tests
    grep -rn "sorry\b" Patchelf/                   # zero matches; keep it

`lake build` from cold is a few minutes — set a generous timeout.

## Scope for this session

In-place sub-case ONLY.  The phdr table stays at its original location;
the new PT_LOAD covers the moved sections at file end.  This works
when there is room for one more phdr entry in the existing phdr-bearing
region.

The harder `relocatePht` sub-case (phdr table itself moves to file end)
is documented in the design doc but is a FOLLOW-UP.  When your new
`canAddFreshPtLoad` predicate fails, fall through to `layoutForEncoding`
exactly as the existing code does — that path will continue to be caught
by the validator, no regression.

## Success criteria

1. `lake build` clean, zero `sorry`s.
2. All 52 existing shell tests pass; do not weaken any of them.
3. A new shell test (`tests/cases/53-cli-set-rpath-bss-heavy.sh` or
   similar) that copies `/tmp/lean-pe-fixtures/ls`, runs `set-rpath /a`
   on it, observes exit 0, reparses the output, and runs the binary
   (it should print its usual `ls` help or list a directory).  Skip
   gracefully (exit 77) if the fixture isn't present.
4. `growEOFWithFreshPtLoad_produces_spliceRegionsDisjoint` proved end
   to end.  Compose with `prepLayoutForEncodeWith_produces_spliceRegionsDisjoint`
   so the existing op-level chain still works.

## Hard constraints

- Don't refactor unrelated code.  This is additive surgery.
- Don't disable or skip the byte roundtrip proof in `ByteRoundtrip.lean`.
  If your changes break it, you've leaked into the wrong layer — back
  up and consult the design doc.
- Don't add `sorry`s, even temporarily.  If a proof obstacle blocks you,
  stop and write up what you tried.  See "If you get stuck" below.
- Don't skip the validator with `--no-validate` to make a test pass —
  that defeats the point.
- Use existing infrastructure: `PlaceFold.{placeStep, placeFold,
  Placement, PairDisjoint, FoldInv}` in `LayoutEngine.lean` already
  handles the foldStep + Placement + PairDisjoint pattern.  Mirror
  the structure of `growEOFWithMainBody_produces_spliceRegionsDisjoint`
  (which is itself a parallel of `layoutForEncoding_produces_spliceRegionsDisjoint`).

## If you get stuck

- Document the obstacle inline as `-- TODO §3.5a: <what you tried, what
  failed>` and stop.
- Save partial progress in a commit (don't push unless asked).
- Hand back a status summary covering: which layers landed, where you
  hit the obstacle, what you'd try next.

The design doc has a "Why this isn't shipping now" note about §1.1 /
§1.2 dependencies.  Those are about the proof chain integrating cleanly
with parser-derived input invariants; for the IMPLEMENTATION you can
ignore them.  For the PROOF, if you find that the bridge to existing
spliceRegionsDisjoint preconditions is awkward without §1.1, document
that and stop — don't try to do §1.1 at the same time.

## Output

Commits in the existing style (see `git log --oneline -10`).  Each
commit message names what landed, which ROADMAP §, which file paths
changed, which tests added.  Small focused commits over one big one.
At the end, update STATUS.md and ROADMAP.md so §3.5a's status reflects
what landed.
```
