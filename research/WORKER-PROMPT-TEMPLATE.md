# Worker Prompt Template

> **ARCHIVED — workflow no longer used.** A multi-worker
> orchestration template from an earlier project phase.  The
> sentinel check below remains structurally correct against the
> current tree, but every workflow detail (Spec/* directories,
> the invariants the workers were operating on, the multi-round
> coordination protocol) is obsolete.  Kept as historical
> reference.

Every background worker spawned via `Agent(isolation: "worktree")` MUST
include these elements in its prompt:

## Required prefix: sentinel check

```
STEP 0 (MANDATORY, RUN BEFORE ANYTHING ELSE):

  # Verify you are in a valid Lean-formalization worktree. If this
  # fails, abort — your worktree is broken and any edits you make will
  # corrupt the main checkout via shared state.
  test -f lean/Patchelf.lean || { echo "ABORT: not a valid worktree (lean/ missing)"; exit 1; }
  test -f lean/lakefile.lean || { echo "ABORT: not a valid worktree (no lakefile)"; exit 1; }

If the sentinel fails, STOP. Report back with:
  BRANCH: worker/<unit>
  WORKTREE: <path>
  ABORTED: broken-worktree
  NOTES: Sentinel check failed; worktree checkout is missing lean/ subdirectory.
```

## Context about why this matters

Rounds 6 and 7 had 6+ worker failures where the `isolation: "worktree"`
infrastructure placed the worker on an old commit (typically
`d0f70ee`, from before the Lean formalization was merged to master).
The resulting worktree had no `lean/` subdirectory, so when the
worker tried `cd lean`, they fell back to absolute paths and wrote
into the main `/Users/cbaker2/ext-sources/patchelf/lean/...` — which
corrupted the coordinator's in-flight merges.

## Codebase conventions (carry-over)

- Every non-trivial invariant cites research/XX docs in a comment.
- No panic!/assert!/unreachable! outside Ops/Read.lean.
- No #check/#eval/#print/#synth/#guard anywhere.
- Use `sorry` with a clear blocker comment rather than weakening
  statements.
- `refine_IsValidELF` macro in Spec/PreservationTactics.lean helps
  discharge IsValidELF goals.
- R7-adversarial-fix #4 added `DynAreaOnlyOp` in Spec/DynAreaOnly.lean
  — use it for any op that only touches `dynArea`.
- R7-adversarial-fix #5 added `indexString_after_append` in
  Elf/StringsBundled.lean — use it for any `*_get_eq` or
  `*_runtime_*` theorem that needs the indexString-chain reasoning.
- T7 added 136 @[simp] projection lemmas; most `_preserves_validity`
  fields close with `simpa using h.<field>`.
- `IsCSafe` predicate (Elf/Strings.lean:173) is decidable; use
  `by decide` on concrete string literals.
- R6-B2 CONFIRMED `refine_IsValidELF` is append-safe.
- `set` tactic is NOT available (no Mathlib). Use `let` + explicit
  `have :=` for abbreviations.

## Scope discipline (post-wave-3 lessons)

Cap every unit at ≤2 sorries closed or ≤1 IsValidELF field added.
Wide-scope units (G2's 3-conjunct ParsePass3 extension, G3's 6
theorems at once, P2's 3-field extension) timed out at the 600s
watchdog. Narrow scope is reliable.
