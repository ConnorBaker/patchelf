/-
  Registers the `[splice_simp]` simp set used by `simp_splice`.

  Split into its own module so that callers can `attribute
  [splice_simp] X` after the init that registers the attribute has
  fired (Lean does not interleave init blocks with subsequent
  attribute applications within the same compilation unit).
-/
module

public meta import Lean

@[expose] public section

/-- Simp set for splice/extract byte-read rewrites.  Members are
    theorems of the form `readU{N} (splice bs off w) r = readU{N} ...`
    with side conditions in linear arithmetic over `Nat` (so they can
    be discharged by `omega`). -/
register_simp_attr splice_simp
