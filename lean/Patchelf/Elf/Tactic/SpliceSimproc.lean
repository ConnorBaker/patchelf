/-
  `simp_splice` — discharge `readU{N} (splice bs off w) i = ...` goals
  with omega side conditions.

  Replaces the manual 4-step splice cascade in `ByteRoundtrip.lean`.
  See ROADMAP.md §5.4.

  Strategy: a tactic macro that runs `simp only [...] (discharger :=
  omega)` over the 12 splice/inside/disjoint rewrite lemmas in
  `Splice.lean`.  The omega discharger handles every side condition
  (`hSplice`, `hrFit`, disjointness, inside-bounds) since they are all
  linear arithmetic over `Nat`.

  This is intentionally the conservative implementation.  A true
  `simproc` that pattern-matches `readU{N} (splice ...)` and dispatches
  between disjoint/inside variants by trying omega is feasible (see
  `Lean.Elab.Tactic.Omega.omega : List Expr → MVarId → MetaM Unit` at
  `lean4/src/Lean/Elab/Tactic/Omega/Frontend.lean:672`) but no in-tree
  precedent calls omega from a simproc, so we start with the
  simp-with-discharger pattern that has known semantics.

  Note: we deliberately do NOT use `register_simp_attr` to introduce a
  new `[splice_simp]` set; in Lean 4.29.1 that command expands to
  `public meta initialize` (module-system syntax) and is unavailable in
  pre-module Lean files.  Naming the lemmas inline in the simp set
  avoids the issue and is no less explicit.
-/
module

public meta import Lean
public import Patchelf.Elf.Splice

@[expose] public section

namespace Patchelf.Elf.Tactic

open Lean Elab Tactic

/-- `simp_splice` rewrites `readU{N} (splice bs off w) r` to its
    disjoint or inside form, discharging side conditions via `omega`.

    Equivalent to `simp only [<splice lemma list>] (discharger := omega)`. -/
syntax (name := simpSplice) "simp_splice" (Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| simp_splice $[$loc:location]?) =>
    `(tactic| simp (discharger := omega) only
        [ Patchelf.Elf.Reader.readU8_splice_disjoint
        , Patchelf.Elf.Reader.readU16_splice_disjoint
        , Patchelf.Elf.Reader.readU32_splice_disjoint
        , Patchelf.Elf.Reader.readU64_splice_disjoint
        , Patchelf.Elf.Reader.readU8_splice_at_off_inside
        , Patchelf.Elf.Reader.readU16_splice_at_off_inside
        , Patchelf.Elf.Reader.readU32_splice_at_off_inside
        , Patchelf.Elf.Reader.readU64_splice_at_off_inside
        , Patchelf.Elf.Reader.readU8_splice_at_0_inside
        , Patchelf.Elf.Reader.readU16_splice_at_0_inside
        , Patchelf.Elf.Reader.readU32_splice_at_0_inside
        , Patchelf.Elf.Reader.readU64_splice_at_0_inside
        , Nat.sub_zero
        ] $[$loc:location]?)

end Patchelf.Elf.Tactic
