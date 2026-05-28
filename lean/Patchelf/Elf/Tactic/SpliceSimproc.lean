/-
  `simp_splice` — discharge `readU{N} (splice bs off w) i = ...` goals
  with omega side conditions.

  Replaces the manual 4-step splice cascade in `ByteRoundtrip.lean`.
  See ROADMAP.md §5.4.

  Strategy: a `[splice_simp]` simp set populated with the 12 splice/
  inside/disjoint rewrite lemmas in `Splice.lean`, plus a `simp_splice`
  tactic macro that runs `simp only [splice_simp] (discharger := omega)`.
  The omega discharger handles every side condition (`hSplice`,
  `hrFit`, disjointness, inside-bounds) since they are all linear
  arithmetic over `Nat`.

  This is intentionally the conservative implementation.  A true
  `simproc` that pattern-matches `readU{N} (splice ...)` and dispatches
  between disjoint/inside variants by trying omega is feasible (see
  `Lean.Elab.Tactic.Omega.omega : List Expr → MVarId → MetaM Unit` at
  `lean4/src/Lean/Elab/Tactic/Omega/Frontend.lean:672`) but no in-tree
  precedent calls omega from a simproc, so we start with the
  simp-with-discharger pattern that has known semantics.
-/
module

public meta import Lean
public import Patchelf.Elf.Splice
public import Patchelf.Elf.Encoder
public import Patchelf.Elf.Tactic.SpliceSimprocAttr

@[expose] public section

attribute [splice_simp]
  -- read-rewrite family: collapses readU{N} (splice ...) to readU{N} on
  -- the underlying buffer (disjoint case) or the splice payload (inside).
  Patchelf.Elf.Reader.readU8_splice_disjoint
  Patchelf.Elf.Reader.readU16_splice_disjoint
  Patchelf.Elf.Reader.readU32_splice_disjoint
  Patchelf.Elf.Reader.readU64_splice_disjoint
  Patchelf.Elf.Reader.readU8_splice_at_off_inside
  Patchelf.Elf.Reader.readU16_splice_at_off_inside
  Patchelf.Elf.Reader.readU32_splice_at_off_inside
  Patchelf.Elf.Reader.readU64_splice_at_off_inside
  Patchelf.Elf.Reader.readU8_splice_at_0_inside
  Patchelf.Elf.Reader.readU16_splice_at_0_inside
  Patchelf.Elf.Reader.readU32_splice_at_0_inside
  Patchelf.Elf.Reader.readU64_splice_at_0_inside
  -- size-yielding lemmas: let the omega discharger see through
  -- buffer-size aliases (`(splice X off w).size`, `(zeroBytes n).size`,
  -- `(Foo.write x).size`, `(writeArray ...).size`) without manual
  -- `have` clauses at the call site.
  Patchelf.Elf.Encoder.splice_size
  Patchelf.Elf.zeroBytes_size
  -- arithmetic cleanups: collapse `(off + k) - off = k`-shaped offsets
  -- that arise when an inside-splice lemma rewrites a read at
  -- `(off + k)` to `readU{N} w (off + k - off)`.
  Nat.sub_zero
  Nat.add_sub_cancel
  Nat.add_sub_cancel_left

namespace Patchelf.Elf.Tactic

open Lean Elab Tactic

/-- `simp_splice` rewrites `readU{N} (splice bs off w) r` to its
    disjoint or inside form, discharging side conditions via `omega`.

    Equivalent to `simp only [splice_simp] (discharger := omega)`. -/
syntax (name := simpSplice) "simp_splice" (Lean.Parser.Tactic.location)? : tactic

/-- Discharger used by `simp_splice`: rewrite splice/zeroBytes/writeArray
    sizes to their underlying terms (so omega can see them), then run
    omega.  The size-rewrite-then-omega ordering is what lets omega
    discharge fit conditions for nested splices like
    `phoff + phdrW.size ≤ (splice buf0 0 hdrW).size` even when
    `phdrW = writeArray ProgramHeader.write _` (no let-binding alias). -/
syntax "splice_disch" : tactic
macro_rules
  | `(tactic| splice_disch) =>
    `(tactic| (try simp only
                [Patchelf.Elf.Encoder.splice_size,
                 Patchelf.Elf.zeroBytes_size,
                 Patchelf.Elf.writeArray_DynEntry_size,
                 Patchelf.Elf.writeArray_ProgramHeader_size,
                 Patchelf.Elf.writeArray_SectionHeader_size,
                 Patchelf.Elf.writeArray_Symbol_size,
                 Patchelf.Elf.writeArray_writeU16_size,
                 Patchelf.Elf.ElfHeader.write_size,
                 Patchelf.Elf.Layout.ehdrSize,
                 Patchelf.Elf.Layout.phdrSize,
                 Patchelf.Elf.Layout.shdrSize,
                 Patchelf.Elf.Layout.dynEntrySize,
                 Patchelf.Elf.Layout.symEntrySize,
                 Array.size_map] at *); omega)

macro_rules
  | `(tactic| simp_splice $[$loc:location]?) =>
    `(tactic| simp (discharger := splice_disch) only [splice_simp]
              $[$loc:location]?)

end Patchelf.Elf.Tactic
