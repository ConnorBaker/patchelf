/-
  Typed DynamicSection indexed by a StringSection.

  Design:
    * The type is `DynamicSection ds` where `ds : StringSection`.
    * Structured fields whose semantics are "a pointer into .dynstr"
      carry `Fin ds.size` instead of `UInt64` — in-bounds-ness is at
      the type level, so the byte layer's `dynamicWellFormed`
      "value < dynstr.size" clause vanishes here.
    * Structured fields patchelf semantically manipulates:
        - `needed`   : Array (Fin ds.size)    -- DT_NEEDED entries
        - `rpath`    : Option (Fin ds.size)   -- DT_RPATH
        - `runpath`  : Option (Fin ds.size)   -- DT_RUNPATH
        - `soname`   : Option (Fin ds.size)   -- DT_SONAME
        - `flags1`   : Option UInt64          -- DT_FLAGS_1 (not a strref)
        - `debug`    : Option UInt64          -- DT_DEBUG   (not a strref)
    * Layout-sensitive tags (DT_RELA / DT_REL / DT_JMPREL / DT_INIT /
      DT_FINI / DT_VERSYM / DT_VERNEED / DT_STRTAB / DT_SYMTAB / DT_HASH /
      DT_GNU_HASH / DT_STRSZ) are NOT stored on `DynamicSection`.
      Patchelf's typed ops never touch them; the byte-layer template
      preserves them verbatim through `Adapter.patchDynamicEntries`.
    * DT_NULL is implicit — the encoder always emits it last.

  Key operation: `rebase` lifts a `DynamicSection ds` to
  `DynamicSection ds'` when `ds.size ≤ ds'.size`.  It's
  `Array.map (Fin.castLE h)` on the offset fields; non-offset fields
  pass through unchanged.
-/
module

public import Patchelf.Elf.StringSection

@[expose] public section

namespace Patchelf.Elf

open Patchelf.Elf (DynEntry)

/-- A dynamic section parameterized by the string section its
    offset-fields point into.  All `Fin ds.size` fields are
    in-bounds by construction, so a "values in bounds of dynstr"
    clause is vacuous at this type. -/
structure DynamicSection (ds : StringSection) where
  needed       : Array (Fin ds.size)
  rpath        : Option (Fin ds.size)
  runpath      : Option (Fin ds.size)
  soname       : Option (Fin ds.size)
  flags1       : Option UInt64
  debug        : Option UInt64
  deriving Repr

namespace DynamicSection

/-! ## Rebase under StringSection growth

    When `ds ≤ ds'` (size-monotonicity), every `Fin ds.size` index lifts
    to `Fin ds'.size` via `Fin.castLE`.  This is the operation that any
    op growing `.dynstr` needs.  It's a plain `Array.map`; no proofs
    required at call sites.
-/

/-- Lift a `DynamicSection ds` to `DynamicSection ds'` when
    `ds.size ≤ ds'.size`.  Numerically a no-op on offsets. -/
def rebase {ds ds' : StringSection} (h : StringSection.SizeLE ds ds')
    (d : DynamicSection ds) : DynamicSection ds' where
  needed   := d.needed.map  (Fin.castLE h)
  rpath    := d.rpath.map   (Fin.castLE h)
  runpath  := d.runpath.map (Fin.castLE h)
  soname   := d.soname.map  (Fin.castLE h)
  flags1   := d.flags1
  debug    := d.debug

/-! ## Structured mutations

    These are the operations patchelf actually performs.  Each is a
    single-line record update; the output type still carries `ds`, so
    validity is preserved at the type level without a theorem.
-/

/-- DT_NEEDED prepend: place a pre-existing dynstr offset at the
    front of `needed`.  Matches C++ patchelf's `addNeeded`, which
    shifts existing DT_NEEDED entries down and inserts new entries
    at the top of `.dynamic`. -/
def pushNeeded {ds : StringSection} (d : DynamicSection ds)
    (off : Fin ds.size) : DynamicSection ds :=
  { d with needed := #[off] ++ d.needed }

/-- DT_NEEDED remove: filter out entries whose dynstr-resolved name
    equals `target`.  Observable-style: the predicate is expressed at
    the offset level to keep this pure. -/
def filterNeeded {ds : StringSection} (d : DynamicSection ds)
    (p : Fin ds.size → Bool) : DynamicSection ds :=
  { d with needed := d.needed.filter p }

/-- DT_RPATH set: overwrite whatever rpath was there. -/
def setRpath {ds : StringSection} (d : DynamicSection ds)
    (off : Fin ds.size) : DynamicSection ds :=
  { d with rpath := some off }

/-- DT_RPATH clear. -/
def clearRpath {ds : StringSection} (d : DynamicSection ds) : DynamicSection ds :=
  { d with rpath := none }

/-- DT_RUNPATH set. -/
def setRunpath {ds : StringSection} (d : DynamicSection ds)
    (off : Fin ds.size) : DynamicSection ds :=
  { d with runpath := some off }

/-- DT_SONAME set. -/
def setSoname {ds : StringSection} (d : DynamicSection ds)
    (off : Fin ds.size) : DynamicSection ds :=
  { d with soname := some off }

/-- DT_DEBUG insert (idempotent on the flag-level; we overwrite the
    value).  Matches the C++ semantics: set to 0 if absent, no-op if
    present. -/
def addDebugTag {ds : StringSection} (d : DynamicSection ds) : DynamicSection ds :=
  match d.debug with
  | some _ => d
  | none   => { d with debug := some 0 }

/-- DT_FLAGS_1 set with DF_1_NODEFLIB (0x00000800).  See `elf.h`:
    `DF_1_NODEFLIB = 0x00000800` ("Ignore default lib search path").
    Do NOT confuse with `DF_1_PIE = 0x08000000`. -/
def setNoDefaultLib {ds : StringSection} (d : DynamicSection ds) : DynamicSection ds :=
  { d with flags1 := some ((d.flags1.getD 0) ||| 0x0000_0800) }

/-- Clear both rpath and runpath. -/
def stripRpath {ds : StringSection} (d : DynamicSection ds) : DynamicSection ds :=
  { d with rpath := none, runpath := none }

/-- Set one rpath slot, clear the other.  `forceRpath = true` → DT_RPATH;
    `forceRpath = false` → DT_RUNPATH. -/
def setRpathTag {ds : StringSection} (d : DynamicSection ds) (forceRpath : Bool)
    (off : Fin ds.size) : DynamicSection ds :=
  if forceRpath then
    { d with rpath := some off, runpath := none }
  else
    { d with rpath := none, runpath := some off }

/-- Rewrite every `needed` offset whose current `.dynstr` lookup equals
    `target`.  Matching offsets become `newOff`; others pass through. -/
def replaceNeededBy {ds : StringSection} (d : DynamicSection ds)
    (target : ByteArray) (newOff : Fin ds.size) : DynamicSection ds :=
  { d with needed := d.needed.map fun off =>
      match ds.lookup off with
      | some bytes => if bytes = target then newOff else off
      | none       => off }

/-- DT_NEEDED filter: drop every `needed` offset matching `target`. -/
def filterNeededBy {ds : StringSection} (d : DynamicSection ds)
    (target : ByteArray) : DynamicSection ds :=
  { d with needed := d.needed.filter fun off =>
      match ds.lookup off with
      | some bytes => bytes ≠ target
      | none       => true }

/-- Set the DT_SONAME offset. -/
def setSonameOff {ds : StringSection} (d : DynamicSection ds)
    (off : Fin ds.size) : DynamicSection ds :=
  { d with soname := some off }

/-- Remove DT_SONAME. -/
def removeSoname {ds : StringSection} (d : DynamicSection ds) : DynamicSection ds :=
  { d with soname := none }

/-! ## Rebase composition / invariance lemmas

    These are the only lemmas ops need to reason about rebase.  Everything
    else is `rfl` or a field projection — no proof work at the op layer.
-/

/-- Rebase preserves `needed.size`: the lift is an `Array.map`. -/
@[simp] theorem rebase_needed_size
    {ds ds' : StringSection} (h : StringSection.SizeLE ds ds')
    (d : DynamicSection ds) :
    (d.rebase h).needed.size = d.needed.size := by
  unfold rebase; simp

/-- The rebased offset at index `i` is the original offset at index `i`,
    lifted via `Fin.castLE`.  This is the ONE equation ops need when
    proving observables about rebased indices. -/
@[simp] theorem rebase_needed_getElem
    {ds ds' : StringSection} (h : StringSection.SizeLE ds ds')
    (d : DynamicSection ds) (i : Nat)
    (hi : i < (d.rebase h).needed.size) :
    ((d.rebase h).needed[i]'hi).val = (d.needed[i]'(by
      have := rebase_needed_size h d; omega)).val := by
  unfold rebase
  simp [Fin.castLE]
  rfl

/-- `pushNeeded` returns a dynamic section whose `needed` is the old
    one with `off` prepended.  Trivial but named. -/
@[simp] theorem pushNeeded_needed
    {ds : StringSection} (d : DynamicSection ds) (off : Fin ds.size) :
    (d.pushNeeded off).needed = #[off] ++ d.needed := rfl

/-- After `pushNeeded off`, the FIRST element IS `off`.  This is the
    core observable for `addNeeded`: the newly-added offset, looked up
    in the new `.dynstr`, resolves to the new name.  Combining with
    `StringSection.append_lookup` gives the full addNeeded observable. -/
@[simp] theorem pushNeeded_getElem_zero
    {ds : StringSection} (d : DynamicSection ds) (off : Fin ds.size)
    (h : 0 < (d.pushNeeded off).needed.size) :
    (d.pushNeeded off).needed[0]'h = off := by
  show (#[off] ++ d.needed)[0]'h = off
  rw [Array.getElem_append_left (by simp)]
  rfl

end DynamicSection
end Patchelf.Elf
