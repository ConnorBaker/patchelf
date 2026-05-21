/-
  clearSymbolVersion — reset `.gnu.version` to VER_NDX_GLOBAL (1) for
  every symbol whose name matches a target.

  All section-selection plumbing is implicit:
    * `.versym` is a named field — no index, no `updateSectionContent`,
      no shstrndx inequality, no content-shape cases.
    * `.dynsym` is a named `Option (SymbolSection dynstr)` — TypedSymbol's
      `st_name` is already `Fin dynstr.size`, so `lookup` is total.
    * Nothing about dynstr or dynamic is touched — frame observables are
      `rfl` / `by rfl`.

  Design note on the precondition: The typed `versym` and `dynsym.symbols`
  parallelism is a parser-level runtime invariant.  An earlier design
  prototyped a `VersymSection` carrier (with a `sizeEq` field linking
  the array length to `dynsym.symbols.size` at the type level) but
  the structure was retired (see `AuxSections.lean` historical note);
  the stored field is a plain `Option (Array UInt16)` to avoid
  dependent-Option juggling across `.dynstr`-growing ops.  This op
  uses a per-element runtime bounds check, which lets the
  precondition stay a plain `isSome ∧ isSome` pair.  Observable is
  stated conditional on the bounds predicate holding for the witness
  index.
-/

import Patchelf.Elf.ValidElfFile
import Patchelf.Elf.Basic

namespace Patchelf.Elf

open Patchelf.Elf (StringTable)

/-- VER_NDX_GLOBAL — the ELF spec's "no explicit version" marker.  Same
    semantic constant for the versym clear operation. -/
def VER_NDX_GLOBAL : UInt16 := 1

/-- Precondition for `clearSymbolVersion`: dynsym and versym both present.
    (Size parity of `versym.size = dynsym.symbols.size` is a parser
    invariant; the op tolerates mismatch via per-element bounds checks
    but the observable only bites at in-range indices.) -/
structure ClearSymbolVersionOk (e : ValidElfFile) : Prop where
  hasDynsym : e.dynsym.isSome
  hasVersym : e.versym.isSome

/-- Build a cleared versym array: for each index `i < vs.size`, replace
    the entry with `VER_NDX_GLOBAL` iff (a) `i` is also a valid index
    into `syms.symbols` and (b) that symbol's name resolves in `ds` to
    `symName.toUTF8`.  Otherwise pass through unchanged.

    The per-element `if hLt : i < syms.symbols.size` guard means this is
    well-typed even if the parser invariant `versym.size =
    dynsym.symbols.size` is violated — in which case "extra" versym
    entries pass through.  With the invariant holding (the realistic
    case) the bounds check is always `true`. -/
def clearVersymEntries
    {ds : StringSection} (syms : SymbolSection ds)
    (vs : Array UInt16) (symName : String) : Array UInt16 :=
  Array.ofFn (n := vs.size) fun i =>
    if hLt : i.val < syms.symbols.size then
      let sym := syms.symbols[i.val]'hLt
      match ds.lookup sym.st_name with
      | some bytes => if bytes = symName.toUTF8 then VER_NDX_GLOBAL else vs[i]
      | none       => vs[i]
    else
      vs[i]

/-- Size of the rewritten versym equals the input. -/
@[simp] theorem clearVersymEntries_size
    {ds : StringSection} (syms : SymbolSection ds)
    (vs : Array UInt16) (symName : String) :
    (clearVersymEntries syms vs symName).size = vs.size := by
  unfold clearVersymEntries
  simp

/-- Read the rewritten versym at index `i`. -/
theorem clearVersymEntries_getElem
    {ds : StringSection} (syms : SymbolSection ds)
    (vs : Array UInt16) (symName : String)
    (i : Nat) (hi : i < vs.size) :
    (clearVersymEntries syms vs symName)[i]'(by
      rw [clearVersymEntries_size]; exact hi) =
      (if hLt : i < syms.symbols.size then
        let sym := syms.symbols[i]'hLt
        match ds.lookup sym.st_name with
        | some bytes => if bytes = symName.toUTF8 then VER_NDX_GLOBAL else vs[i]
        | none       => vs[i]
      else
        vs[i]) := by
  unfold clearVersymEntries
  rw [Array.getElem_ofFn]
  rfl

/-- The op: find every dynsym entry whose name matches `symName` and set
    the corresponding versym entry to `VER_NDX_GLOBAL`.  The rewrite is
    a pure `Array.ofFn`; ValidElfFile record update is a one-liner. -/
def clearSymbolVersion (e : ValidElfFile) (symName : String)
    (h : ClearSymbolVersionOk e) : ValidElfFile :=
  let dsym : SymbolSection e.dynstr := e.dynsym.get h.hasDynsym
  let vs   : Array UInt16           := e.versym.get h.hasVersym
  { e with versym := some (clearVersymEntries dsym vs symName) }

/-! ## Observables -/

/-- The `.versym` field after the op is `some` — the op never erases
    a present versym. -/
@[simp] theorem clearSymbolVersion_versym_isSome
    (e : ValidElfFile) (symName : String) (h : ClearSymbolVersionOk e) :
    (clearSymbolVersion e symName h).versym.isSome := by
  unfold clearSymbolVersion; rfl

/-- Primary observable: if an index `i` identifies a dynsym symbol
    whose name resolves to `symName`, then the post-op versym entry at
    `i` is `VER_NDX_GLOBAL`.

    The hypothesis takes a clean `ds.lookup ... = some symName.toUTF8`
    (the realistic case — the parser's invariant ensures `st_name`
    points at a real entry).  The `none` branch is pass-through and would
    require a stronger premise to observe. -/
theorem clearSymbolVersion_cleared
    (e : ValidElfFile) (symName : String) (h : ClearSymbolVersionOk e)
    (dsym : SymbolSection e.dynstr) (vs : Array UInt16)
    (hDsym : e.dynsym = some dsym) (hVs : e.versym = some vs)
    (i : Nat) (hi : i < vs.size) (hj : i < dsym.symbols.size)
    (hMatch : e.dynstr.lookup (dsym.symbols[i]'hj).st_name = some symName.toUTF8) :
    ∃ vs',
      (clearSymbolVersion e symName h).versym = some vs' ∧
      ∃ hi' : i < vs'.size, vs'[i] = VER_NDX_GLOBAL := by
  -- Pin the accessors.
  have hDsymEq : e.dynsym.get h.hasDynsym = dsym := by simp [hDsym]
  have hVsEq   : e.versym.get h.hasVersym = vs   := by simp [hVs]
  refine ⟨clearVersymEntries dsym vs symName, ?_, ?_⟩
  · unfold clearSymbolVersion
    simp [hDsymEq, hVsEq]
  · have hi' : i < (clearVersymEntries dsym vs symName).size := by
      rw [clearVersymEntries_size]; exact hi
    refine ⟨hi', ?_⟩
    rw [clearVersymEntries_getElem dsym vs symName i hi]
    simp [hj, hMatch]

/-- Dual observable: non-matching entries are preserved.  If at index `i`
    either (a) `i` is out of bounds for `dsym.symbols` (versym is longer
    than dynsym — parser-invariant-violating case), or (b) the lookup
    fails, or (c) the lookup yields something ≠ `symName.toUTF8`, then
    the post-op versym[i] equals the pre-op vs[i]. -/
theorem clearSymbolVersion_preserved
    (e : ValidElfFile) (symName : String) (h : ClearSymbolVersionOk e)
    (dsym : SymbolSection e.dynstr) (vs : Array UInt16)
    (hDsym : e.dynsym = some dsym) (hVs : e.versym = some vs)
    (i : Nat) (hi : i < vs.size)
    (hNotMatch :
      ∀ (hj : i < dsym.symbols.size),
        e.dynstr.lookup (dsym.symbols[i]'hj).st_name ≠ some symName.toUTF8) :
    ∃ vs',
      (clearSymbolVersion e symName h).versym = some vs' ∧
      ∃ hi' : i < vs'.size, vs'[i] = vs[i] := by
  have hDsymEq : e.dynsym.get h.hasDynsym = dsym := by simp [hDsym]
  have hVsEq   : e.versym.get h.hasVersym = vs   := by simp [hVs]
  refine ⟨clearVersymEntries dsym vs symName, ?_, ?_⟩
  · unfold clearSymbolVersion
    simp [hDsymEq, hVsEq]
  · have hi' : i < (clearVersymEntries dsym vs symName).size := by
      rw [clearVersymEntries_size]; exact hi
    refine ⟨hi', ?_⟩
    rw [clearVersymEntries_getElem dsym vs symName i hi]
    by_cases hLt : i < dsym.symbols.size
    · -- In-bounds symbol: do a match on the lookup.
      simp only [hLt, dite_true]
      match hLookup : e.dynstr.lookup (dsym.symbols[i]'hLt).st_name with
      | some bytes =>
          have hNe : bytes ≠ symName.toUTF8 := by
            intro hEq
            have := hNotMatch hLt
            rw [hLookup, hEq] at this
            exact this rfl
          simp only [if_neg hNe]
      | none =>
          rfl
    · simp only [hLt, dite_false]

/-! ## Frame observables: nothing else changes -/

@[simp] theorem clearSymbolVersion_dynstr
    (e : ValidElfFile) (symName : String) (h : ClearSymbolVersionOk e) :
    (clearSymbolVersion e symName h).dynstr = e.dynstr := rfl
@[simp] theorem clearSymbolVersion_dynsym
    (e : ValidElfFile) (symName : String) (h : ClearSymbolVersionOk e) :
    (clearSymbolVersion e symName h).dynsym = e.dynsym := rfl
@[simp] theorem clearSymbolVersion_dynamic
    (e : ValidElfFile) (symName : String) (h : ClearSymbolVersionOk e) :
    (clearSymbolVersion e symName h).dynamic = e.dynamic := rfl
@[simp] theorem clearSymbolVersion_header
    (e : ValidElfFile) (symName : String) (h : ClearSymbolVersionOk e) :
    (clearSymbolVersion e symName h).header = e.header := rfl
@[simp] theorem clearSymbolVersion_phdrs
    (e : ValidElfFile) (symName : String) (h : ClearSymbolVersionOk e) :
    (clearSymbolVersion e symName h).phdrs = e.phdrs := rfl

/-- The rewrite preserves versym size. -/
theorem clearSymbolVersion_versym_size
    (e : ValidElfFile) (symName : String) (h : ClearSymbolVersionOk e)
    (vs : Array UInt16) (hVs : e.versym = some vs) :
    ∃ vs', (clearSymbolVersion e symName h).versym = some vs' ∧ vs'.size = vs.size := by
  have hVsEq : e.versym.get h.hasVersym = vs := by simp [hVs]
  refine ⟨clearVersymEntries (e.dynsym.get h.hasDynsym) vs symName, ?_, ?_⟩
  · unfold clearSymbolVersion; simp [hVsEq]
  · rw [clearVersymEntries_size]

end Patchelf.Elf
