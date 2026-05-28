/-
  renameDynamicSymbols — rewrite symbol names in `.dynsym`.

  Semantics:
    1. Append `newName` to `.dynstr`; get `newOff`.
    2. For each symbol whose current name matches `oldName`, rewrite
       its `st_name` to `newOff`.
    3. Rebuild SysV `.hash` against the new symbol array + new dynstr.
    4. Reject binaries with `.gnu.hash` (precondition).

  Implementation uses `Option.map` on dynsym (rather than a
  `match` on dynsym) so the structural projections reduce by simp,
  letting observables close cleanly.
-/
module

public import Patchelf.Elf.ValidElfFile
public import Patchelf.Elf.GnuHashRebuild
public import Patchelf.Elf.Basic

@[expose] public section

namespace Patchelf.Elf

open Patchelf.Elf (StringTable Symbol SysVHashTable sysvHash)

/-- Rename precondition: has dynsym, offset fits in UInt32.
    Note: removed the `noGnuHash` precondition — the op now rebuilds
    `.gnu.hash` (and the post-rename reloc remap is the caller's
    responsibility; see `Patchelf.CLI.renameOnce` for wiring). -/
structure RenameDynamicSymbolsOk (e : ValidElfFile) (newName : String) : Prop where
  hasDynsym    : e.dynsym.isSome
  offsetFits   : e.dynstr.bytes.size + newName.toUTF8.size + 1 < UInt32.size

/-- Rebuild the SysV hash buckets/chain for the new symbol array. -/
def rebuildSysVHash (ht : SysVHashTable) (ds : StringSection)
    (syms : Array (TypedSymbol ds)) : SysVHashTable :=
  let nBuckets := ht.buckets.size
  let nChain   := ht.chain.size
  let firstSymIdx := syms.size - nChain
  let initBuckets : Array UInt32 := Array.replicate nBuckets 0
  let initChain   : Array UInt32 := Array.replicate nChain 0
  let (newBuckets, newChain) :=
    (List.range nChain).foldl
      (fun (acc : Array UInt32 × Array UInt32) i =>
        let (buckets, chain) := acc
        let symIdx := firstSymIdx + i
        if hSym : symIdx < syms.size then
          let name := (ds.lookup (syms[symIdx]'hSym).st_name).getD ByteArray.empty
          let hash := sysvHash name
          if nBuckets = 0 then acc
          else
            let bIdx := (hash.toNat % nBuckets)
            if hBI : bIdx < buckets.size then
              let prev := buckets[bIdx]'hBI
              let newChain :=
                if hCI : i < chain.size then chain.set i prev hCI else chain
              let newBuckets := buckets.set bIdx i.toUInt32 hBI
              (newBuckets, newChain)
            else acc
        else acc)
      (initBuckets, initChain)
  { ht with buckets := newBuckets, chain := newChain }

/-- Per-symbol rename: if `s.st_name` looks up to `oldName` in `ds`,
    return `s` with `st_name := off`; otherwise return `s` unchanged. -/
def renameTypedSymbol {ds : StringSection} (oldName : String) (off : Fin ds.size)
    (s : TypedSymbol ds) : TypedSymbol ds :=
  match ds.lookup s.st_name with
  | some bytes => if bytes = oldName.toUTF8 then { s with st_name := off } else s
  | none       => s

/-- Rename every symbol in a section. -/
def SymbolSection.rename {ds : StringSection} (ss : SymbolSection ds)
    (oldName : String) (off : Fin ds.size) : SymbolSection ds where
  symbols := ss.symbols.map (renameTypedSymbol oldName off)

/-- The op: grow dynstr, rebase dynsym, rename matching symbols,
    rebuild SysV hash.

    Uses `Option.map` on dynsym (rather than `match`) so that
    `(rename e).dynsym = e'.dynsym.map ...` is rfl-reducible — this
    lets the observables close cleanly.

    GNU hash rebuild is a SEPARATE op (`gnuHashRebuildOp`) called by
    the CLI as a post-pass; this avoids reshaping the rename op's
    body and breaking the existing observable theorems. -/
def renameDynamicSymbols (e : ValidElfFile) (oldName newName : String)
    (_h : RenameDynamicSymbolsOk e newName) : ValidElfFile :=
  let p := e.growDynstr newName
  let e'  := p.1
  let off := p.2
  let newDynsym := e'.dynsym.map (fun dsym => dsym.rename oldName off)
  let newSysvHash := e'.sysvHash.map (fun shs =>
    match newDynsym with
    | some nd => { table := rebuildSysVHash shs.table e'.dynstr nd.symbols }
    | none    => shs)
  { e' with dynsym := newDynsym, sysvHash := newSysvHash }

/-- Rebuild `.gnu.hash` for a `ValidElfFile` whose `.dynsym` has been
    renamed.  Reorders `.dynsym` and `.gnu.version` according to the
    new bucket layout; rewrites bloom/buckets/chain.  Returns the
    post-rebuild file PLUS the dynsym permutation for callers that
    need to remap relocation `r_info` symbol indices.

    No-op (returns input unchanged + identity perm) when either
    `.gnu.hash` is absent or `.dynsym` is absent. -/
def gnuHashRebuildOp (e : ValidElfFile) : ValidElfFile × Option (Nat × Array Nat) :=
  match _h : e.dynsym, e.gnuHash with
  | some dsym, some ghs =>
    let versym0 : Array UInt16 := e.versym.getD #[]
    let r := rebuildGnuHash dsym e.dynstr versym0 ghs.table
    let e' : ValidElfFile :=
      { e with
          dynsym := some r.dynsym
          versym := if e.versym.isSome then some r.versym else none
          gnuHash := some { table := r.ght } }
    (e', some (r.firstSymIdx, r.perm))
  | _, _ => (e, none)

/-! ## Observables -/

/-- The dynstr grew by `newName.toUTF8.size + 1`. -/
theorem renameDynamicSymbols_dynstr
    (e : ValidElfFile) (oldName newName : String)
    (h : RenameDynamicSymbolsOk e newName) :
    (renameDynamicSymbols e oldName newName h).dynstr
      = (e.dynstr.append newName).1 := rfl

/-- The result's dynsym is `some` iff the input's was `some`. -/
theorem renameDynamicSymbols_dynsym_isSome
    (e : ValidElfFile) (oldName newName : String)
    (h : RenameDynamicSymbolsOk e newName) :
    (renameDynamicSymbols e oldName newName h).dynsym.isSome
      = e.dynsym.isSome := by
  unfold renameDynamicSymbols ValidElfFile.growDynstr
  cases e.dynsym <;> rfl

/-- If the input had a symbol at index `i` whose `st_name` looked up
    to `oldName` in the OLD dynstr, the output has a symbol at the
    same index whose `st_name` equals the newly-appended offset.
    (The GNU hash rebuild reorders dynsym; this observable is
    pre-rebuild.) -/
theorem renameDynamicSymbols_observable
    (e : ValidElfFile) (oldName newName : String)
    (h : RenameDynamicSymbolsOk e newName)
    (dsym : SymbolSection e.dynstr) (hDsym : e.dynsym = some dsym)
    (i : Nat) (hi : i < dsym.symbols.size)
    (hMatchesThroughNew :
      (e.dynstr.append newName).1.lookup
        (((dsym.rebase (StringSection.size_le_append e.dynstr newName)).symbols[i]'(by
          rw [SymbolSection.rebase_size]; exact hi)).st_name)
      = some oldName.toUTF8) :
    ∃ dsym',
      (renameDynamicSymbols e oldName newName h).dynsym = some dsym' ∧
      ∃ hi' : i < dsym'.symbols.size,
        (dsym'.symbols[i]'hi').st_name.val = (e.dynstr.appendOffset newName).val := by
  have hRebaseSize : (dsym.rebase (StringSection.size_le_append e.dynstr newName)).symbols.size
                   = dsym.symbols.size := SymbolSection.rebase_size _ _
  refine ⟨(dsym.rebase (StringSection.size_le_append e.dynstr newName)).rename
            oldName (e.dynstr.appendOffset newName), ?_, ?_⟩
  · unfold renameDynamicSymbols ValidElfFile.growDynstr
    simp [hDsym]
  have hSize : ((dsym.rebase (StringSection.size_le_append e.dynstr newName)).rename
                 oldName (e.dynstr.appendOffset newName)).symbols.size
             = dsym.symbols.size := by
    unfold SymbolSection.rename
    simp
  refine ⟨hSize ▸ hi, ?_⟩
  show (((dsym.rebase (StringSection.size_le_append e.dynstr newName)).rename
          oldName (e.dynstr.appendOffset newName)).symbols[i]'_).st_name.val =
       (e.dynstr.appendOffset newName).val
  unfold SymbolSection.rename
  rw [Array.getElem_map]
  unfold renameTypedSymbol
  rw [hMatchesThroughNew]
  simp

end Patchelf.Elf
