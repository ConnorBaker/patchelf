/-
  GNU hash rebuild — reorders `.dynsym` (and `.gnu.version`), rebuilds
  the bloom/buckets/chain arrays of `.gnu.hash`, returns the resulting
  `old2new` permutation so callers can remap relocation symbol indices.

  Mirrors C++ patchelf's `rebuildGnuHashTable` (src/patchelf.cc:2076).

  Algorithm:
    1. For each dynsym from `firstSymIdx = ght.symndx` onward, compute
       `(hash, bucketIdx, originalPos)` where `hash = gnuHash(name)` and
       `bucketIdx = hash % nBuckets`.
    2. Sort entries by `bucketIdx` (stable; within a bucket, original
       order is preserved).
    3. Build `old2new` permutation: `old2new[entries[i].originalPos] = i`.
    4. Apply the permutation to `dynsym` and `versym` (within range
       `[firstSymIdx, end)`).
    5. Zero `bloom`; for each entry, set bits at `(h / 64) % maskwords`
       and `((h >> shift2) / 64) % maskwords`.
    6. Zero `buckets`; for each bucket, the FIRST entry in it gets its
       absolute dynsym index recorded.
    7. Fill `chain[i] = hash | (i is last in bucket ? 1 : 0)`.

  The permutation `old2new` is exposed so callers can remap relocation
  `r_info` symbol indices (callers typically rewrite raw rel/rela
  bytes via this mapping).
-/
module

public import Patchelf.Elf.SymbolSection
public import Patchelf.Elf.AuxSections
public import Patchelf.Elf.Basic

@[expose] public section

namespace Patchelf.Elf

open Patchelf.Elf (StringTable Symbol GnuHashTable gnuHash)

/-- One per-symbol record used to compute the new dynsym ordering. -/
structure GnuHashRebuildEntry where
  /-- gnuHash of the symbol's name (UInt32, full hash). -/
  hash        : UInt32
  /-- `hash % numBuckets` — the bucket index in the new layout. -/
  bucketIdx   : Nat
  /-- The symbol's original index in `[firstSymIdx, end)`. -/
  originalPos : Nat
  deriving Repr

namespace GnuHashRebuild

/-- Build per-symbol entries for the gnu hash rebuild.  Operates on
    typed symbols `[firstSymIdx, end)`.  An empty bucket count yields
    `bucketIdx = 0` for all entries (caller must reject this case). -/
def computeEntries {ds : StringSection} (syms : Array (TypedSymbol ds))
    (firstSymIdx : Nat) (numBuckets : Nat) : Array GnuHashRebuildEntry := Id.run do
  let mut entries : Array GnuHashRebuildEntry := #[]
  let n := syms.size
  let mut k : Nat := 0
  while h : firstSymIdx + k < n do
    let sym := syms[firstSymIdx + k]'h
    let nameBytes := (ds.lookup sym.st_name).getD ByteArray.empty
    let hsh := gnuHash nameBytes
    let bIdx := if numBuckets = 0 then 0 else hsh.toNat % numBuckets
    entries := entries.push { hash := hsh, bucketIdx := bIdx, originalPos := k }
    k := k + 1
  return entries

/-- Sort entries by `bucketIdx`, ties broken by `originalPos` (stable). -/
def sortByBucket (es : Array GnuHashRebuildEntry) : Array GnuHashRebuildEntry :=
  es.qsort (fun a b =>
    if a.bucketIdx < b.bucketIdx then true
    else if a.bucketIdx > b.bucketIdx then false
    else a.originalPos < b.originalPos)

/-- Build `old2new` from sorted entries: `old2new[entries[i].originalPos] = i`. -/
def buildOld2New (sorted : Array GnuHashRebuildEntry) (n : Nat) : Array Nat := Id.run do
  let mut a := Array.replicate n 0
  let mut i : Nat := 0
  while h : i < sorted.size do
    let e := sorted[i]'h
    if hOk : e.originalPos < a.size then
      a := a.set e.originalPos i hOk
    i := i + 1
  return a

/-- Apply a permutation to a sub-range `[firstSymIdx, firstSymIdx + perm.size)`
    of an array.  Symbols outside the range stay put. -/
def applyPerm {α} (arr : Array α) (firstSymIdx : Nat) (perm : Array Nat) : Array α := Id.run do
  let mut result := arr
  let mut i : Nat := 0
  while h : i < perm.size do
    if hSrc : firstSymIdx + i < arr.size then
      let dst := firstSymIdx + (perm[i]'h)
      if hDst : dst < result.size then
        result := result.set dst (arr[firstSymIdx + i]'hSrc) hDst
    i := i + 1
  return result

/-- `applyPerm` for the typed `SymbolSection`, preserving the dynstr index. -/
def applyPermSymbols {ds : StringSection} (s : SymbolSection ds)
    (firstSymIdx : Nat) (perm : Array Nat) : SymbolSection ds where
  symbols := applyPerm s.symbols firstSymIdx perm

/-- Compute the new bloom filter array.  Two bits are set per entry:
    one indexed by `hash`, the other by `hash >> shift2`.
    `ELFCLASS = 64` for ELF64. -/
def computeBloom (entries : Array GnuHashRebuildEntry)
    (maskwords shift2 : Nat) : Array UInt64 := Id.run do
  if maskwords = 0 then return #[]
  let mut bloom := Array.replicate maskwords (0 : UInt64)
  for e in entries do
    let h := e.hash.toNat
    let idx := (h / 64) % maskwords
    if hI : idx < bloom.size then
      let bit1 : UInt64 := 1 <<< UInt64.ofNat (h % 64)
      let bit2 : UInt64 := 1 <<< UInt64.ofNat ((h >>> shift2) % 64)
      bloom := bloom.set idx ((bloom[idx]'hI) ||| bit1 ||| bit2) hI
  return bloom

/-- Compute the new buckets array: for each bucket, record the FIRST
    sorted-entry's absolute dynsym index. -/
def computeBuckets (sorted : Array GnuHashRebuildEntry) (numBuckets firstSymIdx : Nat) :
    Array UInt32 := Id.run do
  let mut buckets : Array UInt32 := Array.replicate numBuckets 0
  let mut i : Nat := 0
  while h : i < sorted.size do
    let e := sorted[i]'h
    if hI : e.bucketIdx < buckets.size then
      if (buckets[e.bucketIdx]'hI) = 0 then
        buckets := buckets.set e.bucketIdx (firstSymIdx + i).toUInt32 hI
    i := i + 1
  return buckets

/-- Compute the new chain array: each entry holds `hash | (lastInBucket ? 1 : 0)`. -/
def computeChain (sorted : Array GnuHashRebuildEntry) : Array UInt32 := Id.run do
  let n := sorted.size
  let mut chain : Array UInt32 := Array.replicate n 0
  let mut i : Nat := 0
  while h : i < n do
    let e := sorted[i]'h
    let isLast :=
      if hN : i + 1 < n then (sorted[i + 1]'hN).bucketIdx ≠ e.bucketIdx
      else true
    let v : UInt32 := if isLast then e.hash ||| 1 else e.hash &&& (Complement.complement 1)
    if hC : i < chain.size then
      chain := chain.set i v hC
    i := i + 1
  return chain

/-- Bundle the rebuild's outputs.  Callers apply `dynsymPerm` to dynsym /
    versym (already done here for the typed side), and to relocation
    `r_info` symbol indices (NOT done here — the typed algebra doesn't
    structurally model relocations).  The byte-level remap pass uses
    `dynsymPerm` to rewrite raw rel/rela section bytes. -/
structure RebuildResult (ds : StringSection) where
  /-- New dynsym (typed, with the same ds index). -/
  dynsym  : SymbolSection ds
  /-- New versym (one entry per dynsym). -/
  versym  : Array UInt16
  /-- New gnu.hash table. -/
  ght     : GnuHashTable
  /-- `dynsymPerm[k]` = new position of `firstSymIdx + k` (within the
      hashed range).  Symbols outside `[firstSymIdx, end)` are not
      permuted.  Used by reloc remap. -/
  perm    : Array Nat
  /-- The first hashed dynsym index (= original `ght.symndx`). -/
  firstSymIdx : Nat

end GnuHashRebuild

/-- Rebuild the GNU hash table for the post-rename dynsym.  Returns
    the new dynsym, versym, hash table, and the dynsym permutation. -/
def rebuildGnuHash {ds : StringSection} (dynsym : SymbolSection ds)
    (dynstr : StringSection) (versym : Array UInt16) (ght : GnuHashTable) :
    GnuHashRebuild.RebuildResult ds :=
  let firstSymIdx := ght.symndx.toNat
  let numBuckets  := ght.buckets.size
  let entries     := GnuHashRebuild.computeEntries dynsym.symbols firstSymIdx numBuckets
  let sorted      := GnuHashRebuild.sortByBucket entries
  let perm        := GnuHashRebuild.buildOld2New sorted entries.size
  let newDynsym   := GnuHashRebuild.applyPermSymbols dynsym firstSymIdx perm
  let newVersym   := GnuHashRebuild.applyPerm versym firstSymIdx perm
  let newBloom    := GnuHashRebuild.computeBloom sorted ght.bloom.size ght.shift2.toNat
  let newBuckets  := GnuHashRebuild.computeBuckets sorted numBuckets firstSymIdx
  let newChain    := GnuHashRebuild.computeChain sorted
  let newGht : GnuHashTable :=
    { ght with bloom := newBloom, buckets := newBuckets, chain := newChain }
  { dynsym := newDynsym
    versym := newVersym
    ght    := newGht
    perm   := perm
    firstSymIdx := firstSymIdx }

end Patchelf.Elf
