/-
  Structural-decoder helpers: `buildArray`, `decodeStringTable`,
  `decodeVersym`, `decodeChain` (linked-list walker), `decodeSysVHash`,
  `decodeGnuHash`. Structural decoders never fail (pure byte-reads +
  wrappers); validation is factored out to top-level `parse`.

  All per-struct decoders for fixed-layout records (ElfIdent,
  ElfHeader, ProgramHeader, SectionHeader, DynEntry, Symbol, Vernaux)
  plus their fixed-count-array wrappers (`decodePhdrs`, `decodeShdrs`,
  `decodeDynsym`), the `.dynamic` early-exit loop decoder
  (`decodeDynamic{Loop,}`), the Verneed / Vernaux chain decoders, and
  the parser-side `DecodedIdent` / `decodeIdent` wrapper are all in
  `Schemas.lean` — DSL-generated where the DSL supports the field
  shape, hand-written where it doesn't (chained / variable-size /
  validation-additive).
-/
module

public import Patchelf.Elf.Basic
public import Patchelf.Elf.Layout
public import Patchelf.Elf.Reader

@[expose] public section

namespace Patchelf.Elf.Decode

open Layout Reader

/-- Build an `Array α` of length `n` by mapping each index `i < n` through
    `f`. Every packed-table decoder in this file reduces to a call of
    `buildArray`. Keeps the size lemma — `buildArray_size` — in one place. -/
def buildArray {α : Type} (n : Nat) (f : Nat → α) : Array α :=
  (List.range n).foldl (fun acc i => acc.push (f i)) #[]

@[simp] theorem buildArray_size {α : Type} (n : Nat) (f : Nat → α) :
    (buildArray n f).size = n := by
  unfold buildArray
  rw [List.foldl_push_eq_append]
  simp

/-- `buildArray n f` produces `#[f 0, f 1, ..., f (n-1)]`; indexing at
    position `i < n` recovers `f i`. -/
theorem buildArray_getElem {α : Type} (n : Nat) (f : Nat → α)
    (i : Nat) (hi : i < (buildArray n f).size) :
    (buildArray n f)[i] = f i := by
  have hiN : i < n := by rw [buildArray_size] at hi; exact hi
  unfold buildArray
  simp only [List.foldl_push_eq_append, Array.empty_append]
  show (List.map f (List.range n)).toArray[i]'(by simp; exact hiN) = f i
  rw [List.getElem_toArray, List.getElem_map, List.getElem_range]

/-- Decode a section's string-table contents: the `sz` bytes starting at
    `off` in `bs`. Always succeeds structurally; null-termination is a
    validity check performed upstream. -/
def decodeStringTable (bs : ByteArray) (off : Nat) (sz : Nat) : StringTable :=
  ⟨readBytes bs off sz⟩

/-- `decodeStringTable bs off sz` has exactly `sz` bytes when the window
    fits in `bs`. Bridge for the `encoderLocationsAgree.dynstr` /
    `.shstrtab` / `.interp` size-match clauses:
    `shdrs[i].size.val.toNat = decoded.bytes.size` reduces to `sz = sz`
    under this identity. -/
theorem decodeStringTable_bytes_size (bs : ByteArray) (off sz : Nat)
    (h : off + sz ≤ bs.size) :
    (decodeStringTable bs off sz).bytes.size = sz := by
  unfold decodeStringTable
  show (readBytes bs off sz).size = sz
  exact readBytes_size bs off sz h

/-- `bs.extract off (off+sz)` has exactly `sz` bytes when the window fits.
    Bridge for the `encoderLocationsAgree.interp` raw-section size match
    (`.interp` is decoded as `bs.extract off (off+sz)` directly rather
    than via `decodeStringTable`). -/
theorem bytes_extract_size (bs : ByteArray) (off sz : Nat)
    (h : off + sz ≤ bs.size) :
    (bs.extract off (off + sz)).size = sz := by
  rw [ByteArray.size_extract]; omega

/-- Decode a `.gnu.version` (versym) section as an `Array UInt16`.
    Each entry is a single `Elf64_Half` (2 bytes) holding a version
    index (VER_NDX_*). The array length equals the `.dynsym` entry
    count (one versym per symbol); the `sz` argument is the section
    size in bytes, so `n = sz / 2` at the parser layer. -/
def decodeVersym (bs : ByteArray) (off : Nat) (n : Nat) : Array UInt16 :=
  buildArray n (fun i => readU16 bs (off + i * 2))

@[simp] theorem decodeVersym_size (bs : ByteArray) (off n : Nat) :
    (decodeVersym bs off n).size = n := by
  unfold decodeVersym; exact buildArray_size n _

/-- Helper loop for `decodeChain`. Structural recursion on `remaining`
    (which strictly decreases each step) lets Lean generate equation
    lemmas + enables induction-based size bounds. Extracted as a
    top-level `def` rather than `let rec` so `decodeChainLoop_size_le`
    can reference it by name. -/
def decodeChainLoop {α : Type}
    (decode : Nat → α) (next : α → UInt32)
    (curOff : Nat) (remaining : Nat) (acc : Array α) : Array α :=
  match remaining with
  | 0 => acc
  | n + 1 =>
    let x := decode curOff
    let acc' := acc.push x
    if next x = 0 then acc'
    else decodeChainLoop decode next (curOff + (next x).toNat) n acc'

/-- Walk a linked list of records with byte-offset `next` pointers.
    Given `decode` that produces one record at a given offset and `next`
    that extracts the byte-offset-to-next field (0 = end), collect
    records by following the chain until `next = 0` or `maxCount`
    exhausts. Used by both the Verneed and Vernaux chain decoders. -/
def decodeChain {α : Type}
    (decode : Nat → α) (next : α → UInt32)
    (startOff : Nat) (maxCount : Nat) : Array α :=
  decodeChainLoop decode next startOff maxCount #[]

/-- `decodeChainLoop` grows the accumulator by at most `remaining`
    entries. Each step either terminates (push 1 + exit) or recurses
    with `remaining - 1`. Structural induction on `remaining` closes it. -/
theorem decodeChainLoop_size_le {α : Type}
    (decode : Nat → α) (next : α → UInt32)
    (curOff remaining : Nat) (acc : Array α) :
    (decodeChainLoop decode next curOff remaining acc).size
      ≤ acc.size + remaining := by
  induction remaining generalizing curOff acc with
  | zero => simp [decodeChainLoop]
  | succ n ih =>
    unfold decodeChainLoop
    simp only []
    by_cases h : next (decode curOff) = 0
    · simp [h, Array.size_push]
    · simp only [h, if_false]
      have := ih (curOff + (next (decode curOff)).toNat) (acc.push (decode curOff))
      simp [Array.size_push] at this
      omega

/-- `decodeChain` returns at most `maxCount` entries. -/
theorem decodeChain_size_le {α : Type}
    (decode : Nat → α) (next : α → UInt32)
    (startOff maxCount : Nat) :
    (decodeChain decode next startOff maxCount).size ≤ maxCount := by
  unfold decodeChain
  have := decodeChainLoop_size_le decode next startOff maxCount #[]
  simpa using this

/-- Read a packed array of u32s from `bs[off..off+n*4)`. -/
def readU32Array (bs : ByteArray) (off n : Nat) : Array UInt32 :=
  buildArray n (fun i => readU32 bs (off + i * 4))

/-- Read a packed array of u64s from `bs[off..off+n*8)`. -/
def readU64Array (bs : ByteArray) (off n : Nat) : Array UInt64 :=
  buildArray n (fun i => readU64 bs (off + i * 8))

/-- Exposed unfold: `readU32Array` reduces to `buildArray`.  Keeps
    the def private while letting `simp` see through it in the
    variable-length byte-roundtrip proofs. -/
@[simp] theorem readU32Array_eq (bs : ByteArray) (off n : Nat) :
    readU32Array bs off n = buildArray n (fun i => readU32 bs (off + i * 4)) := rfl

@[simp] theorem readU64Array_eq (bs : ByteArray) (off n : Nat) :
    readU64Array bs off n = buildArray n (fun i => readU64 bs (off + i * 8)) := rfl

/-- Decode a SysV `.hash` section at `bs[off..off+sz)`. Header is 8
    bytes, then `numBuckets` u32 buckets, then `numChain` u32 chain.

    Reads the on-disk `numBuckets`/`numChain` to determine array
    lengths, with a defensive `min` against `sz` to guard against a
    malformed section claiming more entries than fit. -/
def decodeSysVHash (bs : ByteArray) (off sz : Nat) : SysVHashTable :=
  let numBuckets := readU32 bs off
  let numChain   := readU32 bs (off + 4)
  let bucketsOff := off + 8
  let chainOff   := bucketsOff + numBuckets.toNat * 4
  let bucketCount := min numBuckets.toNat ((sz - 8) / 4)
  let chainCount  := min numChain.toNat
                      ((sz - 8 - bucketCount * 4) / 4)
  { buckets := readU32Array bs bucketsOff bucketCount
    chain   := readU32Array bs chainOff  chainCount }

/-- Decode a GNU `.gnu.hash` section at `bs[off..off+sz)`. Header is 16
    bytes, then `maskwords` u64 bloom filters, then `numBuckets` u32
    buckets, then the chain fills the rest. -/
def decodeGnuHash (bs : ByteArray) (off sz : Nat) : GnuHashTable :=
  let numBuckets := readU32 bs off
  let symndx     := readU32 bs (off + 4)
  let maskwords  := readU32 bs (off + 8)
  let shift2     := readU32 bs (off + 12)
  let bloomOff   := off + 16
  let bucketsOff := bloomOff + maskwords.toNat * 8
  let chainOff   := bucketsOff + numBuckets.toNat * 4
  let bloomCount   := min maskwords.toNat ((sz - 16) / 8)
  let bucketCount  := min numBuckets.toNat
                        ((sz - 16 - bloomCount * 8) / 4)
  let chainCount   := (sz - 16 - bloomCount * 8 - bucketCount * 4) / 4
  { symndx  := symndx
    shift2  := shift2
    bloom   := readU64Array bs bloomOff bloomCount
    buckets := readU32Array bs bucketsOff bucketCount
    chain   := readU32Array bs chainOff  chainCount }

/-- Bucket count in `decodeSysVHash` is exactly `min numBuckets.toNat ((sz-8)/4)`.
    Exposed so Roundtrip-level size bounds can reason about the
    decoded array sizes without unfolding the private `readU32Array`. -/
@[simp] theorem decodeSysVHash_buckets_size (bs : ByteArray) (off sz : Nat) :
    (decodeSysVHash bs off sz).buckets.size =
      min (readU32 bs off).toNat ((sz - 8) / 4) := by
  unfold decodeSysVHash readU32Array
  simp [buildArray_size]

/-- Chain count in `decodeSysVHash` is exactly
    `min numChain.toNat ((sz - 8 - bucketCount * 4) / 4)`. -/
@[simp] theorem decodeSysVHash_chain_size (bs : ByteArray) (off sz : Nat) :
    (decodeSysVHash bs off sz).chain.size =
      min (readU32 bs (off + 4)).toNat
        ((sz - 8 - (min (readU32 bs off).toNat ((sz - 8) / 4)) * 4) / 4) := by
  unfold decodeSysVHash readU32Array
  simp [buildArray_size]

/-- Bloom count in `decodeGnuHash` is exactly `min maskwords.toNat ((sz-16)/8)`. -/
@[simp] theorem decodeGnuHash_bloom_size (bs : ByteArray) (off sz : Nat) :
    (decodeGnuHash bs off sz).bloom.size =
      min (readU32 bs (off + 8)).toNat ((sz - 16) / 8) := by
  unfold decodeGnuHash readU64Array
  simp [buildArray_size]

/-- Bucket count in `decodeGnuHash` is exactly
    `min numBuckets.toNat ((sz - 16 - bloomCount * 8) / 4)`. -/
@[simp] theorem decodeGnuHash_buckets_size (bs : ByteArray) (off sz : Nat) :
    (decodeGnuHash bs off sz).buckets.size =
      min (readU32 bs off).toNat
        ((sz - 16 - (min (readU32 bs (off + 8)).toNat ((sz - 16) / 8)) * 8) / 4) := by
  unfold decodeGnuHash readU32Array
  simp [buildArray_size]

/-- Chain count in `decodeGnuHash` is
    `(sz - 16 - bloomCount * 8 - bucketCount * 4) / 4` (no `min` — fills
    the remaining window). -/
@[simp] theorem decodeGnuHash_chain_size (bs : ByteArray) (off sz : Nat) :
    (decodeGnuHash bs off sz).chain.size =
      (sz - 16
        - (min (readU32 bs (off + 8)).toNat ((sz - 16) / 8)) * 8
        - (min (readU32 bs off).toNat
            ((sz - 16 - (min (readU32 bs (off + 8)).toNat ((sz - 16) / 8)) * 8) / 4)) * 4) / 4 := by
  unfold decodeGnuHash readU32Array
  simp [buildArray_size]

end Patchelf.Elf.Decode
