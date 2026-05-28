/-
  RelocRemap — apply a dynsym permutation to the r_info fields of
  every SHT_REL / SHT_RELA section in a byte-layer ElfFile.

  Used after `gnuHashRebuildOp` reorders dynsym: every relocation that
  named an old dynsym index in `[firstSymIdx, end)` must be rewritten
  to point at the new index.  The C++ analogue is the `for (auto &
  shdr : shdrs) { ... changeRelocTableSymIds(...) }` block in
  `patchelf.cc:2144`.

  This module operates on RAW section bytes (not the typed algebra)
  because relocations flow as `SectionContent.raw` at the byte layer
  — we don't model them structurally.
-/
module

public import Patchelf.Elf.ElfFile
public import Patchelf.Elf.Basic
public import Patchelf.Elf.SectionOps
public import Patchelf.Elf.Splice
public import Patchelf.Elf.Reader
public import Patchelf.Elf.Writer

@[expose] public section

namespace Patchelf.Elf

namespace RelocRemap

/-- Remap a single dynsym index using the permutation `(firstSymIdx, perm)`:
    indices `< firstSymIdx` are unchanged; `firstSymIdx + k` becomes
    `firstSymIdx + perm[k]` (for `k < perm.size`); out-of-range
    indices are left as-is (defensive — matches C++ behavior on
    malformed binaries). -/
@[inline] def remapSymIdx (firstSymIdx : Nat) (perm : Array Nat) (idx : UInt32) : UInt32 :=
  let n := idx.toNat
  if n < firstSymIdx then idx
  else
    let k := n - firstSymIdx
    if h : k < perm.size then
      (firstSymIdx + (perm[k]'h)).toUInt32
    else idx

/-- Rewrite the r_info field of one ELF64 Rel/Rela entry: extract the
    symbol index (high 32 bits), apply the permutation, recombine with
    the type (low 32 bits). -/
@[inline] def rewriteRInfo (firstSymIdx : Nat) (perm : Array Nat) (rInfo : UInt64) : UInt64 :=
  let symIdx : UInt32 := (rInfo >>> 32).toUInt32
  let relType : UInt32 := rInfo.toUInt32
  let newSymIdx := remapSymIdx firstSymIdx perm symIdx
  (newSymIdx.toUInt64 <<< 32) ||| relType.toUInt64

/-- Remap symbol indices in a SHT_REL section's raw bytes (16 bytes per
    entry: r_offset @ 0, r_info @ 8). -/
def remapRelBytes (firstSymIdx : Nat) (perm : Array Nat) (bs : ByteArray) : ByteArray := Id.run do
  let mut out := bs
  let n := bs.size / 16
  let mut i : Nat := 0
  while i < n do
    let off := i * 16
    -- Read r_info at off+8.
    if hOff : off + 16 ≤ out.size then
      let rInfo := Reader.readU64 out (off + 8)
      let new := rewriteRInfo firstSymIdx perm rInfo
      -- Splice 8 bytes of new r_info at off+8.
      out := Encoder.splice out (off + 8) (Writer.writeU64 new)
    i := i + 1
  return out

/-- Remap symbol indices in a SHT_RELA section's raw bytes (24 bytes
    per entry: r_offset @ 0, r_info @ 8, r_addend @ 16).  Same r_info
    layout as Rel; we just step by 24 bytes. -/
def remapRelaBytes (firstSymIdx : Nat) (perm : Array Nat) (bs : ByteArray) : ByteArray := Id.run do
  let mut out := bs
  let n := bs.size / 24
  let mut i : Nat := 0
  while i < n do
    let off := i * 24
    if hOff : off + 24 ≤ out.size then
      let rInfo := Reader.readU64 out (off + 8)
      let new := rewriteRInfo firstSymIdx perm rInfo
      out := Encoder.splice out (off + 8) (Writer.writeU64 new)
    i := i + 1
  return out

end RelocRemap

/-- Apply a dynsym permutation to every SHT_REL / SHT_RELA section in
    `e.sections`.  Walks sections by `s.type`; for matching sections,
    decodes the entries' r_info, remaps the symbol index, and writes
    back via `updateSectionContent`.  Sections of other types are
    left untouched.

    No-op when `permOpt = none` (e.g. when `gnuHashRebuildOp` had
    nothing to rebuild). -/
def ElfFile.remapRelocs (e : ElfFile) (permOpt : Option (Nat × Array Nat)) : ElfFile :=
  match permOpt with
  | none => e
  | some (firstSymIdx, perm) => Id.run do
    let mut out := e
    let mut i : Nat := 0
    while h : i < out.sections.size do
      let s := out.sections[i]'h
      match s.content with
      | .raw ty hOk bs =>
        if ty = Layout.ShType.SHT_REL then
          let newBs := RelocRemap.remapRelBytes firstSymIdx perm bs
          out := out.updateSectionContent i (.raw ty hOk newBs)
        else if ty = Layout.ShType.SHT_RELA then
          let newBs := RelocRemap.remapRelaBytes firstSymIdx perm bs
          out := out.updateSectionContent i (.raw ty hOk newBs)
        else pure ()
      | _ => pure ()
      i := i + 1
    return out

end Patchelf.Elf
