/-
  Minimal header parsing shared between the byte-layer parser and
  any caller that needs a `ParseError`.
-/

import Patchelf.Elf.Basic
import Patchelf.Elf.Layout
import Patchelf.Elf.Reader
import Patchelf.Elf.Decode
import Patchelf.Elf.Schemas

namespace Patchelf.Elf

open Layout

/-- Parse-time errors. -/
inductive ParseError
  | tooShort (expected : Nat) (actual : Nat)
  | badMagic
  | not64Bit
  | notLittleEndian
  | badPhentsize (got : UInt16)
  | badShentsize (got : UInt16)
  | phdrsOutOfBounds
  | shdrsOutOfBounds
  | badShstrndx (idx : UInt16) (sectionCount : UInt16)
  | shstrtabNotStrtab
  | shstrtabNotNullTerminated
  | dynstrNotNullTerminated
  | dynamicMissingNull
  | dynamicOffsetOutOfBounds
  | dynsymOffsetOutOfBounds
  | sectionBytesOutOfBounds (shIdx : Nat)
  | badEntsize (shIdx : Nat) (expected : Nat) (got : Nat)
  | shdr0NotNull
  | shdrIdxMismatch
  | shdrIdxAliased
  | sectionSizeMismatch
  | phdrSlotOutOfBounds (phIdx : Nat)
  | sectionTooSmall (shIdx : Nat) (minSize : Nat) (actual : Nat)
  | sectionNobits (shIdx : Nat)
  | dynamicEntsizeZero
  | dynsymEntsizeZero
  | badClass
  | badData
  | badVersion
  deriving Repr

namespace Parse

/-- Decode + validate the ELF header.

    Refactored from a `do`-block to an explicit if-then-else cascade
    so callers can extract validation facts via successive
    `by_cases + rw [if_*]` walks (do-blocks elaborate to lambda
    continuations that resist this).  Semantics unchanged; the
    success/error pattern matches the previous implementation.

    See `Parser.lean`'s `parse` for the do-block-style consumer that
    uses `parseHeader` via `←`. -/
def parseHeader (bs : ByteArray) : Except ParseError ElfHeader :=
  if hSize : bs.size < Layout.ehdrSize then
    .error (.tooShort (expected := Layout.ehdrSize) (actual := bs.size))
  else
    have hDec : 0 + 64 ≤ bs.size := by
      have hEhdr : Layout.ehdrSize = 64 := rfl
      have := Nat.le_of_not_lt hSize
      omega
    have h16 : 0 + 16 ≤ bs.size := by omega
    let di := Decode.decodeIdent bs 0 h16
    if ¬ di.magicOk then .error .badMagic
    else if di.classByte ≠ Layout.ElfClass.elf64.encode then .error .not64Bit
    else if di.dataByte ≠ Layout.ElfData.lsb.encode then .error .notLittleEndian
    else
      let h := Decode.decodeHeader bs 0 hDec
      if h.phentsize.toNat ≠ Layout.phdrSize then
        .error (.badPhentsize (got := h.phentsize))
      else if h.shentsize.toNat ≠ Layout.shdrSize then
        .error (.badShentsize (got := h.shentsize))
      else if h.phoff.val + h.phnum.toNat * h.phentsize.toNat > bs.size then
        .error .phdrsOutOfBounds
      else if h.shoff.val + h.shnum.toNat * h.shentsize.toNat > bs.size then
        .error .shdrsOutOfBounds
      else if h.shstrndx.toNat ≥ h.shnum.toNat then
        .error (.badShstrndx (idx := h.shstrndx) (sectionCount := h.shnum))
      else
        .ok h

end Parse
end Patchelf.Elf
