/-
  Pre-write validator: refuse to write a non-loadable binary.

  The encoder pipeline (`growEOF` + `syncDtAddrTagsInFile`) handles
  the common ET_DYN cases, but corner cases (e.g. binaries with a
  large BSS in the last PT_LOAD, like coreutils `ls`) fall back to
  `layoutForEncoding`'s repack — which doesn't preserve PT_LOAD
  coverage and produces bytes the kernel rejects at exec.

  This module is the safety net: it re-parses the post-encode bytes,
  decidably checks loader coherence (PT_LOAD congruence, every
  SHF_ALLOC section in some PT_LOAD's file range, agreement of
  PT_INTERP/PT_DYNAMIC offsets), and surfaces a structured failure
  on any violation.  The CLI wires it in front of every write so a
  failed validation is `exit nonzero, file unchanged on disk`.
-/
module

public import Patchelf.Elf.ElfFile
public import Patchelf.Elf.Parser

@[expose] public section

namespace Patchelf.Elf

/-- Per-clause failure reason for a refused write. -/
inductive ValidateFailure : Type
  /-- Output bytes don't even parse — encoder is broken. -/
  | parseFailed (err : ParseError)
  /-- Byte-level invariant failed (bad ident bytes, malformed shdr,
      etc.). -/
  | isValidFailed
  /-- Sections overlap each other or shdr table. -/
  | sectionsOverlapping
  /-- A PT_LOAD's `(p_offset, p_vaddr)` aren't congruent mod
      `p_align`.  Kernel rejects. -/
  | segmentCongruenceFailed
  /-- PT_INTERP / PT_DYNAMIC offsets don't match their section. -/
  | ptInterpAgreementFailed
  | ptDynamicAgreementFailed
  /-- A non-NOBITS section is outside every PT_LOAD's file range —
      the kernel won't mmap those bytes. -/
  | sectionFileOutsidePtLoad (sectionIdx : Nat)
  deriving Repr

/-- Render a validate failure for `--help`-shaped stderr. -/
def ValidateFailure.message : ValidateFailure → String
  | .parseFailed e             => s!"output bytes failed to parse: {repr e}"
  | .isValidFailed             => "output bytes failed byte-level validity (IsValid)"
  | .sectionsOverlapping       => "output sections overlap each other or the section header table"
  | .segmentCongruenceFailed   =>
      "PT_LOAD offset/vaddr congruence failed (kernel will reject this binary)"
  | .ptInterpAgreementFailed   => "PT_INTERP phdr offset doesn't match .interp section"
  | .ptDynamicAgreementFailed  => "PT_DYNAMIC phdr offset doesn't match .dynamic section"
  | .sectionFileOutsidePtLoad i =>
      s!"section {i}'s file range is outside every PT_LOAD's file range " ++
      "(this binary will SIGSEGV at exec)"

/-- Find the first section index whose file range is outside every
    PT_LOAD.  Returns `none` only when every section is covered. -/
def firstOutOfLoadSection (e : ElfFile) : Option Nat :=
  Nat.fold e.sections.size (init := none) fun i hi acc =>
    match acc with
    | some _ => acc
    | none   =>
      if decide (ElfFile.sectionInSomePtLoad e i hi) then none else some i

/-- Run all validation clauses on a parsed `ElfFile`.  Returns the
    first failure or `.ok ()`. -/
def validateElfFile (e : ElfFile) : Except ValidateFailure Unit :=
  if !decide e.IsValid then .error .isValidFailed
  else if !decide e.sectionsNonOverlapping then .error .sectionsOverlapping
  else if !decide e.shdrSectionDisjoint then .error .sectionsOverlapping
  else if !decide e.ptInterpAgreement then .error .ptInterpAgreementFailed
  else if !decide e.ptDynamicAgreement then .error .ptDynamicAgreementFailed
  else if !decide e.segmentCongruence then .error .segmentCongruenceFailed
  else
    match firstOutOfLoadSection e with
    | some i => .error (.sectionFileOutsidePtLoad i)
    | none   => .ok ()

/-- Top-level: parse output bytes and run validation. -/
def validateBytes (bs : ByteArray) : Except ValidateFailure Unit :=
  match parse bs with
  | .error e => .error (.parseFailed e)
  | .ok pe   => validateElfFile pe.elf

/-- Decidable predicate: output bytes are loadable.  This is the
    Prop-level statement of "this won't SIGSEGV at exec." -/
def IsLoadableBytes (bs : ByteArray) : Prop :=
  match parse bs with
  | .error _ => False
  | .ok pe   =>
      pe.elf.IsLoadable ∧ pe.elf.shdrSectionDisjoint ∧
      pe.elf.sectionFileInSomePtLoad

instance (bs : ByteArray) : Decidable (IsLoadableBytes bs) := by
  unfold IsLoadableBytes
  split <;> exact inferInstance

end Patchelf.Elf
