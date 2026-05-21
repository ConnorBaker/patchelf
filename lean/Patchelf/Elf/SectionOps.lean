/-
  Section content update on the byte-layer `ElfFile`.

  Used by `Adapter.toElfFile` (to splice typed-side mutations back
  into the byte-layer file) and by `Encoder.syncDtStrszInFile` (to
  rewrite `.dynamic`'s DT_STRSZ entry before encode).

  This file is intentionally small.  An earlier design carried
  `IsValid`-preservation infrastructure (per-clause lemmas +
  bundling theorems) for byte-layer section-content updates, but
  ops live on `ValidElfFile` and don't traverse byte-layer
  `IsValid` clauses; the preservation block had zero callers and
  was removed.  Today this file is `updateSectionContent` plus
  three `@[simp]` projection lemmas.
-/

import Patchelf.Elf.ElfFile

namespace Patchelf.Elf

/-- Update the content of the section at index `i`. Metadata (name,
    type, flags, addr, offset, link, info, addralign, entsize) is
    preserved. Out-of-bounds indices are no-ops. -/
def ElfFile.updateSectionContent (e : ElfFile) (i : Nat)
    (newContent : SectionContent) : ElfFile :=
  if h : i < e.sections.size then
    let updated := { (e.sections[i]'h) with content := newContent }
    { e with sections := e.sections.set i updated h }
  else e

@[simp] theorem ElfFile.updateSectionContent_header (e : ElfFile)
    (i : Nat) (c : SectionContent) :
    (e.updateSectionContent i c).header = e.header := by
  unfold updateSectionContent
  split <;> rfl

@[simp] theorem ElfFile.updateSectionContent_phdrs (e : ElfFile)
    (i : Nat) (c : SectionContent) :
    (e.updateSectionContent i c).phdrs = e.phdrs := by
  unfold updateSectionContent
  split <;> rfl

@[simp] theorem ElfFile.updateSectionContent_sections_size (e : ElfFile)
    (i : Nat) (c : SectionContent) :
    (e.updateSectionContent i c).sections.size = e.sections.size := by
  unfold updateSectionContent
  split <;> simp

end Patchelf.Elf
