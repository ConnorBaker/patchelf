/-
  Byte-layer parser: `ByteArray → Except ParseError ParsedElf`.

  Builds `sections : Array Section` directly by walking the shdr
  table and decoding each section's content per its SHT_* type:

    SHT_NOBITS        → SectionContent.nobits (no file bytes)
    SHT_STRTAB        → SectionContent.strtab (null-terminated bytes)
    SHT_DYNAMIC       → SectionContent.dynamic (Array DynEntry)
    SHT_DYNSYM        → SectionContent.dynsym (Array Symbol)
    SHT_GNU_VERSYM    → SectionContent.versym (Array UInt16)
    everything else   → SectionContent.raw (bytes verbatim)

  `.gnu.version_r` (SHT_GNU_VERNEED), SysV `.hash` (SHT_HASH), and
  `.gnu.hash` (SHT_GNU_HASH) sections are stored as `.raw` at the
  byte layer.  The typed-section algebra's `Adapter.ofElfFile`
  decodes them on demand for the typed-layer's read path; ops
  modify them via the typed layer, and the Adapter writes back to
  `.raw` bytes via the existing per-struct writers (`writeArray
  Verneed.write`, `SysVHashTable.write`, `GnuHashTable.write`).

  Uses fixed-layout decoders from `Schemas.lean` and variable-length
  decoders from `Decode.lean`. ELF header validation (magic, class,
  data, phentsize, shentsize, bounds) is via `Parse.parseHeader` in
  `ParseHeader.lean`. Validity is checked via the `Decidable
  IsValid` instance; on failure a generic `shdrIdxMismatch` is
  thrown (per-clause error classification is future work).
-/

import Patchelf.Elf.ElfFile
import Patchelf.Elf.Layout
import Patchelf.Elf.Reader
import Patchelf.Elf.Decode
import Patchelf.Elf.Schemas
import Patchelf.Elf.ParseHeader

namespace Patchelf.Elf

open Layout
open Patchelf.Elf (ElfHeader DynEntry DynTag Symbol Verneed SysVHashTable
                     GnuHashTable StringTable SectionHeader)
open Patchelf.Elf.Decode

/-! ## Section decoding dispatch -/

/-- Decode one section's content given its shdr and the underlying
    bytes. Structural decoders never fail; validation errors are
    raised at the `parse` top-level.

    Byte-layer policy: only sections that the typed-section algebra
    edits structurally get a typed `SectionContent` constructor at
    the byte layer.  Sections that are byte-verbatim through ops
    (`.gnu.version_r`, `.hash`, `.gnu.hash`) are stored as `.raw`;
    typed materialization happens in the Adapter.

    For SHT_NOBITS sections, content is `.nobits` regardless of shdr
    size (NOBITS has virtual-only size; no file bytes to read).
    For SHT_STRTAB, decode as `StringTable`.
    For SHT_DYNAMIC / SHT_DYNSYM / SHT_GNU_VERSYM, decode to the
    matching typed constructor.
    Everything else (including the demoted Verneed/SysVHash/GnuHash
    sections, and `.interp` as SHT_PROGBITS) becomes `.raw`. -/
def decodeSectionContent (bs : ByteArray) (sh : SectionHeader) :
    SectionContent :=
  let off := sh.offset.val
  let sz  := sh.size.val
  if sh.type = ShType.SHT_NOBITS then
    SectionContent.nobits
  else if sh.type = ShType.SHT_STRTAB then
    SectionContent.strtab (decodeStringTable bs off sz)
  else if sh.type = ShType.SHT_DYNAMIC then
    -- maxCount = section size / entry size
    SectionContent.dynamic (decodeDynamic bs off (sz / Layout.dynEntrySize))
  else if sh.type = ShType.SHT_DYNSYM then
    SectionContent.dynsym (decodeDynsym bs off (sz / Layout.symEntrySize))
  else if sh.type = ShType.SHT_GNU_VERSYM then
    SectionContent.versym (decodeVersym bs off (sz / 2))
  else
    SectionContent.raw (Reader.readBytes bs off sz)

/-- Build a `Section` from a `SectionHeader` and the underlying bytes. -/
def sectionFromShdr (bs : ByteArray) (sh : SectionHeader) : Section :=
  { name      := sh.name
    type      := sh.type
    flags     := sh.flags
    addr      := sh.addr
    offset    := sh.offset
    link      := sh.link
    info      := sh.info
    addralign := sh.addralign
    entsize   := sh.entsize
    content   := decodeSectionContent bs sh }

/-- Build the section array from the decoded shdr table. -/
def sectionsFromShdrs (bs : ByteArray) (shdrs : Array SectionHeader) :
    Array Section :=
  shdrs.map (sectionFromShdr bs)

/-! ## Top-level parse -/

/-- A parsed ElfFile bundled with its validity proof.  The
    byte-level parser's result type; downstream CLI/op code
    converts to `ValidElfFile` (the typed-section record) via
    `Adapter.ofElfFile`. -/
structure ParsedElf where
  elf : ElfFile
  isValid : elf.IsValid

/-- Parse a byte array into a validated pure-IR ElfFile.

    Reuses `Parse.parseHeader` (from `Elf/ParseHeader.lean`) for the
    fixed-layout header validation. Once header and shdrs are in hand,
    builds `sections` via `sectionsFromShdrs` and runs the decidable
    `IsValid` check; on failure raises a generic `shdrIdxMismatch`
    error (per-clause error classification is left as future work). -/
def parse (bs : ByteArray) : Except Patchelf.Elf.ParseError ParsedElf := do
  let h ← Patchelf.Elf.Parse.parseHeader bs
  let phdrs := Patchelf.Elf.Decode.decodePhdrs bs h.phoff.val h.phnum.toNat
  let shdrs := Patchelf.Elf.Decode.decodeShdrs bs h.shoff.val h.shnum.toNat
  let sections := sectionsFromShdrs bs shdrs
  let elf : ElfFile := { header := h, phdrs := phdrs, sections := sections }
  -- Runtime decidability check of IsValid: the decidable instance
  -- enumerates clauses; if any fails, we return a generic parse error.
  -- Proper per-clause error classification is deferred.
  if hVal : elf.IsValid then
    return ⟨elf, hVal⟩
  else
    -- Best-effort error classification: fall through to a generic
    -- error for now.  Per-clause classification (so callers see
    -- the specific IsValid violation) is tracked in
    -- `research/ROADMAP.md` §3.8.
    throw .shdrIdxMismatch

end Patchelf.Elf
