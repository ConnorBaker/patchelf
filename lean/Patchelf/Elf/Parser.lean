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
module

public import Patchelf.Elf.ElfFile
public import Patchelf.Elf.Layout
public import Patchelf.Elf.Reader
public import Patchelf.Elf.Decode
public import Patchelf.Elf.Schemas
public import Patchelf.Elf.ParseHeader

@[expose] public section

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
  -- Dispatch on sh.type; each branch produces the matching SectionContent constructor.
  -- For the raw branch (else), `sh.type.isStructural = false` holds because all 5
  -- structural types were handled above — we produce the proof via `decide`.
  if h1 : sh.type = ShType.SHT_NOBITS then
    SectionContent.nobits sz
  else if h2 : sh.type = ShType.SHT_STRTAB then
    SectionContent.strtab (decodeStringTable bs off sz)
  else if h3 : sh.type = ShType.SHT_DYNAMIC then
    SectionContent.dynamic (decodeDynamic bs off (sz / Layout.dynEntrySize))
  else if h4 : sh.type = ShType.SHT_DYNSYM then
    SectionContent.dynsym (decodeDynsym bs off (sz / Layout.symEntrySize))
  else if h5 : sh.type = ShType.SHT_GNU_VERSYM then
    SectionContent.versym (decodeVersym bs off (sz / 2))
  else
    -- All 5 structural-type guards failed: h1..h5 are negation hypotheses.
    SectionContent.raw sh.type
      (by
        unfold ShType.isStructural
        simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]
        exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩)
      (Reader.readBytes bs off sz)

/-- Decoded content's type matches the original `sh.type`.  By
    construction every dispatch branch produces a `SectionContent`
    whose `type` equals the input `sh.type` — for structural branches
    the hypothesis pins it down; for the `.raw` else branch the
    constructor stores `sh.type` directly. -/
@[simp] theorem decodeSectionContent_type (bs : ByteArray) (sh : SectionHeader) :
    (decodeSectionContent bs sh).type = sh.type := by
  unfold decodeSectionContent
  split
  · simp_all [SectionContent.type]
  · split
    · simp_all [SectionContent.type]
    · split
      · simp_all [SectionContent.type]
      · split
        · simp_all [SectionContent.type]
        · split
          · simp_all [SectionContent.type]
          · simp [SectionContent.type]

/-- Build a `Section` from a `SectionHeader` and the underlying bytes.
    The `type` field is gone from `Section` — it is now computed from
    `content` via `SectionContent.type`. -/
def sectionFromShdr (bs : ByteArray) (sh : SectionHeader) : Section :=
  { name      := sh.name
    flags     := sh.flags
    addr      := sh.addr
    offset    := sh.offset
    link      := sh.link
    info      := sh.info
    addralign := sh.addralign
    entsize   := sh.entsize
    content   := decodeSectionContent bs sh }

/-- `(sectionFromShdr bs sh).type = sh.type`. -/
@[simp] theorem sectionFromShdr_type (bs : ByteArray) (sh : SectionHeader) :
    (sectionFromShdr bs sh).type = sh.type := by
  show (sectionFromShdr bs sh).content.type = sh.type
  unfold sectionFromShdr
  exact decodeSectionContent_type bs sh

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
    `IsValid` check; on failure dispatches the failure to the
    matching per-clause `ParseError` variant via the if-then-else
    cascade below. -/
def parse (bs : ByteArray) : Except Patchelf.Elf.ParseError ParsedElf := do
  let h ← Patchelf.Elf.Parse.parseHeader bs
  let phdrs := Patchelf.Elf.Decode.decodePhdrs bs h.phoff.val h.phnum.toNat
  let shdrs := Patchelf.Elf.Decode.decodeShdrs bs h.shoff.val h.shnum.toNat
  let sections := sectionsFromShdrs bs shdrs
  let elf : ElfFile := { header := h, phdrs := phdrs, sections := sections }
  if hVal : elf.IsValid then
    return ⟨elf, hVal⟩
  else
    -- Per-clause classification: probe each decidable clause and
    -- return the first failing one's specific error.  This must
    -- exhaust all 8 `IsValid` clauses; if every clause holds, the
    -- decidable instance would have given `IsValid` and the else
    -- branch would not have fired, so the fall-through is dead.
    if ¬ elf.headerCountsConsistent then throw .headerCountsMismatch
    else if ¬ elf.sectionsWellFormed then throw .shdr0NotNull
    else if ¬ elf.strtabsWellFormed then throw .strtabMalformed
    else if ¬ elf.dynamicWellFormed then throw .dynamicWellFormedFailed
    else if ¬ elf.dynsymNamesInBounds then throw .dynsymOffsetOutOfBounds
    else if ¬ elf.sectionsContentWellFormed then throw .contentWellFormedFailed
    else if ¬ elf.sectionsAtDistinctTypes then throw .typesNotDistinct
    else if ¬ elf.namedSectionsUnique then throw .namesNotUnique
    else throw .shdrIdxMismatch  -- unreachable; kept for totality.

/-- Parsed ElfFile with `IsLoadable` evidence plus the two extra
    clauses (`shdrSectionDisjoint`, `sectionFileInSomePtLoad`) that
    `Validate.IsLoadableBytes` checks at write time.  Together these
    cover everything the kernel + glibc loader inspect: byte-level
    `IsValid` (8 clauses), section/segment overlap-freedom, PT_*
    agreement, segment congruence, and SHF_ALLOC coverage.

    `LoadableElfFile.toParsedElf` recovers the weaker `ParsedElf`
    bundle for callers that only need `IsValid`. -/
structure LoadableElfFile where
  elf            : ElfFile
  isLoadable     : elf.IsLoadable
  shdrSecDisjoint : elf.shdrSectionDisjoint
  secInSomeLoad  : elf.sectionFileInSomePtLoad

/-- Forget the loader-coherence proofs and recover a plain
    `ParsedElf`. -/
def LoadableElfFile.toParsedElf (le : LoadableElfFile) : ParsedElf :=
  ⟨le.elf, le.isLoadable.toIsValid⟩

/-- Parse + verify all loader-coherence clauses.  Strictly stronger
    than `parse`: returns a `LoadableElfFile` carrying the same
    proofs that `Validate.validateBytes` checks at write time.

    On `IsValid` failure: dispatches to the same per-clause
    `ParseError` variants as `parse`.  On `IsLoadable` failure (or
    one of the two extra clauses): returns a per-clause variant
    naming which loader-coherence invariant failed.

    Use this when downstream code wants the stronger static
    guarantee — e.g., op-level `_preserves_loadable` theorems in
    ROADMAP §1.2.  Existing CLI flows continue to use `parse`. -/
def parseLoadable (bs : ByteArray) :
    Except Patchelf.Elf.ParseError LoadableElfFile := do
  let pe ← parse bs
  let elf := pe.elf
  if hLoad : elf.IsLoadable then
    if hShdrSec : elf.shdrSectionDisjoint then
      if hSecLoad : elf.sectionFileInSomePtLoad then
        return ⟨elf, hLoad, hShdrSec, hSecLoad⟩
      else
        -- Find which section is outside every PT_LOAD.
        let idx := Nat.fold elf.sections.size (init := (0 : Nat)) (fun i hi acc =>
          if decide (ElfFile.sectionInSomePtLoad elf i hi) then acc else i)
        throw (.sectionFileOutsidePtLoad idx)
    else
      throw .shdrSectionsOverlapping
  else
    -- Per-clause IsLoadable failure.  Probe the four clauses in
    -- order; the IsValid base is already established (parse succeeded).
    if ¬ elf.sectionsNonOverlapping then throw .sectionsOverlapping
    else if ¬ elf.ptInterpAgreement then throw .ptInterpAgreementFailed
    else if ¬ elf.ptDynamicAgreement then throw .ptDynamicAgreementFailed
    else if ¬ elf.segmentCongruence then throw .segmentCongruenceFailed
    else throw .shdrIdxMismatch  -- unreachable; kept for totality.

end Patchelf.Elf
