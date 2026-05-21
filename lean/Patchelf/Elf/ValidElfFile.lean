/-
  ValidElfFile — typed ELF file with compile-time cross-section
  invariants.

  Domain-modeled sections are named Option fields; unmodeled
  sections (text/data/rela/note/…) are carried by the byte-layer
  `ElfFile` template via the Adapter (not stored here).  This
  matches how patchelf actually operates: it never examines
  opaque sections, only routes them through the wire format
  unchanged.

  Design invariants ENFORCED AT THE TYPE LEVEL (not post-hoc
  validated):
    * `dynstr : StringSection` — null-termination via
      `StringSection.wf`
    * `dynamic : Option (DynamicSection dynstr)` — string-ref
      offsets are `Fin dynstr.size` by construction; bounds
      trivially hold
    * `dynsym : Option (SymbolSection dynstr)` —
      `st_name : Fin dynstr.size`
    * DT_STRTAB / DT_SYMTAB / DT_HASH / DT_GNU_HASH / DT_VERNEED
      are NOT fields — they're derived at encode time from
      `LayoutCtx`
    * DT_STRSZ is NOT a field — derived from `dynstr.bytes.size`

  Eliminated from the byte layer's `IsValid` (vacuous by
  construction here):
    * `sectionsAtDistinctTypes` / `namedSectionsUnique`
      (named fields)
    * `dynamicWellFormed` bounds / `dynsymNamesInBounds` (Fin-typed)
    * `strtabsWellFormed` (StringSection's wf field)
    * `dynStrszCoherent` / `dynAddressCoherentForTag × 5`
      (derived at encode)
-/
module

public import Patchelf.Elf.StringSection
public import Patchelf.Elf.DynamicSection
public import Patchelf.Elf.SymbolSection
public import Patchelf.Elf.AuxSections
public import Patchelf.Elf.InterpSection
public import Patchelf.Elf.Basic

@[expose] public section

namespace Patchelf.Elf

open Patchelf.Elf (ElfHeader ProgramHeader SectionHeader)

/-- Full typed ELF file. -/
structure ValidElfFile where
  /-- ELF header — preserved verbatim. -/
  header    : ElfHeader

  /-- Program headers (PT_LOAD / PT_GNU_STACK / …).  PT_INTERP and
      PT_DYNAMIC are preserved here for offset-sync purposes; their
      file offsets are re-derived at encode time from corresponding
      section offsets. -/
  phdrs     : Array ProgramHeader

  /-- Dynamic string table.  Empty for statically-linked ELFs. -/
  dynstr    : StringSection

  /-- `.dynsym` — dynamic symbol table. -/
  dynsym    : Option (SymbolSection dynstr)

  /-- `.dynamic` — typed dynamic entries. -/
  dynamic   : Option (DynamicSection dynstr)

  /-- `.gnu.version` — one UInt16 per dynsym symbol.  We require
      `dynsym.isSome ∧ versym.size = dynsym.symbols.size` at parse time,
      but store as a bare array here to avoid dependent-Option
      complications. -/
  versym    : Option (Array UInt16)

  /-- `.gnu.version_r`. -/
  verneed   : Option VerneedSection

  /-- SysV `.hash`. -/
  sysvHash  : Option SysVHashSection

  /-- `.gnu.hash`. -/
  gnuHash   : Option GnuHashSection

  /-- `.interp`. -/
  interp    : Option InterpSection

  deriving Repr

namespace ValidElfFile

/-! ## Atomic section mutation helpers -/

/-- Append a string to `.dynstr`; rebase all dependent sections.
    Returns the new ValidElfFile + the typed offset of the appended
    string in the new dynstr. -/
def growDynstr (e : ValidElfFile) (s : String) :
    ValidElfFile × Fin (e.dynstr.append s).1.size :=
  let ds' := (e.dynstr.append s).1
  let h : StringSection.SizeLE e.dynstr ds' := StringSection.size_le_append e.dynstr s
  let e' : ValidElfFile :=
    { header   := e.header
    , phdrs    := e.phdrs
    , dynstr   := ds'
    , dynsym   := e.dynsym.map (·.rebase h)
    , dynamic  := e.dynamic.map (·.rebase h)
    , versym   := e.versym
    , verneed  := e.verneed
    , sysvHash := e.sysvHash
    , gnuHash  := e.gnuHash
    , interp   := e.interp }
  (e', e.dynstr.appendOffset s)

/-- Replace the interpreter path. -/
def setInterp (e : ValidElfFile) (path : String) : ValidElfFile :=
  { e with interp := some (InterpSection.ofString path) }

/-- Modify the OS/ABI byte in the ELF header's ident block. -/
def setOsAbi (e : ValidElfFile) (abi : Patchelf.Elf.OsAbi) : ValidElfFile :=
  { e with header := { e.header with ident := { e.header.ident with osAbi := abi } } }

end ValidElfFile

end Patchelf.Elf
