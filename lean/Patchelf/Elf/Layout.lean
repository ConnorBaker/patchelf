/-
  ELF64 LE layout constants. Pure data; shared by Reader, Writer, Parser, Encoder.

  Every category of constant gets its own wrapper type so that, e.g., a
  phdr-type code can't be accidentally compared to an shdr-type code,
  or a fixed section size confused with a byte offset.
-/

namespace Patchelf.Elf.Layout

/-! ## Semantic wrappers for 64-bit quantities

    ELF spreads `UInt64` across several semantically incompatible roles:
    file offsets, virtual addresses, byte sizes, alignment powers.
    Treating them as the same type is the primary source of patchelf-
    adjacent bugs. Wrap each so the type system enforces their disjoint
    algebras.

    Each wrapper exposes `.val : Nat`; there is no `Coe` between them.

    `val` is `Nat` (not `UInt64`) so layout-engine and offset arithmetic
    work in unbounded naturals; the wire layer (`writeU64` / `readU64`)
    is the only place where the `< 2^64` fit constraint shows up, and
    it lives in the `EncodePreconditions` / parser-derived facts there. -/

/-- A byte offset from the start of the file. -/
structure FileOffset where val : Nat deriving DecidableEq, Repr
/-- A virtual memory address at load time. -/
structure VirtualAddr where val : Nat deriving DecidableEq, Repr
/-- A physical address (usually 0 on modern systems; kept for roundtrip). -/
structure PhysicalAddr where val : Nat deriving DecidableEq, Repr
/-- A length in bytes. -/
structure ByteSize where val : Nat deriving DecidableEq, Repr
/-- An alignment constraint (power of 2, or 0 / 1 meaning "no alignment"). -/
structure Alignment where val : Nat deriving DecidableEq, Repr
-- Note: no separate string-table-offset wrapper exists.
-- `SectionHeader.name` is a 32-bit offset into `.shstrtab`;
-- `DynEntry.value` (for DT_NEEDED etc.) is a 64-bit offset into
-- `.dynstr`.  Both are stored as raw primitives.  An earlier design
-- planned a `StrtabOffset`/`DynValue` wrapper pair; the work was
-- absorbed into the typed-section algebra (DynamicSection's
-- string-ref fields are `Fin ds.size` and the byte-layer offsets are
-- raw `UInt32` / `UInt64`), so the wrappers were not introduced.

/-! ## Fixed byte sizes (ELF64) -/

/-- Byte size of one ELF header. -/
def ehdrSize     : Nat := 64
/-- Byte size of one program header entry. -/
def phdrSize     : Nat := 56
/-- Byte size of one section header entry. -/
def shdrSize     : Nat := 64
/-- Byte size of one dynamic-table entry. -/
def dynEntrySize : Nat := 16
/-- Byte size of one symbol-table entry. -/
def symEntrySize : Nat := 24

/-! ## e_ident indices

    Positions within the 16-byte `e_ident` array. -/

def EI_MAG0       : Nat := 0
def EI_MAG1       : Nat := 1
def EI_MAG2       : Nat := 2
def EI_MAG3       : Nat := 3
def EI_CLASS      : Nat := 4
def EI_DATA       : Nat := 5
def EI_VERSION    : Nat := 6
def EI_OSABI      : Nat := 7
def EI_ABIVERSION : Nat := 8
def EI_NIDENT     : Nat := 16

/-- "\x7fELF" magic (bytes 0..3 of e_ident). -/
def magic : ByteArray := ⟨#[0x7f, 0x45, 0x4c, 0x46]⟩

/-! ## e_ident byte values

    Small enums for the non-OSABI bytes inside e_ident. -/

/-- `EI_CLASS` byte values. -/
inductive ElfClass | elf32 | elf64 | raw (b : UInt8)
  deriving DecidableEq, Repr

def ElfClass.encode : ElfClass → UInt8
  | .elf32 => 1
  | .elf64 => 2
  | .raw b => b

/-- `EI_DATA` byte values (endian). -/
inductive ElfData | lsb | msb | raw (b : UInt8)
  deriving DecidableEq, Repr

def ElfData.encode : ElfData → UInt8
  | .lsb   => 1
  | .msb   => 2
  | .raw b => b

/-! ## Field offsets inside the fixed-size structs

    Each offset is a byte position within a single header's bytes. The
    enum `Ehdr`/`Phdr`/`Shdr`/`Sym` + the `byteOffset` functions give
    readable call sites (`Ehdr.phoff.byteOffset` vs. a magic `32`). The
    Nat return type is intentional; all callers immediately arithmetic
    on the offset. -/

/-- Named ELF-header field. -/
inductive Ehdr
  | ident | objType | machine | version | entry | phoff | shoff | flags
  | ehsize | phentsize | phnum | shentsize | shnum | shstrndx
  deriving DecidableEq, Repr

/-- Byte offset of the named field within the ELF header. -/
def Ehdr.byteOffset : Ehdr → Nat
  | .ident     => 0
  | .objType   => 16
  | .machine   => 18
  | .version   => 20
  | .entry     => 24
  | .phoff     => 32
  | .shoff     => 40
  | .flags     => 48
  | .ehsize    => 52
  | .phentsize => 54
  | .phnum     => 56
  | .shentsize => 58
  | .shnum     => 60
  | .shstrndx  => 62

/-- Named program-header field. -/
inductive Phdr
  | type | flags | offset | vaddr | paddr | filesz | memsz | align
  deriving DecidableEq, Repr

def Phdr.byteOffset : Phdr → Nat
  | .type   => 0
  | .flags  => 4
  | .offset => 8
  | .vaddr  => 16
  | .paddr  => 24
  | .filesz => 32
  | .memsz  => 40
  | .align  => 48

/-- Named section-header field. -/
inductive Shdr
  | name | type | flags | addr | offset | size | link | info | addralign | entsize
  deriving DecidableEq, Repr

def Shdr.byteOffset : Shdr → Nat
  | .name      => 0
  | .type      => 4
  | .flags     => 8
  | .addr      => 16
  | .offset    => 24
  | .size      => 32
  | .link      => 40
  | .info      => 44
  | .addralign => 48
  | .entsize   => 56

/-- Named dynsym-entry field (Elf64_Sym, 24 bytes). -/
inductive Sym
  | st_name | st_info | st_other | st_shndx | st_value | st_size
  deriving DecidableEq, Repr

def Sym.byteOffset : Sym → Nat
  | .st_name  => 0
  | .st_info  => 4
  | .st_other => 5
  | .st_shndx => 6
  | .st_value => 8
  | .st_size  => 16

/-- Byte size of one `.gnu.version_r` Verneed header (ELF64, 16 bytes).
    The associated Vernaux entries follow in memory, not bundled. -/
def verneedSize : Nat := 16

/-- Byte size of one `.gnu.version_r` Vernaux entry (ELF64, 16 bytes). -/
def vernauxSize : Nat := 16

/-- Named Verneed field (Elf64_Verneed). Distinct from the record type
    `Patchelf.Elf.Verneed` defined in `Basic.lean`. -/
inductive VerneedField
  | vn_version | vn_cnt | vn_file | vn_aux | vn_next
  deriving DecidableEq, Repr

def VerneedField.byteOffset : VerneedField → Nat
  | .vn_version => 0
  | .vn_cnt     => 2
  | .vn_file    => 4
  | .vn_aux     => 8
  | .vn_next    => 12

/-- Named Vernaux field (Elf64_Vernaux). -/
inductive VernauxField
  | vna_hash | vna_flags | vna_other | vna_name | vna_next
  deriving DecidableEq, Repr

def VernauxField.byteOffset : VernauxField → Nat
  | .vna_hash  => 0
  | .vna_flags => 4
  | .vna_other => 6
  | .vna_name  => 8
  | .vna_next  => 12

/-! ## Type codes

    Section-header `sh_type`, program-header `p_type`, and dynamic-table
    `d_tag` share the same 32-bit encoding in ELF but live in disjoint
    semantic namespaces. Wrap each so code can't compare an `SHT_*` to
    a `PT_*` even though both decode to `UInt32`. -/

/-- `sh_type` code. -/
structure ShType where raw : UInt32 deriving DecidableEq, Repr
/-- `p_type` code. -/
structure PhType where raw : UInt32 deriving DecidableEq, Repr

namespace ShType
def SHT_NULL     : ShType := ⟨0⟩
def SHT_PROGBITS : ShType := ⟨1⟩
def SHT_SYMTAB   : ShType := ⟨2⟩
def SHT_STRTAB   : ShType := ⟨3⟩
def SHT_RELA     : ShType := ⟨4⟩
def SHT_HASH     : ShType := ⟨5⟩
def SHT_DYNAMIC  : ShType := ⟨6⟩
def SHT_NOTE     : ShType := ⟨7⟩
def SHT_NOBITS   : ShType := ⟨8⟩
def SHT_REL      : ShType := ⟨9⟩
def SHT_DYNSYM   : ShType := ⟨11⟩
/-- `.gnu.hash` (GNU-specific). -/
def SHT_GNU_HASH   : ShType := ⟨0x6ffffff6⟩
/-- `.gnu.version_r` (verneed table). -/
def SHT_GNU_VERNEED : ShType := ⟨0x6ffffffe⟩
/-- `.gnu.version` (symbol versioning table, `versym`). -/
def SHT_GNU_VERSYM  : ShType := ⟨0x6fffffff⟩
end ShType

namespace PhType
def PT_NULL         : PhType := ⟨0⟩
def PT_LOAD         : PhType := ⟨1⟩
def PT_DYNAMIC      : PhType := ⟨2⟩
def PT_INTERP       : PhType := ⟨3⟩
def PT_NOTE         : PhType := ⟨4⟩
def PT_SHLIB        : PhType := ⟨5⟩
def PT_PHDR         : PhType := ⟨6⟩
def PT_TLS          : PhType := ⟨7⟩
def PT_GNU_STACK    : PhType := ⟨0x6474e551⟩
def PT_GNU_RELRO    : PhType := ⟨0x6474e552⟩
def PT_GNU_EH_FRAME : PhType := ⟨0x6474e550⟩
end PhType

/-! ## Program-header flag bits (p_flags) -/

/-- `p_flags` bitmask: execute permission. -/
def PF_X : UInt32 := 0x1
/-- `p_flags` bitmask: write permission. -/
def PF_W : UInt32 := 0x2
/-- `p_flags` bitmask: read permission. -/
def PF_R : UInt32 := 0x4

/-- Read-only mapping (no write, no execute). -/
def PF_R_ONLY : UInt32 := PF_R
/-- Read-write mapping (for .dynamic). -/
def PF_RW : UInt32 := PF_R ||| PF_W

/-! ## Alignment utilities

    Used by the layout engine's size-and-offset math. `roundUp`
    satisfies the page-alignment constraints that ELF loaders enforce
    via `p_align`. -/

/-- Round `n` up to the next multiple of `align`. Requires `align ≥ 1`;
    when `align = 0` returns `n` unchanged (degenerate case). -/
def roundUp (n align : Nat) : Nat :=
  if align = 0 then n else (n + align - 1) / align * align

end Patchelf.Elf.Layout
