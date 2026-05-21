/-
  Core ELF data types (shared across the byte layer and the
  typed-section algebra).

  Defines the record shapes for the ELF header + ident block
  (`ElfHeader`, `ElfIdent`, `OsAbi`), dynamic entries (`DynEntry`,
  `DynTag`), program / section headers (`ProgramHeader`,
  `SectionHeader`), dynamic symbols (`Symbol`), version-need
  entries (`Vernaux`, `Verneed`), and hash tables
  (`SysVHashTable`, `GnuHashTable`), plus string-table support
  (`StringTable`) and the SysV / GNU string hashes.

  64-bit LSB ELF only.  32-bit and big-endian support would
  require parameterizing every decoder over a size/endianness
  tag — straightforward but orthogonal.
-/

import Patchelf.Elf.Layout
import Std.Tactic.BVDecide

namespace Patchelf.Elf

-- ByteArray has no `Repr` in Lean 4.29 core. Derive it once here so
-- structures containing ByteArray can themselves derive Repr.
deriving instance Repr for ByteArray

/-- OS/ABI identifier (`e_ident[EI_OSABI]`, offset 7 in the ELF header).

    Canonical: `.raw b` requires `b ∉ {0, 3, 9}` so encoding is injective
    (no two `OsAbi` values share an encoded byte).  Construction goes
    through `OsAbi.ofByte`, which pattern-matches and produces the
    named constructor for known values. -/
inductive OsAbi
  | systemV                        -- 0
  | linux                          -- 3
  | freebsd                        -- 9
  | raw (byte : UInt8)
        (h : byte ≠ 0 ∧ byte ≠ 3 ∧ byte ≠ 9)
  deriving Repr

instance : DecidableEq OsAbi := fun a b =>
  match a, b with
  | .systemV, .systemV => isTrue rfl
  | .linux,   .linux   => isTrue rfl
  | .freebsd, .freebsd => isTrue rfl
  | .raw b₁ _, .raw b₂ _ =>
      if h : b₁ = b₂ then
        isTrue (by subst h; rfl)
      else
        isFalse (fun heq => h (by cases heq; rfl))
  -- Cross-constructor cases: never equal.
  | .systemV, .linux | .systemV, .freebsd | .systemV, .raw _ _
  | .linux, .systemV | .linux, .freebsd | .linux, .raw _ _
  | .freebsd, .systemV | .freebsd, .linux | .freebsd, .raw _ _
  | .raw _ _, .systemV | .raw _ _, .linux | .raw _ _, .freebsd =>
      isFalse (by intro h; cases h)

def OsAbi.encode : OsAbi → UInt8
  | .systemV       => 0
  | .linux         => 3
  | .freebsd       => 9
  | .raw b _       => b

/-- Smart constructor: convert a byte to the canonical `OsAbi`.
    Named values produce the matching named constructor; everything
    else produces `.raw b` with the disjointness witness.

    Replaces the previous `decode` function — same shape, but now
    exhausts the inductive's representable states. -/
def OsAbi.ofByte (b : UInt8) : OsAbi :=
  if h0 : b = 0 then .systemV
  else if h3 : b = 3 then .linux
  else if h9 : b = 9 then .freebsd
  else .raw b ⟨h0, h3, h9⟩

/-- `encode ∘ ofByte = id` on UInt8.  Each named branch's encode is the
    constant byte equal to the matched value; the catch-all returns the
    raw byte verbatim. -/
theorem OsAbi.encode_ofByte (b : UInt8) : (OsAbi.ofByte b).encode = b := by
  unfold OsAbi.ofByte
  by_cases h0 : b = 0
  · rw [dif_pos h0]; show (0 : UInt8) = b; exact h0.symm
  rw [dif_neg h0]
  by_cases h3 : b = 3
  · rw [dif_pos h3]; show (3 : UInt8) = b; exact h3.symm
  rw [dif_neg h3]
  by_cases h9 : b = 9
  · rw [dif_pos h9]; show (9 : UInt8) = b; exact h9.symm
  rw [dif_neg h9]
  rfl

/-- `ofByte ∘ encode = id` on `OsAbi`.  Forward direction — was
    impossible to prove on the un-canonicalized type because `.raw 0`
    and `.systemV` produced the same byte.  Now closes by case
    analysis: named constructors hit their matching `if` branch;
    `.raw b ⟨h0, h3, h9⟩` falls through to the catch-all because
    `b ≠ 0 ∧ b ≠ 3 ∧ b ≠ 9` blocks each preceding `if`. -/
theorem OsAbi.ofByte_encode (a : OsAbi) : OsAbi.ofByte a.encode = a := by
  cases a with
  | systemV => rfl
  | linux   => rfl
  | freebsd => rfl
  | raw b h =>
    obtain ⟨h0, h3, h9⟩ := h
    show OsAbi.ofByte b = .raw b ⟨h0, h3, h9⟩
    unfold OsAbi.ofByte
    rw [dif_neg h0, dif_neg h3, dif_neg h9]


/-- Human-readable name for a recognized ABI, else `0x<byte>` hex. -/
def OsAbi.display : OsAbi → String
  | .systemV   => "System V"
  | .linux     => "Linux"
  | .freebsd   => "FreeBSD"
  | .raw b _   => s!"0x{String.ofList (Nat.toDigits 16 b.toNat)}"

/-- The 16-byte `e_ident` array. Only the OS/ABI byte is mutable via patchelf;
    the rest we keep abstract as raw bytes. -/
structure ElfIdent where
  /-- Bytes 0-6 (magic + class + data + version): never modified by patchelf. -/
  head        : ByteArray
  osAbi       : OsAbi
  /-- Bytes 8-15 (ABI version + padding): never modified by patchelf. -/
  tail        : ByteArray
  head_size   : head.size = 7
  tail_size   : tail.size = 8
  deriving Repr

/-- ELF header (ELF64 subset sufficient for this prototype).

    `entry` is a virtual address; `phoff`/`shoff` are file offsets.
    Count/size fields stay as `UInt16`/`UInt32` — they're small enough
    that no semantic confusion arises, and they're read by every clause
    of `IsValid` as arithmetic. -/
structure ElfHeader where
  ident     : ElfIdent
  objType   : UInt16
  machine   : UInt16
  version   : UInt32
  entry     : Layout.VirtualAddr
  phoff     : Layout.FileOffset
  shoff     : Layout.FileOffset
  flags     : UInt32
  ehsize    : UInt16
  phentsize : UInt16
  phnum     : UInt16
  shentsize : UInt16
  shnum     : UInt16
  shstrndx  : UInt16
  deriving Repr

/-- Disjointness predicate for `DynTag.raw`: the tag value is not one
    of the 17 named codes.  Forbidding overlap makes encoding injective. -/
def DynTag.RawDisjoint (t : Int64) : Prop :=
  t ≠ 0 ∧ t ≠ 1 ∧ t ≠ 4 ∧ t ≠ 5 ∧ t ≠ 6 ∧ t ≠ 7 ∧ t ≠ 10 ∧
  t ≠ 14 ∧ t ≠ 15 ∧ t ≠ 17 ∧ t ≠ 21 ∧ t ≠ 23 ∧ t ≠ 29 ∧
  t ≠ 0x6ffffef5 ∧ t ≠ 0x6ffffff0 ∧ t ≠ 0x6ffffffb ∧ t ≠ 0x6ffffffe

instance : DecidablePred DynTag.RawDisjoint := by
  intro t; unfold DynTag.RawDisjoint; exact inferInstance

/-- Dynamic section tag. ELF64 `d_tag` is a signed 64-bit value; we
    enumerate the tags patchelf modifies.

    Canonical: `.raw t` requires `DynTag.RawDisjoint t` so encoding is
    injective.  Construction goes through `DynTag.decode`, which
    pattern-matches and produces named constructors for known values
    (see below). -/
inductive DynTag
  | null
  | needed
  | strtab
  | symtab
  | strsz
  | hash
  | soname
  | rpath
  | runpath
  | rela
  | rel
  | jmprel
  | versym
  | verneed
  | gnuHash
  | flags1
  | debug
  | raw (tag : Int64) (h : DynTag.RawDisjoint tag)
  deriving Repr

instance : DecidableEq DynTag := fun a b =>
  match a, b with
  | .null, .null | .needed, .needed | .strtab, .strtab | .symtab, .symtab
  | .strsz, .strsz | .hash, .hash | .soname, .soname | .rpath, .rpath
  | .runpath, .runpath | .rela, .rela | .rel, .rel | .jmprel, .jmprel
  | .versym, .versym | .verneed, .verneed | .gnuHash, .gnuHash
  | .flags1, .flags1 | .debug, .debug => isTrue rfl
  | .raw t₁ _, .raw t₂ _ =>
      if h : t₁ = t₂ then isTrue (by subst h; rfl)
      else isFalse (fun heq => h (by cases heq; rfl))
  | .null, .needed | .null, .strtab | .null, .symtab | .null, .strsz
  | .null, .hash | .null, .soname | .null, .rpath | .null, .runpath
  | .null, .rela | .null, .rel | .null, .jmprel | .null, .versym
  | .null, .verneed | .null, .gnuHash | .null, .flags1 | .null, .debug | .null, .raw _ _
  | .needed, .null | .needed, .strtab | .needed, .symtab | .needed, .strsz
  | .needed, .hash | .needed, .soname | .needed, .rpath | .needed, .runpath
  | .needed, .rela | .needed, .rel | .needed, .jmprel | .needed, .versym
  | .needed, .verneed | .needed, .gnuHash | .needed, .flags1 | .needed, .debug | .needed, .raw _ _
  | .strtab, .null | .strtab, .needed | .strtab, .symtab | .strtab, .strsz
  | .strtab, .hash | .strtab, .soname | .strtab, .rpath | .strtab, .runpath
  | .strtab, .rela | .strtab, .rel | .strtab, .jmprel | .strtab, .versym
  | .strtab, .verneed | .strtab, .gnuHash | .strtab, .flags1 | .strtab, .debug | .strtab, .raw _ _
  | .symtab, .null | .symtab, .needed | .symtab, .strtab | .symtab, .strsz
  | .symtab, .hash | .symtab, .soname | .symtab, .rpath | .symtab, .runpath
  | .symtab, .rela | .symtab, .rel | .symtab, .jmprel | .symtab, .versym
  | .symtab, .verneed | .symtab, .gnuHash | .symtab, .flags1 | .symtab, .debug | .symtab, .raw _ _
  | .strsz, .null | .strsz, .needed | .strsz, .strtab | .strsz, .symtab
  | .strsz, .hash | .strsz, .soname | .strsz, .rpath | .strsz, .runpath
  | .strsz, .rela | .strsz, .rel | .strsz, .jmprel | .strsz, .versym
  | .strsz, .verneed | .strsz, .gnuHash | .strsz, .flags1 | .strsz, .debug | .strsz, .raw _ _
  | .hash, .null | .hash, .needed | .hash, .strtab | .hash, .symtab
  | .hash, .strsz | .hash, .soname | .hash, .rpath | .hash, .runpath
  | .hash, .rela | .hash, .rel | .hash, .jmprel | .hash, .versym
  | .hash, .verneed | .hash, .gnuHash | .hash, .flags1 | .hash, .debug | .hash, .raw _ _
  | .soname, .null | .soname, .needed | .soname, .strtab | .soname, .symtab
  | .soname, .strsz | .soname, .hash | .soname, .rpath | .soname, .runpath
  | .soname, .rela | .soname, .rel | .soname, .jmprel | .soname, .versym
  | .soname, .verneed | .soname, .gnuHash | .soname, .flags1 | .soname, .debug | .soname, .raw _ _
  | .rpath, .null | .rpath, .needed | .rpath, .strtab | .rpath, .symtab
  | .rpath, .strsz | .rpath, .hash | .rpath, .soname | .rpath, .runpath
  | .rpath, .rela | .rpath, .rel | .rpath, .jmprel | .rpath, .versym
  | .rpath, .verneed | .rpath, .gnuHash | .rpath, .flags1 | .rpath, .debug | .rpath, .raw _ _
  | .runpath, .null | .runpath, .needed | .runpath, .strtab | .runpath, .symtab
  | .runpath, .strsz | .runpath, .hash | .runpath, .soname | .runpath, .rpath
  | .runpath, .rela | .runpath, .rel | .runpath, .jmprel | .runpath, .versym
  | .runpath, .verneed | .runpath, .gnuHash | .runpath, .flags1 | .runpath, .debug | .runpath, .raw _ _
  | .rela, .null | .rela, .needed | .rela, .strtab | .rela, .symtab
  | .rela, .strsz | .rela, .hash | .rela, .soname | .rela, .rpath
  | .rela, .runpath | .rela, .rel | .rela, .jmprel | .rela, .versym
  | .rela, .verneed | .rela, .gnuHash | .rela, .flags1 | .rela, .debug | .rela, .raw _ _
  | .rel, .null | .rel, .needed | .rel, .strtab | .rel, .symtab
  | .rel, .strsz | .rel, .hash | .rel, .soname | .rel, .rpath
  | .rel, .runpath | .rel, .rela | .rel, .jmprel | .rel, .versym
  | .rel, .verneed | .rel, .gnuHash | .rel, .flags1 | .rel, .debug | .rel, .raw _ _
  | .jmprel, .null | .jmprel, .needed | .jmprel, .strtab | .jmprel, .symtab
  | .jmprel, .strsz | .jmprel, .hash | .jmprel, .soname | .jmprel, .rpath
  | .jmprel, .runpath | .jmprel, .rela | .jmprel, .rel | .jmprel, .versym
  | .jmprel, .verneed | .jmprel, .gnuHash | .jmprel, .flags1 | .jmprel, .debug | .jmprel, .raw _ _
  | .versym, .null | .versym, .needed | .versym, .strtab | .versym, .symtab
  | .versym, .strsz | .versym, .hash | .versym, .soname | .versym, .rpath
  | .versym, .runpath | .versym, .rela | .versym, .rel | .versym, .jmprel
  | .versym, .verneed | .versym, .gnuHash | .versym, .flags1 | .versym, .debug | .versym, .raw _ _
  | .verneed, .null | .verneed, .needed | .verneed, .strtab | .verneed, .symtab
  | .verneed, .strsz | .verneed, .hash | .verneed, .soname | .verneed, .rpath
  | .verneed, .runpath | .verneed, .rela | .verneed, .rel | .verneed, .jmprel
  | .verneed, .versym | .verneed, .gnuHash | .verneed, .flags1 | .verneed, .debug | .verneed, .raw _ _
  | .gnuHash, .null | .gnuHash, .needed | .gnuHash, .strtab | .gnuHash, .symtab
  | .gnuHash, .strsz | .gnuHash, .hash | .gnuHash, .soname | .gnuHash, .rpath
  | .gnuHash, .runpath | .gnuHash, .rela | .gnuHash, .rel | .gnuHash, .jmprel
  | .gnuHash, .versym | .gnuHash, .verneed | .gnuHash, .flags1 | .gnuHash, .debug | .gnuHash, .raw _ _
  | .flags1, .null | .flags1, .needed | .flags1, .strtab | .flags1, .symtab
  | .flags1, .strsz | .flags1, .hash | .flags1, .soname | .flags1, .rpath
  | .flags1, .runpath | .flags1, .rela | .flags1, .rel | .flags1, .jmprel
  | .flags1, .versym | .flags1, .verneed | .flags1, .gnuHash | .flags1, .debug | .flags1, .raw _ _
  | .debug, .null | .debug, .needed | .debug, .strtab | .debug, .symtab
  | .debug, .strsz | .debug, .hash | .debug, .soname | .debug, .rpath
  | .debug, .runpath | .debug, .rela | .debug, .rel | .debug, .jmprel
  | .debug, .versym | .debug, .verneed | .debug, .gnuHash | .debug, .flags1 | .debug, .raw _ _
  | .raw _ _, .null | .raw _ _, .needed | .raw _ _, .strtab | .raw _ _, .symtab
  | .raw _ _, .strsz | .raw _ _, .hash | .raw _ _, .soname | .raw _ _, .rpath
  | .raw _ _, .runpath | .raw _ _, .rela | .raw _ _, .rel | .raw _ _, .jmprel
  | .raw _ _, .versym | .raw _ _, .verneed | .raw _ _, .gnuHash | .raw _ _, .flags1 | .raw _ _, .debug =>
      isFalse (by intro h; cases h)

/-- Codec for `DynTag`. The on-disk representation is a signed 64-bit
    value; values outside the enumerated set round-trip through `.raw`. -/
def DynTag.encode : DynTag → Int64
  | .null      => 0
  | .needed    => 1
  | .strtab    => 5
  | .symtab    => 6
  | .strsz     => 10
  | .hash      => 4
  | .soname    => 14
  | .rpath     => 15
  | .runpath   => 29
  | .rela      => 7
  | .rel       => 17
  | .jmprel    => 23
  | .versym    => 0x6ffffff0
  | .verneed   => 0x6ffffffe
  | .gnuHash   => 0x6ffffef5
  | .flags1    => 0x6ffffffb
  | .debug     => 21
  | .raw t _   => t

/-- Does this tag's `value` field carry a virtual address (vs. an
    offset, size, flag, or count)? The layout engine's
    `rewriteDynamicAddresses` pass must update these tags when their
    target section moves; non-address tags are left alone. -/
def DynTag.isAddressTag : DynTag → Bool
  | .strtab | .symtab | .hash | .rela | .rel | .jmprel
  | .versym | .verneed | .gnuHash => true
  | _ => false

/-- On-disk round-trip for `d_tag`: reading then re-writing preserves the
    bit pattern, even though the type signature flips Int64 ↔ UInt64.
    Lean's `.toUInt64` / `.toInt64` both preserve the 64-bit word. -/
theorem DynTag.encode_toUInt64_toInt64 (d : DynTag) :
    d.encode.toUInt64.toInt64 = d.encode := by
  cases d <;> rfl

/-- Decoder, exhaustively pattern-matching the 17 named codes.  The
    catch-all builds a `.raw t` with a `RawDisjoint t` witness derived
    from the failed equality checks above. -/
def DynTag.decode (t : Int64) : DynTag :=
  if h0 : t = 0 then .null
  else if h1 : t = 1 then .needed
  else if h4 : t = 4 then .hash
  else if h5 : t = 5 then .strtab
  else if h6 : t = 6 then .symtab
  else if h7 : t = 7 then .rela
  else if h10 : t = 10 then .strsz
  else if h14 : t = 14 then .soname
  else if h15 : t = 15 then .rpath
  else if h17 : t = 17 then .rel
  else if h21 : t = 21 then .debug
  else if h23 : t = 23 then .jmprel
  else if h29 : t = 29 then .runpath
  else if h_gh : t = 0x6ffffef5 then .gnuHash
  else if h_vs : t = 0x6ffffff0 then .versym
  else if h_f1 : t = 0x6ffffffb then .flags1
  else if h_vn : t = 0x6ffffffe then .verneed
  else .raw t ⟨h0, h1, h4, h5, h6, h7, h10, h14, h15, h17, h21, h23, h29, h_gh, h_vs, h_f1, h_vn⟩

/-- `DynTag.encode` is a right inverse of `DynTag.decode` at the `Int64`
    level: `(decode t).encode = t` for every `t : Int64`.  Each branch
    of the if-cascade either substitutes the matched constant (named
    case) or returns `.raw t` whose `.encode` is `t` definitionally.

    Note: this is NOT a decode-then-encode roundtrip starting from
    `DynTag` (which is `.decode_encode`).  This direction is the
    Int64-level identity; the canonicalization makes the other
    direction (`.encode_decode`) also true — see `decode_encode_dyntag`. -/
theorem DynTag.decode_encode (t : Int64) : (DynTag.decode t).encode = t := by
  -- Walk the 17-arm `dite` cascade.  Each arm: if discriminant matches,
  -- the named encoding is the matched constant; otherwise recurse.
  unfold DynTag.decode
  by_cases h0 : t = 0
  · rw [dif_pos h0]; subst h0; rfl
  rw [dif_neg h0]
  by_cases h1 : t = 1
  · rw [dif_pos h1]; subst h1; rfl
  rw [dif_neg h1]
  by_cases h4 : t = 4
  · rw [dif_pos h4]; subst h4; rfl
  rw [dif_neg h4]
  by_cases h5 : t = 5
  · rw [dif_pos h5]; subst h5; rfl
  rw [dif_neg h5]
  by_cases h6 : t = 6
  · rw [dif_pos h6]; subst h6; rfl
  rw [dif_neg h6]
  by_cases h7 : t = 7
  · rw [dif_pos h7]; subst h7; rfl
  rw [dif_neg h7]
  by_cases h10 : t = 10
  · rw [dif_pos h10]; subst h10; rfl
  rw [dif_neg h10]
  by_cases h14 : t = 14
  · rw [dif_pos h14]; subst h14; rfl
  rw [dif_neg h14]
  by_cases h15 : t = 15
  · rw [dif_pos h15]; subst h15; rfl
  rw [dif_neg h15]
  by_cases h17 : t = 17
  · rw [dif_pos h17]; subst h17; rfl
  rw [dif_neg h17]
  by_cases h21 : t = 21
  · rw [dif_pos h21]; subst h21; rfl
  rw [dif_neg h21]
  by_cases h23 : t = 23
  · rw [dif_pos h23]; subst h23; rfl
  rw [dif_neg h23]
  by_cases h29 : t = 29
  · rw [dif_pos h29]; subst h29; rfl
  rw [dif_neg h29]
  by_cases h_gh : t = 0x6ffffef5
  · rw [dif_pos h_gh]; subst h_gh; rfl
  rw [dif_neg h_gh]
  by_cases h_vs : t = 0x6ffffff0
  · rw [dif_pos h_vs]; subst h_vs; rfl
  rw [dif_neg h_vs]
  by_cases h_f1 : t = 0x6ffffffb
  · rw [dif_pos h_f1]; subst h_f1; rfl
  rw [dif_neg h_f1]
  by_cases h_vn : t = 0x6ffffffe
  · rw [dif_pos h_vn]; subst h_vn; rfl
  rw [dif_neg h_vn]
  rfl

/-- Forward identity: `(decode ∘ encode) = id` on `DynTag`.  Now
    provable because the canonicalized type forbids `.raw t` for
    named codes — each named case substitutes its constant and falls
    into the matching `if`; the `.raw t h` case fails every preceding
    `if` (by the disjointness witness) and falls through to the
    catch-all, which reproduces `.raw t h`. -/
theorem DynTag.decode_encode_dyntag (a : DynTag) : DynTag.decode a.encode = a := by
  cases a with
  | null    => rfl
  | needed  => rfl
  | strtab  => rfl
  | symtab  => rfl
  | strsz   => rfl
  | hash    => rfl
  | soname  => rfl
  | rpath   => rfl
  | runpath => rfl
  | rela    => rfl
  | rel     => rfl
  | jmprel  => rfl
  | versym  => rfl
  | verneed => rfl
  | gnuHash => rfl
  | flags1  => rfl
  | debug   => rfl
  | raw t h =>
    obtain ⟨h0, h1, h4, h5, h6, h7, h10, h14, h15, h17, h21, h23, h29,
             h_gh, h_vs, h_f1, h_vn⟩ := h
    show DynTag.decode t = .raw t _
    unfold DynTag.decode
    rw [dif_neg h0, dif_neg h1, dif_neg h4, dif_neg h5, dif_neg h6,
        dif_neg h7, dif_neg h10, dif_neg h14, dif_neg h15, dif_neg h17,
        dif_neg h21, dif_neg h23, dif_neg h29, dif_neg h_gh,
        dif_neg h_vs, dif_neg h_f1, dif_neg h_vn]

/-- A parsed dynamic-section entry. `d_un` is uninterpreted — dynamic entries
    are either an address or an offset depending on tag, and we keep the raw
    64-bit word. -/
structure DynEntry where
  tag   : DynTag
  value : UInt64
  deriving Repr

/-- UInt64-valued codec for `DynTag`. Composes `.encode : DynTag → Int64`
    with `.toUInt64 : Int64 → UInt64` (bit-preserving). -/
def DynTag.encodeU64 (t : DynTag) : UInt64 := t.encode.toUInt64

/-- UInt64-valued decoder for `DynTag`, composing `.toInt64` with
    `DynTag.decode`. -/
def DynTag.decodeU64 (u : UInt64) : DynTag := DynTag.decode u.toInt64

/-- Encode-after-decode identity on the UInt64 representation. Combines
    `DynTag.decode_encode` (Int64-level identity, already proved) with
    the `.toInt64.toUInt64 = id` fact on UInt64 (discharged by
    `bv_decide`). Required by the `elf_schema` codec rule to close the
    byte-roundtrip theorem for the `tag` field of `DynEntry`. -/
theorem DynTag.encodeU64_decodeU64 (u : UInt64) :
    (DynTag.decodeU64 u).encodeU64 = u := by
  unfold DynTag.encodeU64 DynTag.decodeU64
  rw [DynTag.decode_encode]
  bv_decide

/-- Forward identity on the UInt64 representation: decoding the encoding
    of a `DynTag` value recovers it.  Required by the `elf_schema`
    codec rule's forward-roundtrip emission for the `tag` field of
    `DynEntry`.  Closes via `decode_encode_dyntag` after the
    `.toUInt64.toInt64 = id` bridge from `bv_decide`. -/
theorem DynTag.decodeU64_encodeU64 (t : DynTag) :
    DynTag.decodeU64 t.encodeU64 = t := by
  unfold DynTag.decodeU64 DynTag.encodeU64
  rw [show t.encode.toUInt64.toInt64 = t.encode from by bv_decide]
  exact DynTag.decode_encode_dyntag t

/-- Is this entry a DT_RPATH or DT_RUNPATH? Used by rpath-related ops. -/
def DynEntry.isRpathish (d : DynEntry) : Bool :=
  decide (d.tag = DynTag.rpath) || decide (d.tag = DynTag.runpath)

/-- Is this entry a DT_NEEDED, DT_SONAME, DT_RPATH, or DT_RUNPATH?
    These are the 4 dynamic entries whose `.value` is a `.dynstr` byte
    offset, so their validity depends on `.dynstr`'s size. -/
def DynEntry.isStringRef (d : DynEntry) : Bool :=
  decide (d.tag = DynTag.needed) ||
  decide (d.tag = DynTag.soname) ||
  decide (d.tag = DynTag.rpath)  ||
  decide (d.tag = DynTag.runpath)

/-- `isStringRef` as a disjunction.  Useful for `by_cases` over each tag. -/
theorem DynEntry.isStringRef_iff (d : DynEntry) :
    d.isStringRef = true ↔
    (d.tag = DynTag.needed ∨ d.tag = DynTag.soname ∨
     d.tag = DynTag.rpath  ∨ d.tag = DynTag.runpath) := by
  unfold DynEntry.isStringRef
  simp [decide_eq_true_eq, or_assoc]

/-- A DT_NULL entry is not a string-ref. -/
theorem DynEntry.not_rpathish_of_null {d : DynEntry} (hd : d.tag = DynTag.null) :
    d.isRpathish = false := by
  simp [DynEntry.isRpathish, hd]

/-- A parsed `.dynsym` entry (ELF64 `Elf64_Sym`).

    Byte layout (24 bytes):
      st_name   : UInt32 (offset 0, size 4)   -- dynstr offset
      st_info   : UInt8  (offset 4, size 1)   -- type + binding
      st_other  : UInt8  (offset 5, size 1)   -- visibility
      st_shndx  : UInt16 (offset 6, size 2)   -- section index (or SHN_*)
      st_value  : UInt64 (offset 8, size 8)   -- symbol value (addr/offset)
      st_size   : UInt64 (offset 16, size 8)  -- symbol size
-/
structure Symbol where
  st_name   : UInt32
  st_info   : UInt8
  st_other  : UInt8
  st_shndx  : UInt16
  st_value  : UInt64
  st_size   : UInt64
  deriving Repr

/-- A parsed `.gnu.version_r` auxiliary entry (ELF64 `Elf64_Vernaux`, 16 bytes).
    Byte layout:
      vna_hash  : UInt32 (offset 0)
      vna_flags : UInt16 (offset 4)
      vna_other : UInt16 (offset 6)
      vna_name  : UInt32 (offset 8)   -- offset into the strings section
      vna_next  : UInt32 (offset 12)  -- byte offset to next Vernaux; 0 = last
-/
structure Vernaux where
  vna_hash  : UInt32
  vna_flags : UInt16
  vna_other : UInt16
  vna_name  : UInt32
  vna_next  : UInt32
  deriving Repr

/-- A parsed `.gnu.version_r` entry (ELF64 `Elf64_Verneed`, 16 bytes) plus
    its associated Vernaux list. The `.gnu.version_r` section is a linked
    list of Verneed records (each followed by its Vernaux records); we
    flatten it into an array of `Verneed` values here.

    Byte layout:
      vn_version : UInt16 (offset 0)
      vn_cnt     : UInt16 (offset 2)   -- number of associated Vernaux
      vn_file    : UInt32 (offset 4)   -- offset into the strings section
      vn_aux     : UInt32 (offset 8)   -- byte offset to first Vernaux
      vn_next    : UInt32 (offset 12)  -- byte offset to next Verneed; 0 = last

    `replaceNeeded` rewrites `vn_file` when a library is renamed. -/
structure Verneed where
  vn_version : UInt16
  vn_cnt     : UInt16
  vn_file    : UInt32
  vn_aux     : UInt32
  vn_next    : UInt32
  /-- The Vernaux entries this Verneed points at (decoded from the
      `vn_aux`-chained list). Size is `vn_cnt.toNat`. -/
  aux        : Array Vernaux
  deriving Repr

/-- A parsed SysV `.hash` table (Elf32/64 share layout: 8-byte header +
    two u32 arrays).

    Byte layout:
      numBuckets : UInt32 (offset 0)  -- == buckets.size, derived at write
      numChain   : UInt32 (offset 4)  -- == chain.size,   derived at write
      buckets    : numBuckets × UInt32 starting at offset 8
      chain      : numChain × UInt32 starting at offset 8 + numBuckets*4

    `numBuckets` / `numChain` are NOT stored in the IR — they're
    `buckets.size` / `chain.size` by definition.  At write time the
    encoder emits `array.size.toUInt32` for the on-disk count fields;
    at decode time the section size determines the array lengths.
    Keeping these as separate IR fields would let the IR represent
    "stored count disagrees with array size," which is a malformed
    state we'd rather not be expressible.

    Algorithm: hash the symbol name (SysV-hash), mod buckets.size →
    bucket index. `buckets[b]` holds the dynsym index of the first
    symbol hashing to `b`; `chain[i]` links to the next one (0 = end).

    `renameDynamicSymbols` must rebuild the bucket/chain arrays after
    mutating any `st_name` whose hashed bucket would change. -/
structure SysVHashTable where
  buckets : Array UInt32
  chain   : Array UInt32
  deriving Repr

/-- A parsed GNU `.gnu.hash` table. More complex than SysV: it sorts
    dynsyms by hashed bucket so the loader can bsearch + range-scan.

    Byte layout (ELF64):
      numBuckets : UInt32 (offset 0)  -- == buckets.size,  derived at write
      symndx     : UInt32 (offset 4)  -- dynsym index of first hashed symbol
      maskwords  : UInt32 (offset 8)  -- == bloom.size,    derived at write
      shift2     : UInt32 (offset 12)
      bloom      : maskwords × UInt64 (bloom filter)
      buckets    : numBuckets × UInt32
      chain      : rest × UInt32       -- hash + end-of-chain bit

    `numBuckets` and `maskwords` are NOT stored — they're `buckets.size`
    and `bloom.size`.  `symndx` and `shift2` are real algorithmic
    parameters and remain.

    A full rebuild requires re-sorting `.dynsym` (and reindexing every
    relocation that refers to a dynsym by index). We model the fields
    and expose `gnuHash` for callers; full rebuild lives in the
    layout-engine tier. -/
structure GnuHashTable where
  symndx  : UInt32
  shift2  : UInt32
  bloom   : Array UInt64
  buckets : Array UInt32
  chain   : Array UInt32
  deriving Repr

/-- Null-terminated string table (`.dynstr`, `.shstrtab`). We represent it as a
    ByteArray that is guaranteed to end in a zero byte when non-empty. -/
structure StringTable where
  bytes : ByteArray
  deriving Repr

namespace StringTable

/-- A StringTable is well-formed iff either empty or ends with a null byte. -/
def WellFormed (st : StringTable) : Prop :=
  st.bytes.size = 0 ∨ ∃ h : 0 < st.bytes.size, st.bytes[st.bytes.size - 1]'(by omega) = 0

instance (st : StringTable) : Decidable st.WellFormed := by
  unfold WellFormed
  by_cases h : st.bytes.size = 0
  · exact .isTrue (Or.inl h)
  · have hPos : 0 < st.bytes.size := by omega
    by_cases h2 : st.bytes[st.bytes.size - 1]'(by omega) = 0
    · exact .isTrue (Or.inr ⟨hPos, h2⟩)
    · exact .isFalse (by rintro (h3 | ⟨_, h3⟩) <;> contradiction)

/-- Auxiliary: find the first 0 byte at or after `i` in `bs`; return the
    slice `bs[lo..i)`. -/
def findNullFrom (bs : ByteArray) (lo i : Nat) : Option ByteArray :=
  if h : i < bs.size then
    if bs[i] = 0 then some (bs.extract lo i)
    else findNullFrom bs lo (i + 1)
  else none
  termination_by bs.size - i

/-- Look up the C-string starting at byte `offset`. Returns the bytes up to
    (but not including) the terminating null. -/
def lookup (st : StringTable) (offset : Nat) : Option ByteArray :=
  if offset ≥ st.bytes.size then none
  else findNullFrom st.bytes offset offset

/-- Scan the table for the first offset at which the C-string equals `target`.
    Returns `none` if the string is absent (no C-string in the table matches
    `target`). Linear in `bs.size`. Used by ops that want to reuse an
    existing string rather than grow the table via `append`. -/
def findOffsetOf (st : StringTable) (target : ByteArray) : Option Nat :=
  let rec loop (i : Nat) : Option Nat :=
    if _h : i < st.bytes.size then
      match findNullFrom st.bytes i i with
      | some bs => if bs = target then some i else loop (i + bs.size + 1)
      | none    => none
    else none
    termination_by st.bytes.size - i
    decreasing_by omega
  loop 0

/-- Append a null-terminated string and return the offset at which it was
    placed plus the updated table. -/
def append (st : StringTable) (s : String) : StringTable × Nat :=
  let offset := st.bytes.size
  let strBytes := s.toUTF8
  let nullByte := ByteArray.mk #[0]
  let combined := st.bytes ++ strBytes ++ nullByte
  (⟨combined⟩, offset)

theorem append_size (st : StringTable) (s : String) :
    (st.append s).1.bytes.size
    = st.bytes.size + s.toUTF8.size + 1 := by
  simp only [append, ByteArray.size_append]
  rfl

/-- Appending monotonically grows the byte array (a direct corollary of
    `append_size`). Used by preservation proofs that need to show offsets
    in-bounds for the old table remain in-bounds for the new one. -/
theorem append_size_le (st : StringTable) (s : String) :
    st.bytes.size ≤ (st.append s).1.bytes.size := by
  rw [append_size]; omega

/-- The offset `append` returned is `st.bytes.size` (i.e., the end of the
    old table). Useful to reduce `(st.append s).2 < new_size` to an
    `append_size`-driven arithmetic fact. -/
@[simp] theorem append_offset (st : StringTable) (s : String) :
    (st.append s).2 = st.bytes.size := rfl

/-- Ground lemma: the last byte of `a ++ b ++ ⟨#[0]⟩` is 0. -/
private theorem triple_append_last (a b : ByteArray) :
    (a ++ b ++ (⟨#[0]⟩ : ByteArray))[(a ++ b).size]'
        (by
          have : ((⟨#[0]⟩ : ByteArray)).size = 1 := rfl
          simp [ByteArray.size_append, this]) = 0 := by
  rw [ByteArray.getElem_append_right (a := a ++ b) (b := ⟨#[0]⟩)
        (hle := Nat.le_refl _)]
  -- `(a ++ b).size - (a ++ b).size = 0`, and `⟨#[0]⟩[0] = 0`.
  simp only [Nat.sub_self]
  rfl

/-- The new offset (= `st.bytes.size`), cast through `UInt64` and back to
    `Nat`, is in-bounds of the appended table — provided the size fits in
    `UInt64`. Callers reach for this pattern in `dynamicWellFormed` proofs
    for ops that append a new dynamic entry pointing at the newly-added
    string. The `UInt32` variant covers dynsym offsets. -/
theorem append_offset_toNat_lt_appended_u64
    (st : StringTable) (s : String)
    (hFit : st.bytes.size + s.toUTF8.size + 1 < UInt64.size) :
    (UInt64.ofNat st.bytes.size).toNat < (st.append s).1.bytes.size := by
  have hLt : st.bytes.size < UInt64.size := by omega
  rw [append_size, UInt64.toNat_ofNat_of_lt' hLt]; omega

theorem append_offset_toNat_lt_appended_u32
    (st : StringTable) (s : String)
    (hFit : st.bytes.size + s.toUTF8.size + 1 < UInt32.size) :
    (UInt32.ofNat st.bytes.size).toNat < (st.append s).1.bytes.size := by
  have hLt : st.bytes.size < UInt32.size := by omega
  rw [append_size, UInt32.toNat_ofNat_of_lt' hLt]; omega

/-! ## Lookup roundtrip

    When we append a C-safe string to a string table, looking up by
    offset recovers the original bytes. "C-safe" means no interior NUL
    bytes; real filesystem paths, library names, etc. satisfy this.
    The ops that use `StringTable.append` (addNeeded, setRpath, setSoname,
    replaceNeeded) all take filesystem-path-shaped strings, so the
    precondition is trivially met in practice. -/

/-- A ByteArray contains no NUL bytes. -/
def NoNullBytes (bs : ByteArray) : Prop :=
  ∀ i : Fin bs.size, bs[i] ≠ 0

instance (bs : ByteArray) : Decidable (NoNullBytes bs) :=
  decidable_of_iff
    (∀ i : Fin bs.size, bs[i] ≠ 0)
    Iff.rfl

/-- Core lemma: `findNullFrom bs lo i` steps from `i` to `i + k` while
    `bs[j]` is non-zero for `i ≤ j < i + k`, and finds `bs.size - 1` as
    the first null when the byte at `bs.size - 1` is zero and all earlier
    bytes (from `i`) are non-zero. -/
theorem findNullFrom_of_runway
    (bs : ByteArray) (lo nullIdx : Nat)
    (hNull : ∃ h : nullIdx < bs.size, bs[nullIdx]'h = 0)
    (hNoNullsBefore : ∀ j, lo ≤ j → j < nullIdx →
      ∃ h : j < bs.size, bs[j]'h ≠ 0)
    (i : Nat) (hi_ge : lo ≤ i) (hi_le : i ≤ nullIdx) :
    findNullFrom bs lo i = some (bs.extract lo nullIdx) := by
  -- Induction on `nullIdx - i` (decreasing bound).
  obtain ⟨hNullLt, hNullZero⟩ := hNull
  unfold findNullFrom
  have hiLt : i < bs.size := Nat.lt_of_le_of_lt hi_le hNullLt
  rw [dif_pos hiLt]
  by_cases hEq : i = nullIdx
  · -- At the null. `bs[i] = 0`, so the inner `if` returns `bs.extract lo i`.
    subst hEq
    simp [hNullZero]
  · -- Not yet at the null. `bs[i] ≠ 0`, recurse.
    have hiLtNull : i < nullIdx := Nat.lt_of_le_of_ne hi_le hEq
    obtain ⟨_, hNonzero⟩ := hNoNullsBefore i hi_ge hiLtNull
    have : ¬ (bs[i] = 0) := hNonzero
    rw [if_neg this]
    have : nullIdx - (i + 1) < nullIdx - i := by omega
    exact findNullFrom_of_runway bs lo nullIdx
      ⟨hNullLt, hNullZero⟩ hNoNullsBefore (i + 1)
      (Nat.le_of_lt (Nat.lt_of_le_of_lt hi_ge (Nat.lt_succ_self i)))
      hiLtNull
termination_by nullIdx - i

/-- Bytes in the middle region of a triple append:
    `(a ++ b ++ ⟨#[0]⟩).extract a.size (a.size + b.size) = b`. -/
private theorem triple_extract_middle (a b : ByteArray) :
    (a ++ b ++ (⟨#[0]⟩ : ByteArray)).extract a.size (a.size + b.size) = b := by
  -- Use the general `extract_append` to split off the trailing `⟨#[0]⟩`,
  -- then `extract_append_eq_right` to read exactly `b` from `a ++ b`.
  have hAB : (a ++ b).size = a.size + b.size := ByteArray.size_append
  -- Step 1: (a ++ b ++ ⟨#[0]⟩).extract a.size (a.size + b.size)
  --       = (a ++ b).extract a.size (a.size + b.size) ++ empty tail.
  rw [ByteArray.extract_append]
  -- Tail piece: ⟨#[0]⟩.extract (a.size - (a++b).size) (a.size + b.size - (a++b).size)
  --           = ⟨#[0]⟩.extract 0 0 = empty.
  have hLhs : a.size - (a ++ b).size = 0 := by rw [hAB]; omega
  have hRhs : a.size + b.size - (a ++ b).size = 0 := by rw [hAB]; omega
  rw [hLhs, hRhs]
  rw [ByteArray.extract_same]
  rw [ByteArray.append_empty]
  -- Step 2: (a ++ b).extract a.size (a.size + b.size) = b via extract_append_eq_right.
  exact ByteArray.extract_append_eq_right rfl rfl

/-- The central lookup roundtrip. -/
theorem append_lookup (st : StringTable) (s : String)
    (hNoNulls : NoNullBytes s.toUTF8) :
    (st.append s).1.lookup (st.append s).2 = some s.toUTF8 := by
  unfold lookup
  -- The offset is `st.bytes.size`; the table size is `st.bytes.size + s.toUTF8.size + 1`.
  have hSize : (st.append s).1.bytes.size = st.bytes.size + s.toUTF8.size + 1 :=
    append_size st s
  have hOff : (st.append s).2 = st.bytes.size := append_offset st s
  rw [hOff]
  rw [if_neg (by rw [hSize]; omega)]
  -- Now need `findNullFrom (st.append s).1.bytes st.bytes.size st.bytes.size = some s.toUTF8`.
  -- The bytes are `st.bytes ++ s.toUTF8 ++ ⟨#[0]⟩`.
  -- The first null is at index `st.bytes.size + s.toUTF8.size` (the trailing ⟨#[0]⟩).
  -- All bytes in [st.bytes.size, st.bytes.size + s.toUTF8.size) are from s.toUTF8
  -- and non-null by `hNoNulls`.
  have hBytesEq : (st.append s).1.bytes
                = st.bytes ++ s.toUTF8 ++ (⟨#[0]⟩ : ByteArray) := by
    unfold append; rfl
  rw [hBytesEq]
  -- Apply findNullFrom_of_runway with nullIdx = st.bytes.size + s.toUTF8.size.
  let nullIdx := st.bytes.size + s.toUTF8.size
  have hFullSize : (st.bytes ++ s.toUTF8 ++ (⟨#[0]⟩ : ByteArray)).size = nullIdx + 1 := by
    simp [ByteArray.size_append]; show _ + 1 = nullIdx + 1; rfl
  have hNullLt : nullIdx < (st.bytes ++ s.toUTF8 ++ (⟨#[0]⟩ : ByteArray)).size := by
    rw [hFullSize]; omega
  -- The byte at nullIdx is 0.
  have hNullZero : (st.bytes ++ s.toUTF8 ++ (⟨#[0]⟩ : ByteArray))[nullIdx]'hNullLt = 0 := by
    -- nullIdx = (st.bytes ++ s.toUTF8).size.
    have hABSize : (st.bytes ++ s.toUTF8).size = nullIdx := by
      simp [ByteArray.size_append]; rfl
    rw [ByteArray.getElem_append_right (a := st.bytes ++ s.toUTF8)
        (b := (⟨#[0]⟩ : ByteArray)) (hle := hABSize ▸ Nat.le_refl _)]
    have : nullIdx - (st.bytes ++ s.toUTF8).size = 0 := by rw [hABSize]; omega
    simp only [this]
    rfl
  -- Bytes in [st.bytes.size, nullIdx) are from s.toUTF8, non-null.
  have hNoNullsBefore : ∀ j, st.bytes.size ≤ j → j < nullIdx →
      ∃ h : j < (st.bytes ++ s.toUTF8 ++ (⟨#[0]⟩ : ByteArray)).size,
        (st.bytes ++ s.toUTF8 ++ (⟨#[0]⟩ : ByteArray))[j]'h ≠ 0 := by
    intro j hjLo hjHi
    have hj : j < (st.bytes ++ s.toUTF8 ++ (⟨#[0]⟩ : ByteArray)).size := by
      rw [hFullSize]; omega
    refine ⟨hj, ?_⟩
    -- (st.bytes ++ s.toUTF8 ++ ⟨#[0]⟩)[j] = (st.bytes ++ s.toUTF8)[j] (since j < mid.size).
    have hMidSize : (st.bytes ++ s.toUTF8).size = nullIdx := by
      simp [ByteArray.size_append]; rfl
    have hjMidLt : j < (st.bytes ++ s.toUTF8).size := by rw [hMidSize]; exact hjHi
    rw [ByteArray.getElem_append_left (a := st.bytes ++ s.toUTF8)
        (b := (⟨#[0]⟩ : ByteArray)) hjMidLt]
    -- (st.bytes ++ s.toUTF8)[j] = s.toUTF8[j - st.bytes.size] (since j ≥ st.bytes.size).
    have hjSubLt : j - st.bytes.size < s.toUTF8.size := by
      have : j < st.bytes.size + s.toUTF8.size := hjHi
      omega
    rw [ByteArray.getElem_append_right (a := st.bytes)
        (b := s.toUTF8) (i := j) (hle := hjLo)]
    -- Now the goal is s.toUTF8[j - st.bytes.size] ≠ 0.
    exact hNoNulls ⟨j - st.bytes.size, hjSubLt⟩
  -- Apply the runway lemma.
  rw [findNullFrom_of_runway _ _ nullIdx ⟨hNullLt, hNullZero⟩ hNoNullsBefore
      st.bytes.size (Nat.le_refl _) (Nat.le_add_right _ _)]
  -- Goal: some ((st.bytes ++ s.toUTF8 ++ ⟨#[0]⟩).extract st.bytes.size nullIdx) = some s.toUTF8.
  show some _ = some s.toUTF8
  congr 1
  -- This is triple_extract_middle st.bytes s.toUTF8.
  exact triple_extract_middle st.bytes s.toUTF8

/-- Lookup the appended string via the `UInt64.ofNat`-truncated offset.
    Callers (four observable theorems) compute `(UInt64.ofNat st.bytes.size).toNat`
    as the dynamic-entry value; this packages the offset-fit-through-U64 +
    `append_lookup` steps into one fact. -/
theorem append_lookup_u64 (st : StringTable) (s : String)
    (hLt : st.bytes.size < UInt64.size)
    (hNoNulls : NoNullBytes s.toUTF8) :
    (st.append s).1.lookup (UInt64.ofNat st.bytes.size).toNat = some s.toUTF8 := by
  rw [UInt64.toNat_ofNat_of_lt' hLt]
  have hOff : (st.append s).2 = st.bytes.size := append_offset st s
  rw [← hOff]
  exact append_lookup st s hNoNulls

/-- `UInt32` variant: used by `st_name` / `vn_file` observables
    where the field is 32 bits instead of 64. -/
theorem append_lookup_u32 (st : StringTable) (s : String)
    (hLt : st.bytes.size < UInt32.size)
    (hNoNulls : NoNullBytes s.toUTF8) :
    (st.append s).1.lookup (UInt32.ofNat st.bytes.size).toNat = some s.toUTF8 := by
  rw [UInt32.toNat_ofNat_of_lt' hLt]
  have hOff : (st.append s).2 = st.bytes.size := append_offset st s
  rw [← hOff]
  exact append_lookup st s hNoNulls

theorem append_wellFormed (st : StringTable) (s : String) :
    (st.append s).1.WellFormed := by
  right
  have hSize : (st.append s).1.bytes.size = st.bytes.size + s.toUTF8.size + 1 :=
    append_size st s
  refine ⟨by omega, ?_⟩
  -- Index size-1 = st.bytes.size + s.toUTF8.size = (st.bytes ++ s.toUTF8).size.
  show (st.append s).1.bytes[(st.append s).1.bytes.size - 1]'(by omega) = 0
  -- Convert the LHS to the triple-append form, then use triple_append_last.
  have hIdx : (st.append s).1.bytes.size - 1 = (st.bytes ++ s.toUTF8).size := by
    rw [hSize, ByteArray.size_append]; omega
  -- Transport the index. Since both sides are UInt8, we can rewrite with hIdx.
  simp only [hIdx]
  -- Now goal: `(st.append s).1.bytes[(st.bytes ++ s.toUTF8).size]? ... = 0`.
  -- Unfold append to reveal the triple structure.
  show ((StringTable.append st s).1).bytes[_] = 0
  unfold append
  exact triple_append_last st.bytes s.toUTF8

end StringTable

/-! ## Hash functions

    ELF uses two string-hash algorithms for dynamic symbol lookup:
    SysV-hash (`.hash` section) and GNU-hash (`.gnu.hash` section).
    Both consume a NUL-terminated byte sequence. -/

/-- SysV (ELF) hash of a byte sequence. Mirrors C++ patchelf.cc:2185.
    Terminates on the first NUL byte or at the end of `bs`. -/
def sysvHash (bs : ByteArray) : UInt32 :=
  let rec go (i : Nat) (h : UInt32) : UInt32 :=
    if hLt : i < bs.size then
      let c := bs[i]
      if c = 0 then h
      else
        let h' := (h <<< 4) + c.toUInt32
        let g := h' &&& 0xf0000000
        let h'' := if g ≠ 0 then (h' ^^^ (g >>> 24)) &&& (Complement.complement g) else h'
        go (i + 1) h''
    else h
  termination_by bs.size - i
  decreasing_by simp_wf; omega
  go 0 0

/-- GNU hash of a byte sequence. Mirrors C++ patchelf.cc:2058.
    djb2 variant terminating on NUL. -/
def gnuHash (bs : ByteArray) : UInt32 :=
  let rec go (i : Nat) (h : UInt32) : UInt32 :=
    if hLt : i < bs.size then
      let c := bs[i]
      if c = 0 then h
      else go (i + 1) ((h <<< 5) + h + c.toUInt32)
    else h
  termination_by bs.size - i
  decreasing_by simp_wf; omega
  go 0 5381

/-- Program header (ELF64 subset).  Used by both the byte-layer `ElfFile` and typed `ValidElfFile`
    ElfFile models (formerly lived in Elf/ElfFile.lean). -/
structure ProgramHeader where
  type   : Layout.PhType
  flags  : UInt32
  offset : Layout.FileOffset
  vaddr  : Layout.VirtualAddr
  paddr  : Layout.PhysicalAddr
  filesz : Layout.ByteSize
  memsz  : Layout.ByteSize
  align  : Layout.Alignment
  deriving Repr

/-- Section header (ELF64 subset).  Used by both the byte-layer `ElfFile` and typed `ValidElfFile`
    ElfFile models (formerly lived in Elf/ElfFile.lean). -/
structure SectionHeader where
  name      : UInt32
  type      : Layout.ShType
  flags     : UInt64
  addr      : Layout.VirtualAddr
  offset    : Layout.FileOffset
  size      : Layout.ByteSize
  link      : UInt32
  info      : UInt32
  addralign : Layout.Alignment
  entsize   : Layout.ByteSize
  deriving Repr

/-- Pull the underlying value `v` with `o = some v` out of an `isSome` witness. -/
theorem Option.get_witness {α : Type} {o : Option α} (h : o.isSome) :
    ∃ v, o = some v ∧ o.get h = v := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
  exact ⟨v, hv, by simp [hv]⟩

end Patchelf.Elf
