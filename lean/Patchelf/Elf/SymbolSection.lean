/-
  SymbolSection — dynsym entries indexed by a StringSection.

  Symbol.st_name is an offset into .dynstr; The typed record stores it as
  Fin ds.size to guarantee bounds at the type level.  The rest of
  Symbol (st_info, st_other, st_shndx, st_value, st_size) is preserved
  verbatim.
-/

import Patchelf.Elf.StringSection
import Patchelf.Elf.Basic

namespace Patchelf.Elf

open Patchelf.Elf (StringTable)

/-- A single dynsym entry whose `st_name` is an in-bounds offset into
    a specific StringSection. -/
structure TypedSymbol (ds : StringSection) where
  st_name   : Fin ds.size
  st_info   : UInt8
  st_other  : UInt8
  st_shndx  : UInt16
  st_value  : UInt64
  st_size   : UInt64
  deriving Repr

/-- The `.dynsym` section.  Every symbol's `st_name` is guaranteed
    in-bounds of `ds`. -/
structure SymbolSection (ds : StringSection) where
  symbols : Array (TypedSymbol ds)
  deriving Repr

namespace SymbolSection

/-- Lift the symbols when `.dynstr` grows. -/
def rebase {ds ds' : StringSection} (h : StringSection.SizeLE ds ds')
    (s : SymbolSection ds) : SymbolSection ds' where
  symbols := s.symbols.map fun sym =>
    { sym with st_name := Fin.castLE h sym.st_name }

/-- Rename a single symbol by index.  The new name's offset is typed. -/
def renameAt {ds : StringSection} (s : SymbolSection ds)
    (i : Nat) (newOff : Fin ds.size) : SymbolSection ds where
  symbols :=
    if h : i < s.symbols.size then
      s.symbols.set i { (s.symbols[i]'h) with st_name := newOff } h
    else
      s.symbols

@[simp] theorem rebase_size {ds ds' : StringSection}
    (h : StringSection.SizeLE ds ds') (s : SymbolSection ds) :
    (s.rebase h).symbols.size = s.symbols.size := by
  unfold rebase; simp

@[simp] theorem renameAt_size {ds : StringSection}
    (s : SymbolSection ds) (i : Nat) (newOff : Fin ds.size) :
    (s.renameAt i newOff).symbols.size = s.symbols.size := by
  unfold renameAt
  split <;> simp

end SymbolSection
end Patchelf.Elf
