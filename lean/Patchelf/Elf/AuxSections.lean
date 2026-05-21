/-
  Auxiliary structural section wrappers for the typed algebra.

  Passthrough wrappers over the byte-layer structs for Verneed /
  SysV hash / GNU hash.  These sections are preserved verbatim
  during ops (none of the 14 mutate their internal structure —
  even `renameDynamicSymbols` rebuilds the SysV hash via a
  dedicated function, not by mutating section fields).

  An earlier dependent-typing design (`VersymSection` indexed by a
  `SymbolSection` with size-parity) was prototyped but had no
  runtime callers and was removed.  If future ops need it,
  restore via an `elf_section` DSL that binds parser + encoder +
  ops together in one declaration.
-/

import Patchelf.Elf.Basic

namespace Patchelf.Elf

open Patchelf.Elf (Verneed SysVHashTable GnuHashTable)

/-- `.gnu.version_r` as a passthrough. -/
structure VerneedSection where
  entries : Array Verneed
  deriving Repr

/-- `.hash` (SysV) as a passthrough. -/
structure SysVHashSection where
  table : SysVHashTable
  deriving Repr

/-- `.gnu.hash` as a passthrough. -/
structure GnuHashSection where
  table : GnuHashTable
  deriving Repr

end Patchelf.Elf
