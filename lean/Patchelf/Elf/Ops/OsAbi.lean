/-
  setOsAbi — flip the EI_OSABI byte in the ELF header.

  Pure record update + trivial observables. No dynstr interaction.
-/
module

public import Patchelf.Elf.ValidElfFile
public import Patchelf.Elf.Basic

@[expose] public section

namespace Patchelf.Elf

open Patchelf.Elf (OsAbi)

/-- `setOsAbi` is a wrapper over `ValidElfFile.setOsAbi` (defined in
    ValidElfFile.lean for the header-only helper family).  Present as a
    top-level alias for consistency with the other op modules. -/
@[inline] def setOsAbi (e : ValidElfFile) (abi : OsAbi) : ValidElfFile :=
  e.setOsAbi abi

/-! ## Observables: trivial projections -/

@[simp] theorem setOsAbi_observable (e : ValidElfFile) (abi : OsAbi) :
    (setOsAbi e abi).header.ident.osAbi = abi := rfl

@[simp] theorem setOsAbi_dynstr (e : ValidElfFile) (abi : OsAbi) :
    (setOsAbi e abi).dynstr = e.dynstr := rfl
@[simp] theorem setOsAbi_dynamic (e : ValidElfFile) (abi : OsAbi) :
    (setOsAbi e abi).dynamic = e.dynamic := rfl
@[simp] theorem setOsAbi_phdrs (e : ValidElfFile) (abi : OsAbi) :
    (setOsAbi e abi).phdrs = e.phdrs := rfl

end Patchelf.Elf
