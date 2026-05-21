/-
  Execstack — set or clear PT_GNU_STACK's execute bit.

  Phdr-only op: map every PT_GNU_STACK phdr, flip PF_X bit.  Nothing
  else in ValidElfFile changes.
-/
module

public import Patchelf.Elf.ValidElfFile
public import Patchelf.Elf.Basic
public import Patchelf.Elf.Layout

@[expose] public section

namespace Patchelf.Elf

open Patchelf.Elf (ProgramHeader)
open Patchelf.Elf.Layout (PhType)

namespace ExecstackFlags
/-- ELF phdr executable flag. -/
def PF_X : UInt32 := 0x1
end ExecstackFlags

inductive ExecstackMode | set | clear
  deriving DecidableEq, Repr

/-- Modify every PT_GNU_STACK phdr's executable bit. -/
def modifyExecstack (e : ValidElfFile) (mode : ExecstackMode) : ValidElfFile :=
  { e with phdrs := e.phdrs.map fun ph =>
      if ph.type = PhType.PT_GNU_STACK then
        match mode with
        | .set   => { ph with flags := ph.flags ||| ExecstackFlags.PF_X }
        | .clear => { ph with flags := ph.flags &&& (Complement.complement ExecstackFlags.PF_X) }
      else ph }

/-! ## Observables -/

@[simp] theorem modifyExecstack_dynstr (e : ValidElfFile) (m : ExecstackMode) :
    (modifyExecstack e m).dynstr = e.dynstr := rfl
@[simp] theorem modifyExecstack_dynamic (e : ValidElfFile) (m : ExecstackMode) :
    (modifyExecstack e m).dynamic = e.dynamic := rfl
@[simp] theorem modifyExecstack_header (e : ValidElfFile) (m : ExecstackMode) :
    (modifyExecstack e m).header = e.header := rfl

@[simp] theorem modifyExecstack_phdrs_size (e : ValidElfFile) (m : ExecstackMode) :
    (modifyExecstack e m).phdrs.size = e.phdrs.size := by
  unfold modifyExecstack; simp

end Patchelf.Elf
