/-
  setInterpreter — replace the `.interp` section content.

    * Overwrite `e.interp` with a new `InterpSection`.
    * Sync every `PT_INTERP` phdr's filesz/memsz to the new byte length
      (path length + 1 for trailing NUL).

  No fitsInExistingSlot precondition (the encoder handles layout).
-/

import Patchelf.Elf.ValidElfFile
import Patchelf.Elf.Basic
import Patchelf.Elf.Layout

namespace Patchelf.Elf

open Patchelf.Elf.Layout (PhType ByteSize)

/-- Overwrite `.interp` and update every PT_INTERP phdr's filesz/memsz. -/
def setInterpreter (e : ValidElfFile) (newPath : String) : ValidElfFile :=
  let newInterp := InterpSection.ofString newPath
  let newFilesz : ByteSize := ⟨newInterp.toBytes.size⟩
  { e with
      interp := some newInterp
      phdrs  := e.phdrs.map fun ph =>
        if ph.type = PhType.PT_INTERP then
          { ph with filesz := newFilesz, memsz := newFilesz }
        else ph }

/-! ## Observables -/

/-- After `setInterpreter`, `.interp` holds the new path. -/
@[simp] theorem setInterpreter_interp (e : ValidElfFile) (path : String) :
    (setInterpreter e path).interp = some (InterpSection.ofString path) := rfl

@[simp] theorem setInterpreter_dynstr (e : ValidElfFile) (path : String) :
    (setInterpreter e path).dynstr = e.dynstr := rfl
@[simp] theorem setInterpreter_dynamic (e : ValidElfFile) (path : String) :
    (setInterpreter e path).dynamic = e.dynamic := rfl

/-- Every PT_INTERP phdr's filesz, after setInterpreter, encodes
    `path.toUTF8.size + 1` (i.e. path + NUL).  No fit precondition
    needed at the typed-section algebra layer — `.val` is `Nat`. -/
theorem setInterpreter_pt_interp_filesz
    (e : ValidElfFile) (path : String)
    (i : Nat) (hi : i < (setInterpreter e path).phdrs.size)
    (hiOrig : i < e.phdrs.size)
    (hType : (e.phdrs[i]'hiOrig).type = PhType.PT_INTERP) :
    (Patchelf.Elf.ProgramHeader.filesz
      ((setInterpreter e path).phdrs[i]'hi)).val
      = path.utf8ByteSize + 1 := by
  unfold setInterpreter
  show (Patchelf.Elf.ProgramHeader.filesz
         ((e.phdrs.map _)[i]'_)).val = _
  rw [Array.getElem_map]
  simp only [hType, if_true]
  unfold InterpSection.ofString
  show (Patchelf.Elf.Layout.ByteSize.val
         (⟨((⟨path.toUTF8⟩ : InterpSection).toBytes.size)⟩ :
           Patchelf.Elf.Layout.ByteSize)) = _
  rw [InterpSection.toBytes_size]
  rfl

end Patchelf.Elf
