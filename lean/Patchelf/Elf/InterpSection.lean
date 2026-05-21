/-
  InterpSection — the `.interp` section (typed).

  Stored as a UTF8 ByteArray path with the implicit trailing NUL added
  at encode time.  The path is the WHOLE section content; no internal
  structure.  Ops treat it as a single-field overwrite.
-/

import Patchelf.Elf.Basic -- For the Repr ByteArray instance

namespace Patchelf.Elf

/-- The ELF interpreter path.  The trailing NUL is implicit (added by
    encode), so callers store just the path bytes. -/
structure InterpSection where
  path : ByteArray
  deriving Repr

namespace InterpSection

/-- Encode to wire bytes: path + trailing NUL. -/
def toBytes (s : InterpSection) : ByteArray := s.path ++ (⟨#[0]⟩ : ByteArray)

/-- The encoded size of an InterpSection is `path.size + 1`. -/
@[simp] theorem toBytes_size (s : InterpSection) :
    s.toBytes.size = s.path.size + 1 := by
  unfold toBytes
  rw [ByteArray.size_append]
  rfl

/-- Construct from a Lean String. -/
def ofString (s : String) : InterpSection := ⟨s.toUTF8⟩

end InterpSection
end Patchelf.Elf
