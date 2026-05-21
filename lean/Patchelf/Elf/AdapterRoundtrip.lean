/-
  Adapter round-trip preservation.

  Proves four structural facts about the byte-layer ⇄ typed
  adapter:

    toElfFile_header  : (toElfFile template t).header = t.header
    toElfFile_phdrs   : (toElfFile template t).phdrs  = t.phdrs
    ofElfFile_header  : ofElfFile e = .ok t → t.header = e.header
    ofElfFile_phdrs   : ofElfFile e = .ok t → t.phdrs  = e.phdrs

  And their composition:

    roundtrip_header : ofElfFile e = .ok t →
                       (toElfFile e t).header = e.header
    roundtrip_phdrs  : ofElfFile e = .ok t →
                       (toElfFile e t).phdrs  = e.phdrs

  Proof technique for the `ofElfFile` side:
  `simp only [ofElfFile, bind, Except.bind] at h` unfolds the
  do-block; then staged `split at h <;> split at h <;> …`
  destructures the nested matches (on `e.dynsym`, `e.dynamic`,
  `symbolSectionOf` result, `DynamicSection.parseFrom` result).
  Each success branch closes with `cases h; rfl`; error branches
  close with `simp_all`.
-/
module

public import Patchelf.Elf.Adapter

@[expose] public section

namespace Patchelf.Elf.Adapter

open Patchelf.Elf (ElfFile)

/-! ## toElfFile preservation -/

@[simp] theorem toElfFile_header (template : ElfFile) (t : ValidElfFile) :
    (toElfFile template t).header = t.header := rfl

@[simp] theorem toElfFile_phdrs (template : ElfFile) (t : ValidElfFile) :
    (toElfFile template t).phdrs = t.phdrs := rfl

/-! ## ofElfFile preservation -/

/-- On successful ofElfFile, t.header = e.header.

    Technique: unfold the do-block via `bind`/`Except.bind`, then
    `split at h` through the 4 levels of nested matches (dynsym
    promotion success + dynsym option + dynamic parse success +
    dynamic option).  Each resulting success case closes with
    `cases h; rfl`; error cases close with `simp_all`. -/
theorem ofElfFile_header (e : ElfFile) (t : ValidElfFile)
    (h : ofElfFile e = .ok t) : t.header = e.header := by
  simp only [ofElfFile, bind, Except.bind] at h
  split at h
  all_goals split at h
  all_goals (try split at h)
  all_goals (try split at h)
  all_goals (first | (cases h; rfl) | simp_all)

/-- On successful ofElfFile, t.phdrs = e.phdrs. -/
theorem ofElfFile_phdrs (e : ElfFile) (t : ValidElfFile)
    (h : ofElfFile e = .ok t) : t.phdrs = e.phdrs := by
  simp only [ofElfFile, bind, Except.bind] at h
  split at h
  all_goals split at h
  all_goals (try split at h)
  all_goals (try split at h)
  all_goals (first | (cases h; rfl) | simp_all)

/-- Bonus: the typed dynstr field is the byte-layer dynstr wrapped via
    `mkStringSectionOpt` (handles the WellFormed force-termination). -/
theorem ofElfFile_dynstr (e : ElfFile) (t : ValidElfFile)
    (h : ofElfFile e = .ok t) : t.dynstr = mkStringSectionOpt e.dynstr := by
  simp only [ofElfFile, bind, Except.bind] at h
  split at h
  all_goals split at h
  all_goals (try split at h)
  all_goals (try split at h)
  all_goals (first | (cases h; rfl) | simp_all)

/-- Bonus: typed versym is the byte-layer versym verbatim. -/
theorem ofElfFile_versym (e : ElfFile) (t : ValidElfFile)
    (h : ofElfFile e = .ok t) : t.versym = e.versym := by
  simp only [ofElfFile, bind, Except.bind] at h
  split at h
  all_goals split at h
  all_goals (try split at h)
  all_goals (try split at h)
  all_goals (first | (cases h; rfl) | simp_all)

/-! ## Round-trip composition -/

theorem roundtrip_header (e : ElfFile) (t : ValidElfFile)
    (h : ofElfFile e = .ok t) :
    (toElfFile e t).header = e.header := by
  rw [toElfFile_header]; exact ofElfFile_header e t h

theorem roundtrip_phdrs (e : ElfFile) (t : ValidElfFile)
    (h : ofElfFile e = .ok t) :
    (toElfFile e t).phdrs = e.phdrs := by
  rw [toElfFile_phdrs]; exact ofElfFile_phdrs e t h

end Patchelf.Elf.Adapter
