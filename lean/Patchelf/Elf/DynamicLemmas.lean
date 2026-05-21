/-
  DT_STRSZ synchronization helper.

  After a `.dynstr`-growing op, the `DT_STRSZ` entry in `.dynamic`
  (if present) must be updated to match the new `.dynstr.sh_size`.
  C++ patchelf does this globally in `rewriteSections()`
  (patchelf.cc:1247); the byte-layer encoder calls `syncDtStrsz`
  via `Encoder.syncDtStrszInFile` as its first pre-pass.

  This file is intentionally small.  An earlier design carried
  helper lemmas (`insertBeforeLast`, filter/map back?-null lemmas,
  subset-tag witnesses, etc.) operating on the byte layer's
  `Array DynEntry` representation, but the typed algebra exposes
  `.dynamic` as `Option (DynamicSection ds)` with named fields,
  so those lemmas had no callers and were removed.
-/
module

public import Patchelf.Elf.Basic

@[expose] public section

namespace Patchelf.Elf

/-- Rewrite the `value` of a DT_STRSZ entry to `newSize`; leave other
    entries unchanged. -/
def syncDtStrszEntry (newSize : UInt64) (d : DynEntry) : DynEntry :=
  if d.tag = DynTag.strsz then { d with value := newSize } else d

/-- Apply `syncDtStrszEntry newSize` across a dyn array. -/
def syncDtStrsz (dyn : Array DynEntry) (newSize : UInt64) : Array DynEntry :=
  dyn.map (syncDtStrszEntry newSize)

@[simp] theorem syncDtStrsz_size (dyn : Array DynEntry) (newSize : UInt64) :
    (syncDtStrsz dyn newSize).size = dyn.size := by
  unfold syncDtStrsz; simp

@[simp] theorem syncDtStrszEntry_tag (newSize : UInt64) (d : DynEntry) :
    (syncDtStrszEntry newSize d).tag = d.tag := by
  unfold syncDtStrszEntry
  split <;> rfl

@[simp] theorem syncDtStrszEntry_isStringRef (newSize : UInt64) (d : DynEntry) :
    (syncDtStrszEntry newSize d).isStringRef = d.isStringRef := by
  unfold syncDtStrszEntry
  split <;> rfl

/-- `syncDtStrszEntry` is the identity on entries that already match
    (DT_STRSZ entries with `value = newSize`, or any non-DT_STRSZ entry). -/
theorem syncDtStrszEntry_eq_self (newSize : UInt64) (d : DynEntry)
    (h : d.tag = DynTag.strsz → d.value = newSize) :
    syncDtStrszEntry newSize d = d := by
  unfold syncDtStrszEntry
  by_cases hT : d.tag = DynTag.strsz
  · rw [if_pos hT]
    have : d.value = newSize := h hT
    cases d; simp; exact this.symm
  · rw [if_neg hT]

/-- `syncDtStrsz` is the identity when all DT_STRSZ entries already
    have `value = newSize`. -/
theorem syncDtStrsz_eq_id (dyn : Array DynEntry) (newSize : UInt64)
    (h : ∀ (i : Nat) (hi : i < dyn.size),
         (dyn[i]'hi).tag = DynTag.strsz → (dyn[i]'hi).value = newSize) :
    syncDtStrsz dyn newSize = dyn := by
  unfold syncDtStrsz
  apply Array.ext
  · simp
  · intros i hi _
    rw [Array.getElem_map]
    have hiBound : i < dyn.size := by
      simp at hi; exact hi
    exact syncDtStrszEntry_eq_self newSize (dyn[i]'hiBound) (h i hiBound)

end Patchelf.Elf
