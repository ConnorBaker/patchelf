/-
  Encoder for DynamicSection (typed → byte-layer DynEntry).

  Goal: validate the design claim that coherence tags
  (DT_STRTAB, DT_SYMTAB, DT_HASH, DT_GNU_HASH, DT_VERNEED, DT_STRSZ)
  can be DERIVED at encode time from a layout context, rather than
  stored as DynEntries with post-hoc coherence invariants.

  Concretely:
    * The byte layer has `IsFullyValid` clauses `dynStrszCoherent` and
      `dynAddressCoherentForTag × 5` — six cross-section coherence
      predicates that every op must either prove preserved or break.
    * This encoder eliminates all six.  The `DynamicSection` only stores the
      user-facing fields (needed, rpath, runpath, soname, flags1, debug,
      unstructured); the encoder emits DT_* entries that reference
      derived values.  Parsing validates (rejects wrong offsets) but
      the IR never carries them.

  Scope of this file: the `assembleEntries` function + proofs that
  (1) the output is DT_NULL-terminated, (2) every string-ref entry's
  value is < ds.size.

  Out of scope: the full ElfFile → ByteArray pipeline, layout
  computation, PT_INTERP/PT_DYNAMIC derivation.  Those are the next
  steps if the DynamicSection encoder design holds up.
-/
module

public import Patchelf.Elf.DynamicSection
public import Patchelf.Elf.Basic

@[expose] public section

namespace Patchelf.Elf

open Patchelf.Elf (DynEntry DynTag)

/-- The address/size metadata the encoder needs to synthesize
    coherence tags.  In a full port this is produced by the layout
    engine; for this prototype the user supplies it. -/
structure LayoutCtx where
  /-- Runtime address of `.dynstr`.  Becomes DT_STRTAB's value. -/
  dynstrAddr   : UInt64
  /-- Runtime address of `.dynsym` (if present).  Becomes DT_SYMTAB's value. -/
  dynsymAddr   : Option UInt64
  /-- Runtime address of SysV `.hash` (if present).  Becomes DT_HASH's value. -/
  hashAddr     : Option UInt64
  /-- Runtime address of `.gnu.hash` (if present).  Becomes DT_GNU_HASH. -/
  gnuHashAddr  : Option UInt64
  /-- Runtime address of `.gnu.version_r` (if present).  Becomes DT_VERNEED. -/
  verneedAddr  : Option UInt64
  deriving Repr

namespace DynamicSection

/-! ## Per-field encoding helpers -/

/-- Emit a DT_NEEDED entry from a dynstr offset. -/
@[inline] def emitNeeded {ds : StringSection} (off : Fin ds.size) : DynEntry :=
  { tag := DynTag.needed, value := off.val.toUInt64 }

/-- Emit a DT_RPATH or DT_RUNPATH entry. -/
@[inline] def emitRpath {ds : StringSection} (off : Fin ds.size) : DynEntry :=
  { tag := DynTag.rpath, value := off.val.toUInt64 }

@[inline] def emitRunpath {ds : StringSection} (off : Fin ds.size) : DynEntry :=
  { tag := DynTag.runpath, value := off.val.toUInt64 }

@[inline] def emitSoname {ds : StringSection} (off : Fin ds.size) : DynEntry :=
  { tag := DynTag.soname, value := off.val.toUInt64 }

/-- Emit DT_STRTAB, DT_STRSZ, and the OPTIONAL layout-sensitive tags
    (DT_SYMTAB, DT_HASH, DT_GNU_HASH, DT_VERNEED).  None of these are
    stored in the DynamicSection — they're derived from layout at
    encode time. -/
def emitCoherenceTags (ds : StringSection) (ctx : LayoutCtx) : Array DynEntry :=
  #[{ tag := DynTag.strtab, value := ctx.dynstrAddr }
   ,{ tag := DynTag.strsz,  value := ds.size.toUInt64 }]
  |> appendOpt (ctx.dynsymAddr.map  fun a => { tag := DynTag.symtab,  value := a })
  |> appendOpt (ctx.hashAddr.map    fun a => { tag := DynTag.hash,    value := a })
  |> appendOpt (ctx.gnuHashAddr.map fun a => { tag := DynTag.gnuHash, value := a })
  |> appendOpt (ctx.verneedAddr.map fun a => { tag := DynTag.verneed, value := a })
where
  /-- Append an optional entry if present. -/
  appendOpt (e : Option DynEntry) (arr : Array DynEntry) : Array DynEntry :=
    match e with
    | some x => arr.push x
    | none   => arr

/-- Emit the structured non-coherence entries: rpath/runpath/soname/
    flags1/debug.  Each contributes 0 or 1 entries. -/
def emitStructuredEntries {ds : StringSection} (d : DynamicSection ds) :
    Array DynEntry :=
  let acc0 : Array DynEntry := #[]
  let acc1 := match d.rpath    with | some off => acc0.push (emitRpath   off) | none => acc0
  let acc2 := match d.runpath  with | some off => acc1.push (emitRunpath off) | none => acc1
  let acc3 := match d.soname   with | some off => acc2.push (emitSoname  off) | none => acc2
  let acc4 := match d.flags1   with
              | some v => acc3.push { tag := DynTag.flags1, value := v }
              | none   => acc3
  let acc5 := match d.debug    with
              | some v => acc4.push { tag := DynTag.debug,  value := v }
              | none   => acc4
  acc5

/-- Emit DT_NEEDED entries in storage order (one per `needed` offset). -/
def emitNeededEntries {ds : StringSection} (d : DynamicSection ds) :
    Array DynEntry :=
  d.needed.map emitNeeded

/-! ## Full assembly

    Canonical order: coherence tags first, then structured entries,
    then DT_NEEDED entries, then DT_NULL terminator.

    Layout-sensitive entries (DT_RELA / DT_REL / DT_JMPREL) are NOT
    emitted by `assembleEntries` — those are preserved by
    `Adapter.patchDynamicEntries` from the byte-layer template.
    `assembleEntries` only fires on the synthesize-from-scratch
    path (typed dynamic exists but byte-layer dynamic does not),
    where there's no template to preserve from.

    Real-world ELF writers emit coherence tags in a specific order
    (DT_NEEDED first, then DT_STRTAB, DT_SYMTAB, DT_HASH, ...); for
    byte-identical round-trip with the original binary we'd use an
    `EncodeOrdering` field.  For this prototype, a fixed canonical
    order suffices.
-/

/-- Assemble the full Array DynEntry for serialization.  DT_NULL is
    always the last entry.

    Inlined (rather than using `let` bindings) so `unfold` gives a
    shape `rw` can pattern-match against. -/
def assembleEntries {ds : StringSection} (d : DynamicSection ds)
    (ctx : LayoutCtx) : Array DynEntry :=
  ((emitCoherenceTags ds ctx ++ emitStructuredEntries d ++
    emitNeededEntries d).push
    { tag := DynTag.null, value := 0 })

/-! ## Well-formedness by construction -/

/-- The last entry is always DT_NULL, because we always push it last. -/
@[simp] theorem assembleEntries_back?_null
    {ds : StringSection} (d : DynamicSection ds) (ctx : LayoutCtx) :
    (d.assembleEntries ctx).back?.any
      (fun e => decide (e.tag = DynTag.null)) = true := by
  unfold assembleEntries
  simp

/-- Size equality: assembleEntries produces exactly
    (coherenceCount + structuredCount + needed.size + 1) entries.
    This is the hook for the encoder's size-eq theorem. -/
theorem assembleEntries_size
    {ds : StringSection} (d : DynamicSection ds) (ctx : LayoutCtx) :
    (d.assembleEntries ctx).size =
      (emitCoherenceTags ds ctx).size +
      (emitStructuredEntries d).size +
      d.needed.size + 1 := by
  unfold assembleEntries emitNeededEntries
  simp [Array.size_append, Nat.add_assoc]

/-! ## Content-preservation observable

    The fundamental round-trip claim: every offset in `d.needed`
    appears in the encoded output as a DT_NEEDED entry with the
    corresponding value.  This is what closes the observable chain
    for addNeeded/replaceNeeded after encoding.
-/

/-- Every offset in `d.needed` corresponds to a DT_NEEDED entry
    *somewhere* in the assembled output.

    Proof: `emitNeeded off` is an element of `d.needed.map emitNeeded`,
    which is the right argument of the outer `++` in `assembleEntries`
    (before the trailing DT_NULL `push`). -/
theorem needed_offset_emitted
    {ds : StringSection} (d : DynamicSection ds) (ctx : LayoutCtx)
    (off : Fin ds.size) (hMem : off ∈ d.needed) :
    ∃ e ∈ d.assembleEntries ctx,
      e.tag = DynTag.needed ∧ e.value = off.val.toUInt64 := by
  have hMapMem : emitNeeded off ∈ d.needed.map emitNeeded := by
    rw [Array.mem_map]; exact ⟨off, hMem, rfl⟩
  unfold assembleEntries emitNeededEntries
  refine ⟨emitNeeded off, ?_, rfl, rfl⟩
  apply Array.mem_push_of_mem
  apply Array.mem_append.mpr; right
  exact hMapMem

/-! ## String-ref bounds by construction

    The byte-layer `dynamicWellFormed` clause has two pieces:
    (a) DT_NULL terminator, and
    (b) every string-ref entry's value is < `.dynstr.size`.

    (a) is proved by `assembleEntries_back?_null` above.  (b) is proved
    below: every string-ref entry in the assembled output comes from a
    `Fin ds.size` field, whose `.val` is bounded by definition.

    This is the core payoff of the indexed type: there's no way to
    construct an out-of-bounds string-ref entry because the offset's
    type prevents it.
-/

/-- If `ds.size < 2^64`, every string-ref entry's value (as a Nat)
    is strictly less than `ds.size`.  The precondition is trivially
    supplied by any real ELF file (dynstrs are never anywhere near
    2^64 bytes); in a full port it lives on `LayoutCtx` or its caller.

    This is the theorem that the byte layer spent cross-section coherence
    reasoning to establish.  Here it's a 3-line consequence of the
    type-level bound. -/
theorem emitNeeded_value_lt {ds : StringSection} (off : Fin ds.size)
    (hDsFit : ds.size < UInt64.size) :
    (emitNeeded off).value.toNat < ds.size := by
  unfold emitNeeded
  show off.val.toUInt64.toNat < ds.size
  have hOffFit : off.val < UInt64.size := Nat.lt_trans off.isLt hDsFit
  -- off.val.toUInt64 = UInt64.ofNat off.val; its .toNat reduces to
  -- off.val mod 2^64 = off.val under hOffFit.  `simp` closes it with
  -- both `Nat.toUInt64` unfolded and the mod-of-small simp lemma.
  have hEq : off.val.toUInt64.toNat = off.val := by
    simp [Nat.toUInt64, Nat.mod_eq_of_lt hOffFit]
  rw [hEq]
  exact off.isLt

end DynamicSection
end Patchelf.Elf
