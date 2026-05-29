/-
  Adapter: byte-layer `ElfFile` ↔ typed `ValidElfFile`.

  Keeps the byte-layer parser/encoder intact and interposes a
  translation so typed ops become the semantic operators while
  the byte layer remains the wire format.

  The `toElfFile` direction is destructive: it rewrites the
  byte-layer ElfFile's `.dynstr`, `.dynamic`, `.dynsym`, `.versym`,
  `.interp`, `.sysvHash` section contents from the typed values.
  Opaque sections (text / data / rela / …) are preserved
  verbatim because the byte-layer input still holds them (the
  adapter uses that original input as a "template").

  This adapter is deliberately NOT a total semantic round-trip —
  it's the minimum needed for typed-op-through-bytes operation.
-/
module

public import Patchelf.Elf.ElfFile
public import Patchelf.Elf.SectionOps  -- provides ElfFile.updateSectionContent
public import Patchelf.Elf.ValidElfFile
public import Patchelf.Elf.DynamicParse   -- DynamicSection.parseFrom
public import Patchelf.Elf.DynamicEncode  -- DynamicSection.assembleEntries
public import Patchelf.Elf.Schemas        -- decodeVerneedChain / decodeSysVHash / decodeGnuHash + Verneed.write etc.
public import Patchelf.Elf.Serialize      -- writeArray (used by applyVerneed)

@[expose] public section

namespace Patchelf.Elf

open Patchelf.Elf (StringTable Symbol Verneed SysVHashTable GnuHashTable
                     DynEntry ElfHeader ProgramHeader SectionHeader)
open Patchelf.Elf (ElfFile SectionContent)
open Patchelf.Elf.Layout (ShType)

/-- Adapter errors. -/
inductive AdapterError : Type
  /-- A byte-layer Symbol at `idx` has `st_name = offset` ≥ dynstr.size.
      The adapter can't construct a `Fin ds.size` offset; this
      indicates genuinely broken input (the offset points past
      the force-terminated dynstr too). -/
  | symbolNameOutOfBounds (idx : Nat) (offset : UInt32) (dynstrSize : Nat)
  /-- the typed dynamic parser rejected an entry (out-of-bounds string-ref
      value).  Same rationale as symbolNameOutOfBounds. -/
  | dynamicParseFailed (e : DynamicParseError)
  deriving Repr

namespace Adapter

/-! ## ofElfFile: bytes → typed.

    Produces a ValidElfFile with the typed domain fields populated.
    OpaqueSections are NOT reconstructed — the adapter stores only the
    typed-relevant content.  `toElfFile` pairs with `ofElfFile` via a CLI-held
    original-bytes-ref (the CLI keeps the original parsed ElfFile alongside). -/

/-- A fallback well-formed string section used when the byte-layer input has
    a malformed strtab (not null-terminated).

    Constructs a minimal well-formed strtab: just a trailing NUL byte.
    Offsets from the malformed input are then invalid against this
    fallback, which will surface as `symbolNameOutOfBounds` downstream —
    the right behavior because the malformed input couldn't have had
    meaningful offsets anyway. -/
def fallbackStringSection : StringSection :=
  ⟨⟨#[0]⟩, by right; exact ⟨Nat.one_pos, rfl⟩⟩

/-- Wrap a byte-layer StringTable into a typed StringSection.  If well-formed,
    use the original bytes; otherwise use a fallback (leading to
    downstream out-of-bounds errors for any symbol that pointed
    into the malformed region — which is the correct behavior,
    signaling that patchelf cannot meaningfully operate on the input).

    This is strictly more permissive than rejecting at ofElfFile:
    well-formed inputs behave as before; malformed inputs get a
    precise per-symbol error instead of a generic `dynstrNotWellFormed`. -/
def mkStringSection (st : StringTable) : StringSection :=
  if h : st.WellFormed then
    ⟨st.bytes, h⟩
  else
    fallbackStringSection

def mkStringSectionOpt (st? : Option StringTable) : StringSection :=
  match st? with
  | none    => StringSection.empty
  | some st => mkStringSection st

/-- Convert a byte-layer Symbol to a typed TypedSymbol indexed by `ds`. -/
def typedSymOfByteSymbol (ds : StringSection) (idx : Nat) (s : Symbol) :
    Except AdapterError (TypedSymbol ds) :=
  let n := s.st_name.toNat
  if h : n < ds.size then
    .ok { st_name  := ⟨n, h⟩
        , st_info  := s.st_info
        , st_other := s.st_other
        , st_shndx := s.st_shndx
        , st_value := s.st_value
        , st_size  := s.st_size }
  else
    .error (.symbolNameOutOfBounds idx s.st_name ds.size)

/-- Build a typed SymbolSection from a raw byte-layer dynsym array. -/
def symbolSectionOf (ds : StringSection) (syms : Array Symbol) :
    Except AdapterError (SymbolSection ds) := do
  let typed ← syms.mapIdxM (fun i s => typedSymOfByteSymbol ds i s)
  .ok { symbols := typed }

/-- Unwrap `.interp` bytes (strip trailing NUL if present). -/
def interpOfBytes (bs : ByteArray) : InterpSection :=
  -- strip a single trailing NUL if present
  if h : 0 < bs.size then
    if bs[bs.size - 1]'(Nat.sub_lt h (Nat.zero_lt_one)) = 0 then
      ⟨bs.extract 0 (bs.size - 1)⟩
    else ⟨bs⟩
  else ⟨bs⟩

/-- Main ofElfFile: translate a byte-layer ElfFile into a typed ValidElfFile.

    Returns an AdapterError only on offsets that can't be promoted to
    `Fin ds.size` (genuinely broken input — patchelf would have
    nothing meaningful to do).  Malformed strtabs (missing trailing
    NUL) are force-terminated, not rejected. -/
def ofElfFile (e : ElfFile) : Except AdapterError ValidElfFile := do
  let dynstr := mkStringSectionOpt e.dynstr
  let dynsym : Option (SymbolSection dynstr) ←
    match e.dynsym with
    | none => .ok none
    | some syms => do
        let ss ← symbolSectionOf dynstr syms
        .ok (some ss)
  let dynamic : Option (DynamicSection dynstr) ←
    match e.dynamic with
    | none => .ok none
    | some dyn =>
        match DynamicSection.parseFrom dynstr dyn with
        | .ok d     => .ok (some d)
        | .error de => .error (.dynamicParseFailed de)
  -- Materialize verneed / sysvHash / gnuHash from their raw bytes
  -- (these sections are stored as `.raw` at the byte layer; the
  -- typed-section algebra owns the decoded view).  Decoders are
  -- invoked at the byte-layer → typed-layer boundary here.
  let verneed : Option VerneedSection :=
    e.verneedRaw.map fun bs =>
      { entries := Patchelf.Elf.Decode.decodeVerneedChain bs 0 (bs.size / 16) }
  let sysvHash : Option SysVHashSection :=
    e.sysvHashRaw.map fun bs =>
      { table := Patchelf.Elf.Decode.decodeSysVHash bs 0 bs.size }
  let gnuHash : Option GnuHashSection :=
    e.gnuHashRaw.map fun bs =>
      { table := Patchelf.Elf.Decode.decodeGnuHash bs 0 bs.size }
  .ok {
    header   := e.header
    phdrs    := e.phdrs
    dynstr   := dynstr
    dynsym   := dynsym
    dynamic  := dynamic
    versym   := e.versym
    verneed  := verneed
    sysvHash := sysvHash
    gnuHash  := gnuHash
    interp   := e.interp.map interpOfBytes
  }

/-! ## toElfFile: write typed fields back into the byte layer via section-content updates.

    Strategy: take a byte-layer ElfFile "template" (typically the input pre-op)
    + a ValidElfFile "new" (post-op).  Produce a byte-layer ElfFile whose
    section contents are patched to match the typed fields.

    This is robust for patchelf's domain: ops mutate small sets of
    named sections; the adapter rewrites only those.  Opaque sections
    (text/data/etc.) are preserved from the template.
-/

/-- Convert a typed `TypedSymbol` back to byte-layer `Symbol`. -/
def symbolOfTyped {ds : StringSection} (s : TypedSymbol ds) : Symbol :=
  { st_name  := s.st_name.val.toUInt32
  , st_info  := s.st_info
  , st_other := s.st_other
  , st_shndx := s.st_shndx
  , st_value := s.st_value
  , st_size  := s.st_size }

/-- Generic foldl array-size bound: if each step grows the accumulator array
    by at most one element, the result is bounded by `init.size + as.size`. -/
theorem Array.foldl_size_le_add {α β : Type} (as : Array α)
    (f : Array β → α → Array β) (init : Array β)
    (hf : ∀ (acc : Array β) (a : α), (f acc a).size ≤ acc.size + 1) :
    (as.foldl f init).size ≤ init.size + as.size :=
  Array.foldl_induction
    (as := as) (motive := fun n acc => acc.size ≤ init.size + n) (init := init) (f := f)
    (Nat.le_add_right _ _)
    (fun i b hb => calc
      (f b as[i]).size ≤ b.size + 1 := hf b _
      _ ≤ init.size + (↑i + 1) := by omega)

/-- Generalization to a foldl over an arbitrary state `σ`, projecting an
    `Array β` component `π`: if each step grows `π` by ≤ 1, the result's `π`
    is bounded by `(π init).size + as.size`. -/
theorem Array.foldl_proj_size_le_add {α σ β : Type} (as : Array α)
    (f : σ → α → σ) (π : σ → Array β) (init : σ)
    (hf : ∀ (s : σ) (a : α), (π (f s a)).size ≤ (π s).size + 1) :
    (π (as.foldl f init)).size ≤ (π init).size + as.size :=
  Array.foldl_induction
    (as := as) (motive := fun n s => (π s).size ≤ (π init).size + n) (init := init) (f := f)
    (Nat.le_add_right _ _)
    (fun i b hb => calc
      (π (f b as[i])).size ≤ (π b).size + 1 := hf b _
      _ ≤ (π init).size + (↑i + 1) := by omega)

/-- Bridge for bounding an `Id`-monad, yield-only `forIn` loop's projected
    output size: when every step grows the projected `Array β` component by
    ≤ 1, the loop's result is bounded by `(π init).size + as.size`.

    This is the reusable connector for §5.1's `patchDynamicEntries` output-
    size bound (see ROADMAP §5.1 "Remaining per-op work"): the
    `Id.run do … forIn …` loop has exactly this shape with `σ` the 8-tuple
    state and `π` the `result` projection.  Converts the `forIn` to a `foldl`
    via `Array.forIn_eq_foldlM` (Id collapses `foldlM`, steps are always
    `.yield`), then applies `foldl_proj_size_le_add` through `ForInStep.value`. -/
theorem idForIn_proj_size_le {α σ β : Type} (as : Array α)
    (g : α → σ → σ) (π : σ → Array β) (init : σ)
    (hf : ∀ (a : α) (s : σ), (π (g a s)).size ≤ (π s).size + 1) :
    (π (Id.run (forIn as init (fun a s => pure (ForInStep.yield (g a s)))))).size
      ≤ (π init).size + as.size := by
  have hstep : Id.run (forIn as init (fun a s => pure (ForInStep.yield (g a s))))
      = (as.foldl (fun b a => match b with
          | ForInStep.yield b => ForInStep.yield (g a b)
          | ForInStep.done b => ForInStep.done b) (ForInStep.yield init)).value := by
    rw [Array.forIn_eq_foldlM]; rfl
  rw [hstep]
  have := Array.foldl_proj_size_le_add as
    (f := fun b a => match b with
      | ForInStep.yield b => ForInStep.yield (g a b)
      | ForInStep.done b => ForInStep.done b)
    (π := fun b => π b.value) (init := ForInStep.yield init)
    (by
      intro s a
      cases s with
      | yield b => simp only [ForInStep.value]; exact hf a b
      | done b => simp only [ForInStep.value]; omega)
  simpa using this

/-- Surgical patch of a byte-layer dynamic entry array to reflect the typed's changes.

    Key design property: POSITIONAL — every byte-layer DT_NEEDED entry is
    rewritten IN PLACE based on the typed `needed[i]` at the same index.
    This preserves entry ordering across renames (critical: the pre-op
    dynamic `[libfoo, libbar]` renamed `libfoo→libbrand` must produce
    `[libbrand, libbar]`, not `[libbar, libbrand]`).

    Pre-op dynamic entries are matched positionally to the typed `needed` array:
    the N-th DT_NEEDED pre-op becomes the N-th entry in the typed `.needed`. -/
def patchDynamicEntries {ds : StringSection} (byteDyn : Array DynEntry)
    (typed : DynamicSection ds) : Array DynEntry := Id.run do
  -- Count pre-op DT_NEEDED entries for positional pairing.  Ops never
  -- reorder: the typed `.needed`[i] corresponds to the i-th pre-op DT_NEEDED entry
  -- (for entries the typed version still contains; surplus go to the end).
  let mut result : Array DynEntry := #[]
  let mut typedNeededIdx : Nat := 0
  let mut flags1Applied := false
  let mut debugApplied := false
  let mut rpathApplied := false
  let mut runpathApplied := false
  let mut sonameApplied := false
  let mut nullEntry : DynEntry := { tag := Patchelf.Elf.DynTag.null, value := 0 }
  for d in byteDyn do
    match d.tag with
    | .null =>
        nullEntry := d
    | .needed =>
        -- Positional match: take the typed needed[typedNeededIdx] (if any).
        -- Extra pre-op entries (typed dropped some) get filtered; extra typed
        -- entries (typed added some) are appended after the loop.
        if hLt : typedNeededIdx < typed.needed.size then
          let off := (typed.needed[typedNeededIdx]'hLt).val.toUInt64
          result := result.push { d with value := off }
          typedNeededIdx := typedNeededIdx + 1
        -- else: typed has fewer NEEDED entries than pre-op (remove-needed) → skip.
    | .rpath =>
        match typed.rpath with
        | some off =>
            result := result.push { d with value := off.val.toUInt64 }
            rpathApplied := true
        | none => pure ()
    | .runpath =>
        match typed.runpath with
        | some off =>
            result := result.push { d with value := off.val.toUInt64 }
            runpathApplied := true
        | none => pure ()
    | .soname =>
        match typed.soname with
        | some off =>
            result := result.push { d with value := off.val.toUInt64 }
            sonameApplied := true
        | none => pure ()
    | .flags1 =>
        match typed.flags1 with
        | some v =>
            result := result.push { d with value := v }
            flags1Applied := true
        | none => pure ()
    | .debug =>
        match typed.debug with
        | some v =>
            result := result.push { d with value := v }
            debugApplied := true
        | none => pure ()
    | _ =>
        -- Other tags: preserve verbatim.
        result := result.push d
  -- Append any typed NEEDED entries we didn't consume (typed has more NEEDEDs
  -- than pre-op → addNeeded path).
  while h : typedNeededIdx < typed.needed.size do
    let off := (typed.needed[typedNeededIdx]'h).val.toUInt64
    result := result.push { tag := Patchelf.Elf.DynTag.needed, value := off }
    typedNeededIdx := typedNeededIdx + 1
  -- Append structured fields the typed ValidElfFile has but pre-op didn't.
  unless flags1Applied do
    match typed.flags1 with
    | some v => result := result.push { tag := Patchelf.Elf.DynTag.flags1, value := v }
    | none => pure ()
  unless debugApplied do
    match typed.debug with
    | some v => result := result.push { tag := Patchelf.Elf.DynTag.debug, value := v }
    | none => pure ()
  unless rpathApplied do
    match typed.rpath with
    | some off =>
        result := result.push
          { tag := Patchelf.Elf.DynTag.rpath, value := off.val.toUInt64 }
    | none => pure ()
  unless runpathApplied do
    match typed.runpath with
    | some off =>
        result := result.push
          { tag := Patchelf.Elf.DynTag.runpath, value := off.val.toUInt64 }
    | none => pure ()
  unless sonameApplied do
    match typed.soname with
    | some off =>
        result := result.push
          { tag := Patchelf.Elf.DynTag.soname, value := off.val.toUInt64 }
    | none => pure ()
  -- Append DT_NULL terminator.
  result := result.push nullEntry
  return result

/-! ## toElfFile section-update helpers.

    Each `applyX` function updates one section kind on the byte-layer ElfFile,
    preserving header/phdrs.  toElfFile composes them then overrides
    header/phdrs from typed as its last step — this shape makes the
    round-trip theorems `(toElfFile t typed).header = typed.header` rfl-provable. -/

/-- Generic optional-section apply: when `e` has section index `idx?` and
    the typed bundle exposes value `val?`, replace the section's content
    with `mkContent val`; otherwise leave `e` alone.  Used by every
    apply except `applyDynstr` (whose dynstr is non-optional) and
    `applyDynamic` (whose absent-byte-side fallback synthesizes entries). -/
def applyOpt {α : Type} (e : ElfFile) (idx? : Option Nat) (val? : Option α)
    (mkContent : α → SectionContent) : ElfFile :=
  match idx?, val? with
  | some i, some v => e.updateSectionContent i (mkContent v)
  | _, _           => e

/-- Each `applyX` takes the typed *fields* it needs as explicit arguments,
    rather than the whole `typed : ValidElfFile`.  Critically, the
    dependent-`Option` fields (`dynsym`/`dynamic`, indexed by the string
    section `ds`) are passed with `ds` as a free variable.  This is what
    makes `toElfFile (op typed)` reduce for ops that don't touch the
    section fields: a header-only op like `setOsAbi` leaves `ds`,
    `dynsym`, `dynamic`, … syntactically unchanged, so the dependent
    matches in `applyDynamic`/`applyDynsym` still compute.  (Passing the
    bundled `typed` instead made the index `typed.dynstr` become
    `({typed with header := …}).dynstr`, which blocks the dependent match
    from reducing even though the two are `rfl`-equal — see ROADMAP §5.1.) -/
def applyDynstr (e : ElfFile) (ds : StringSection) : ElfFile :=
  match e.dynstrIdx with
  | none     => e
  | some iDs => e.updateSectionContent iDs (.strtab ⟨ds.bytes⟩)

def applyDynsym (e : ElfFile) {ds : StringSection}
    (dynsym? : Option (SymbolSection ds)) : ElfFile :=
  applyOpt e e.dynsymIdx dynsym? fun ts =>
    .dynsym (ts.symbols.map symbolOfTyped)

def applyDynamic (e : ElfFile) {ds : StringSection}
    (dynamic? : Option (DynamicSection ds)) : ElfFile :=
  match e.dynamicIdx, dynamic? with
  | some iDyn, some typedDyn =>
      match e.dynamic with
      | some byteDyn => e.updateSectionContent iDyn
          (.dynamic (patchDynamicEntries byteDyn typedDyn))
      | none =>
          let ctx : LayoutCtx :=
            { dynstrAddr := 0, dynsymAddr := none, hashAddr := none
            , gnuHashAddr := none, verneedAddr := none }
          e.updateSectionContent iDyn (.dynamic (typedDyn.assembleEntries ctx))
  | _, _ => e

def applyVersym (e : ElfFile) (versym? : Option (Array UInt16)) : ElfFile :=
  applyOpt e e.versymIdx versym? .versym

def applySysvHash (e : ElfFile) (sysvHash? : Option SysVHashSection) : ElfFile :=
  applyOpt e e.sysvHashIdx sysvHash? fun shs =>
    .raw Layout.ShType.SHT_HASH (by decide) (SysVHashTable.write shs.table)

def applyGnuHash (e : ElfFile) (gnuHash? : Option GnuHashSection) : ElfFile :=
  applyOpt e e.gnuHashIdx gnuHash? fun ghs =>
    .raw Layout.ShType.SHT_GNU_HASH (by decide) (GnuHashTable.write ghs.table)

def applyVerneed (e : ElfFile) (verneed? : Option VerneedSection) : ElfFile :=
  applyOpt e e.verneedIdx verneed? fun vn =>
    .raw Layout.ShType.SHT_GNU_VERNEED (by decide) (writeArray Verneed.write vn.entries)

def applyInterp (e : ElfFile) (interp? : Option InterpSection) : ElfFile :=
  applyOpt e e.interpIdx interp? fun ip =>
    .raw Layout.ShType.SHT_PROGBITS (by decide) ip.toBytes

/-- Apply a ValidElfFile's contents back onto a byte-layer ElfFile template.

    Structure: extract the typed fields once (so the dependent-`Option`
    indices stay free variables — see the `applyX` note above), compose
    the per-section updates, then override header and phdrs from typed as
    the final step.  The final record override makes
    `(toElfFile t typed).header = typed.header` rfl-provable, and the
    un-bundled section args make `toElfFile t (op typed)` reduce for
    section-trivial ops. -/
def toElfFile (template : ElfFile) (typed : ValidElfFile) : ElfFile :=
  let ds := typed.dynstr
  let e := applyInterp (applyVerneed (applyGnuHash (applySysvHash
             (applyVersym (applyDynamic (applyDynsym
               (applyDynstr template ds) (ds := ds) typed.dynsym)
               (ds := ds) typed.dynamic) typed.versym) typed.sysvHash)
               typed.gnuHash) typed.verneed) typed.interp
  { e with header := typed.header, phdrs := typed.phdrs }

end Adapter
end Patchelf.Elf
