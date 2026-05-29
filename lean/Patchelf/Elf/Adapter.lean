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

/-! ## `patchDynamicEntries`: surgical patch of a byte-layer dynamic entry array.

    Key design property: POSITIONAL — every byte-layer DT_NEEDED entry is
    rewritten IN PLACE based on the typed `needed[i]` at the same index.
    This preserves entry ordering across renames (critical: the pre-op
    dynamic `[libfoo, libbar]` renamed `libfoo→libbrand` must produce
    `[libbrand, libbar]`, not `[libbar, libbrand]`).

    Pre-op dynamic entries are matched positionally to the typed `needed`
    array: the N-th DT_NEEDED pre-op becomes the N-th entry in the typed
    `.needed`.

    Implementation note: this was originally a single `Id.run do … for …
    while … unless …` block.  It is now split into a pure loop fold
    (`patchStep` over `byteDyn`) plus explicit tail-append helpers
    (`appendSurplusNeeded` for the `while`, `appendUnless` for the five
    trailing `unless`-blocks).  The two forms are byte-identical (no theorem
    or test depends on the internal shape); the compositional form is what
    lets the §5.1 output-size bound (`patchDynamicEntries_stripRpath_size_le`)
    compose — the desugared `do`-block's `__do_jp` join-points defeated the
    size induction. -/

/-- Loop-carried state for the positional dynamic patch: the running
    `result`, the NEEDED positional cursor, the five "already applied"
    flags for the trailing-append blocks, and the carried DT_NULL entry. -/
structure PatchState (ds : StringSection) where
  result         : Array DynEntry
  typedNeededIdx : Nat
  flags1Applied  : Bool
  debugApplied   : Bool
  rpathApplied   : Bool
  runpathApplied : Bool
  sonameApplied  : Bool
  nullEntry      : DynEntry

/-- Per-entry loop step (pure).  Mirrors the original `for`-loop body:
    DT_NULL is carried (last wins), DT_NEEDED is positionally matched to
    `typed.needed[typedNeededIdx]`, the singleton string-ref / scalar tags
    push their typed value (recording the corresponding `*Applied` flag),
    and every other tag is preserved verbatim. -/
def patchStep {ds : StringSection} (typed : DynamicSection ds)
    (st : PatchState ds) (d : DynEntry) : PatchState ds :=
  match d.tag with
  | .null => { st with nullEntry := d }
  | .needed =>
      if hLt : st.typedNeededIdx < typed.needed.size then
        { st with
            result := st.result.push { d with value := (typed.needed[st.typedNeededIdx]'hLt).val.toUInt64 }
            typedNeededIdx := st.typedNeededIdx + 1 }
      else st
  | .rpath =>
      match typed.rpath with
      | some off => { st with result := st.result.push { d with value := off.val.toUInt64 }, rpathApplied := true }
      | none => st
  | .runpath =>
      match typed.runpath with
      | some off => { st with result := st.result.push { d with value := off.val.toUInt64 }, runpathApplied := true }
      | none => st
  | .soname =>
      match typed.soname with
      | some off => { st with result := st.result.push { d with value := off.val.toUInt64 }, sonameApplied := true }
      | none => st
  | .flags1 =>
      match typed.flags1 with
      | some v => { st with result := st.result.push { d with value := v }, flags1Applied := true }
      | none => st
  | .debug =>
      match typed.debug with
      | some v => { st with result := st.result.push { d with value := v }, debugApplied := true }
      | none => st
  | _ => { st with result := st.result.push d }

/-- Initial loop state (empty result, cursor 0, no flags applied, default
    DT_NULL). -/
def patchInit (ds : StringSection) : PatchState ds where
  result         := #[]
  typedNeededIdx := 0
  flags1Applied  := false
  debugApplied   := false
  rpathApplied   := false
  runpathApplied := false
  sonameApplied  := false
  nullEntry      := { tag := Patchelf.Elf.DynTag.null, value := 0 }

/-- Append the typed NEEDED entries the loop did not consume (the original
    trailing `while`: `typed` has more DT_NEEDED than the byte template, i.e.
    the addNeeded path).  Folds over `range (needed.size - startIdx)`. -/
def appendSurplusNeeded {ds : StringSection} (typed : DynamicSection ds)
    (result : Array DynEntry) (startIdx : Nat) : Array DynEntry :=
  (List.range (typed.needed.size - startIdx)).foldl
    (fun acc k =>
      let i := startIdx + k
      if h : i < typed.needed.size then
        acc.push { tag := Patchelf.Elf.DynTag.needed, value := (typed.needed[i]'h).val.toUInt64 }
      else acc)
    result

/-- One trailing `unless`-block: append a `{tag, v}` entry iff the field was
    not already applied in the loop and the typed bundle carries a value. -/
def appendUnless (applied : Bool) (result : Array DynEntry)
    (tag : DynTag) (val? : Option UInt64) : Array DynEntry :=
  if applied then result
  else match val? with
       | some v => result.push { tag := tag, value := v }
       | none   => result

def patchDynamicEntries {ds : StringSection} (byteDyn : Array DynEntry)
    (typed : DynamicSection ds) : Array DynEntry :=
  let st := byteDyn.foldl (patchStep typed) (patchInit ds)
  let r := appendSurplusNeeded typed st.result st.typedNeededIdx
  let r := appendUnless st.flags1Applied r Patchelf.Elf.DynTag.flags1 typed.flags1
  let r := appendUnless st.debugApplied r Patchelf.Elf.DynTag.debug typed.debug
  let r := appendUnless st.rpathApplied r Patchelf.Elf.DynTag.rpath (typed.rpath.map (·.val.toUInt64))
  let r := appendUnless st.runpathApplied r Patchelf.Elf.DynTag.runpath (typed.runpath.map (·.val.toUInt64))
  let r := appendUnless st.sonameApplied r Patchelf.Elf.DynTag.soname (typed.soname.map (·.val.toUInt64))
  r.push st.nullEntry

/-! ## `patchDynamicEntries` output-size bound for shrinking ops (§5.1)

    A shrinking op (`removeRpath`/`removeNeeded`) feeds `patchDynamicEntries`
    a typed section that is "field-wise smaller" than the no-op one, so its
    byte output is no larger.  The bound below is *relative* — op output vs.
    NO-OP output on the SAME `byteDyn` — which is exactly what the
    `SectionOps.updateSectionContent_*Disjoint_shrink` lemmas consume (and is
    provable with no parse-balance preconditions, unlike an absolute
    `≤ byteDyn.size`).

    The proof is a lockstep fold over `byteDyn` (`Array.foldl_rel`) that
    tracks `ShrinkRel` (result no bigger + matching NEEDED cursor + matching
    `flags1`/`debug`/`soname` applied-flags), followed by a tail bound:
    `stripRpath` only nulls `rpath`/`runpath`, so its trailing `unless`-blocks
    for those become no-ops while every other tail block is shared. -/

/-- Relational fold (list form): if `R` is preserved by each step in lockstep
    on the same element, `R` holds of the two folds' results. -/
private theorem List.foldl_rel {α : Type} {S T : Type} (R : S → T → Prop)
    (f : S → α → S) (g : T → α → T)
    (hstep : ∀ s t a, R s t → R (f s a) (g t a)) :
    ∀ (l : List α) (s0 : S) (t0 : T), R s0 t0 → R (l.foldl f s0) (l.foldl g t0) := by
  intro l
  induction l with
  | nil => intro s0 t0 h0; simpa using h0
  | cons a tl ih =>
      intro s0 t0 h0
      rw [List.foldl_cons, List.foldl_cons]
      exact ih (f s0 a) (g t0 a) (hstep s0 t0 a h0)

/-- Relational fold (array form): two array folds in lockstep preserve `R`. -/
theorem Array.foldl_rel {α : Type} {S T : Type} (R : S → T → Prop)
    (f : S → α → S) (g : T → α → T)
    (hstep : ∀ s t a, R s t → R (f s a) (g t a))
    (as : Array α) (s0 : S) (t0 : T) (h0 : R s0 t0) :
    R (as.foldl f s0) (as.foldl g t0) := by
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  exact List.foldl_rel R f g hstep as.toList s0 t0 h0

/-- The relation carried by the lockstep loop fold for a shrinking op:
    the op-side `result` is no bigger, and the NEEDED cursor + the three
    applied-flags the tail blocks read agree. -/
def ShrinkRel {ds : StringSection} (st2 st1 : PatchState ds) : Prop :=
  st2.result.size ≤ st1.result.size ∧ st2.typedNeededIdx = st1.typedNeededIdx ∧
  st2.flags1Applied = st1.flags1Applied ∧ st2.debugApplied = st1.debugApplied ∧
  st2.sonameApplied = st1.sonameApplied

/-- One loop step preserves `ShrinkRel` for the `stripRpath` shrink: the two
    typed sections agree on `needed`/`soname`/`flags1`/`debug`, and `stripRpath`'s
    `rpath`/`runpath` are `none` (so its `.rpath`/`.runpath` arms never push). -/
theorem patchStep_shrink_rpath {ds : StringSection} (typed : DynamicSection ds)
    (st2 st1 : PatchState ds) (d : DynEntry)
    (hR : ShrinkRel st2 st1) :
    ShrinkRel (patchStep typed.stripRpath st2 d) (patchStep typed st1 d) := by
  obtain ⟨hSz, hIdx, _, _, _⟩ := hR
  have hRp : (typed.stripRpath).rpath = none := rfl
  have hRun : (typed.stripRpath).runpath = none := rfl
  have hNd : (typed.stripRpath).needed = typed.needed := rfl
  have hSn : (typed.stripRpath).soname = typed.soname := rfl
  have hF1 : (typed.stripRpath).flags1 = typed.flags1 := rfl
  have hDbg : (typed.stripRpath).debug = typed.debug := rfl
  cases hd : d.tag <;>
    simp only [patchStep, ShrinkRel, hd, hRp, hRun, hNd, hSn, hF1, hDbg, hIdx] <;>
    (try split) <;>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    first
      | (simp only [Array.size_push]; omega)
      | omega
      | assumption
      | rfl
      | simp_all

/-- Loop-level shrink: the whole `byteDyn` fold preserves `ShrinkRel`. -/
theorem loop_shrink_rpath {ds : StringSection} (typed : DynamicSection ds)
    (byteDyn : Array DynEntry) :
    ShrinkRel (byteDyn.foldl (patchStep typed.stripRpath) (patchInit ds))
              (byteDyn.foldl (patchStep typed) (patchInit ds)) := by
  apply Array.foldl_rel ShrinkRel (patchStep typed.stripRpath) (patchStep typed)
    (fun s t a h => patchStep_shrink_rpath typed s t a h) byteDyn
  exact ⟨Nat.le_refl _, rfl, rfl, rfl, rfl⟩

/-- `appendSurplusNeeded` is size-monotone in the result it extends (the
    surplus count `needed.size - startIdx` is shared; only the base differs). -/
theorem appendSurplusNeeded_size_mono {ds : StringSection} (typed : DynamicSection ds)
    (r2 r1 : Array DynEntry) (startIdx : Nat) (h : r2.size ≤ r1.size) :
    (appendSurplusNeeded typed r2 startIdx).size
      ≤ (appendSurplusNeeded typed r1 startIdx).size := by
  unfold appendSurplusNeeded
  apply List.foldl_rel (fun (a b : Array DynEntry) => a.size ≤ b.size)
  · intro a b k hab
    dsimp only
    split <;> (try simp only [Array.size_push]) <;> omega
  · exact h

/-- `appendUnless` adds at most one entry. -/
theorem appendUnless_size_le (applied : Bool) (result : Array DynEntry)
    (tag : DynTag) (val? : Option UInt64) :
    (appendUnless applied result tag val?).size ≤ result.size + 1 := by
  unfold appendUnless
  split
  · omega
  · split <;> (try simp only [Array.size_push]) <;> omega

/-- `appendUnless` never shrinks the result. -/
theorem appendUnless_size_ge (applied : Bool) (result : Array DynEntry)
    (tag : DynTag) (val? : Option UInt64) :
    result.size ≤ (appendUnless applied result tag val?).size := by
  unfold appendUnless
  split
  · omega
  · split <;> (try simp only [Array.size_push]) <;> omega

/-- `appendUnless` with `none` value is a no-op on size. -/
theorem appendUnless_size_none (applied : Bool) (result : Array DynEntry)
    (tag : DynTag) :
    (appendUnless applied result tag none).size = result.size := by
  unfold appendUnless; split <;> rfl

/-- `appendUnless` is size-monotone in its result argument. -/
theorem appendUnless_size_mono (applied : Bool) (r2 r1 : Array DynEntry)
    (tag : DynTag) (val? : Option UInt64) (h : r2.size ≤ r1.size) :
    (appendUnless applied r2 tag val?).size ≤ (appendUnless applied r1 tag val?).size := by
  unfold appendUnless
  split
  · exact h
  · split <;> (try simp only [Array.size_push]) <;> omega

/-- Tail bound: given the loop relation on two states with matching
    `needed`/`soname`/`flags1`/`debug` and `rpath`/`runpath` cleared on the
    `st2` (op) side, the full tail (surplus + 5 `unless`-blocks + null push)
    of `st2` is no larger than `st1`'s.  This is the `removeRpath`-shaped tail;
    `typed.{rpath,runpath}` on the `st2` side are `none`. -/
theorem tail_shrink_rpath {ds : StringSection} (typed : DynamicSection ds)
    (st2 st1 : PatchState ds) (hR : ShrinkRel st2 st1) :
    (let r := appendSurplusNeeded typed st2.result st2.typedNeededIdx
     let r := appendUnless st2.flags1Applied r DynTag.flags1 typed.flags1
     let r := appendUnless st2.debugApplied r DynTag.debug typed.debug
     let r := appendUnless st2.rpathApplied r DynTag.rpath (none : Option UInt64)
     let r := appendUnless st2.runpathApplied r DynTag.runpath (none : Option UInt64)
     let r := appendUnless st2.sonameApplied r DynTag.soname (typed.soname.map (·.val.toUInt64))
     r.push st2.nullEntry).size
      ≤
    (let r := appendSurplusNeeded typed st1.result st1.typedNeededIdx
     let r := appendUnless st1.flags1Applied r DynTag.flags1 typed.flags1
     let r := appendUnless st1.debugApplied r DynTag.debug typed.debug
     let r := appendUnless st1.rpathApplied r DynTag.rpath (typed.rpath.map (·.val.toUInt64))
     let r := appendUnless st1.runpathApplied r DynTag.runpath (typed.runpath.map (·.val.toUInt64))
     let r := appendUnless st1.sonameApplied r DynTag.soname (typed.soname.map (·.val.toUInt64))
     r.push st1.nullEntry).size := by
  obtain ⟨hSz, hIdx, hF1, hDbg, hSn⟩ := hR
  simp only [Array.size_push, hIdx, hF1, hDbg, hSn]
  refine Nat.add_le_add_right ?_ 1
  -- soname layer: shared value → monotone in inner arg
  refine appendUnless_size_mono _ _ _ _ _ ?_
  -- LHS runpath + rpath are `none` → no-ops; drop both
  rw [appendUnless_size_none, appendUnless_size_none]
  -- RHS: the extra runpath then rpath unless-layers only grow size
  refine Nat.le_trans ?_ (appendUnless_size_ge _ _ _ _)
  refine Nat.le_trans ?_ (appendUnless_size_ge _ _ _ _)
  -- debug + flags1 layers: shared → monotone; surplus: monotone via hSz
  refine appendUnless_size_mono _ _ _ _ _ ?_
  refine appendUnless_size_mono _ _ _ _ _ ?_
  exact appendSurplusNeeded_size_mono _ _ _ _ hSz

/-- §5.1 output-size bound for `removeRpath`: `stripRpath`'s byte output is
    no larger than the no-op output on the same byte template.  Feeds the
    `SectionOps` shrink-monotonicity lemmas for the per-op structural-invariant
    discharge. -/
theorem patchDynamicEntries_stripRpath_size_le {ds : StringSection}
    (byteDyn : Array DynEntry) (typed : DynamicSection ds) :
    (patchDynamicEntries byteDyn (typed.stripRpath)).size
      ≤ (patchDynamicEntries byteDyn typed).size := by
  unfold patchDynamicEntries
  exact tail_shrink_rpath typed _ _ (loop_shrink_rpath typed byteDyn)

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
