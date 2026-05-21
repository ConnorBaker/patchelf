/-
  `elf_schema` command elaborator.

  Compresses the hand-written boilerplate for each fixed-layout ELF
  struct into one schema declaration. The DSL operates on an
  **already-declared** structure — the user writes the `structure Foo
  where ...` by hand, then invokes `elf_schema` to generate up to
  seven serialization artifacts:

  1. `def Foo.write : Foo → ByteArray` — a chain of `writeUN` appends.
  2. `def Decode.decodeFoo : ByteArray → Nat → Foo` — a record literal
     of per-field `readUN bs (off + k)` reads.
  3. `@[simp] theorem Foo.write_size : (Foo.write x).size = N` — the
     size lemma; `@[simp]` so downstream `by simp` calls on size
     obligations close automatically.
  4. `theorem Foo_write_decodeFoo_extract : ∀ bs off,
     off + N ≤ bs.size → Foo.write (decodeFoo bs off) = bs.extract
     off (off + N)` — the byte-level roundtrip theorem.
  5. `def ByteWidth.of_Foo : ByteWidth Foo` — the `ByteWidth` bundle
     feeding the array-level `writeArray_of_width` combinator.
  6. `theorem writeArray_Foo_write_extract : …` — array-lift of (4),
     a thin wrapper over `writeArray_of_width`.
  7. Opt-in via `with_array_decoder N`: `def Decode.N`,
     `theorem Decode.N_size`, `theorem Decode.N_getElem` — a fixed-
     count-array decoder bundle wrapping `Decode.buildArray`.

  **Worked example** — the hand-written

      structure Vernaux where
        vna_hash  : UInt32
        vna_flags : UInt16
        vna_other : UInt16
        vna_name  : UInt32
        vna_next  : UInt32

  plus the declaration

      elf_schema Vernaux := 16
        vna_hash  : u32 @ 0
        vna_flags : u16 @ 4
        vna_other : u16 @ 6
        vna_name  : u32 @ 8
        vna_next  : u32 @ 12

  replaces ~100 LOC of hand-written `write` + `decode` + size lemma +
  byte-roundtrip proof + `ByteWidth` instance.

  **Wrapper-type fields.** Fields whose Lean type is a one-field
  structure wrapping a primitive (e.g. `FileOffset { val : UInt64 }`,
  `PhType { raw : UInt32 }`) are declared with the `wrap` suffix:

      elf_schema ProgramHeader := 56
        type   : u32 @ 0 wrap PhType raw
        offset : u64 @ 8 wrap FileOffset val
        ...

  The generated decoder constructs the wrapper via anonymous
  constructor (`⟨readUN bs ...⟩`); the writer projects via the named
  field (`x.offset.val`). Both the wrapper type and projection name
  are required because the macro doesn't introspect structure decls.

  **Options.** Between `:= TOTAL` and the field list, the caller may
  place any of:
    * `decode_as <ident>` — decoder function name (default
      `decodeFoo`; pass e.g. `decodePhdr` to match existing conventions)
    * `roundtrip_as <ident>` — roundtrip theorem name (default
      `Foo_write_decodeFoo_extract`)
    * `bytewidth_as <ident>` — `ByteWidth` instance name (default
      `of_Foo`; pass e.g. `phdr` to match existing call sites)
    * `skip_write` — caller supplies `Foo.write` + `Foo.write_size`
    * `skip_decode` — caller supplies the decoder function
    * `skip_bytewidth` — do not emit the `ByteWidth` bundle nor the
      array-lift theorem (required for decoders that take a
      precondition; see `raw_bytes ... with_size_field ...` and
      `embed ... with_prec ...` below)
    * `with_array_decoder <ident>` — additionally emit the fixed-
      count-array decoder bundle under `Decode.<ident>`

  The `skip_*` flags allow mixing DSL-emitted artifacts with
  hand-written ones: they let the DSL emit just the roundtrip
  theorem + ByteWidth instance while the hand-written write/decode
  remain.

  **Out of scope.** Variable-length structures whose on-disk size
  isn't known at compile time — the Verneed / Vernaux chain (linked-
  list shape via `.vna_next` / `.vn_next` offsets) and the SysV /
  GNU hash tables (counts in header govern array lengths) — remain
  hand-written in `Patchelf/Elf/Schemas.lean`.  Their write /
  decode / byte-roundtrip lemmas are there rather than here because
  the DSL assumes a fixed byte layout.

  **Users.** All in-tree fixed-layout structs are driven by
  `elf_schema`: `DynEntry`, `ElfIdent`, `Vernaux`, `Symbol`,
  `ProgramHeader`, `SectionHeader`, `ElfHeader` (see
  `Patchelf/Elf/Schemas.lean`).
-/

import Lean
import Patchelf.Elf.ByteLevel

namespace Patchelf.Elf.SchemaDSL

open Lean Elab Command Meta
open Patchelf.Elf

/-! ## DSL syntax -/

-- Declare the syntax categories.  `elfSchemaWidth` is a one-of-four
-- primitive width token; `elfSchemaField` is dispatched by
-- individual `syntax (name := fieldX) ... : elfSchemaField` rules.
declare_syntax_cat elfSchemaWidth
declare_syntax_cat elfSchemaField

/-- Primitive width tokens.  Declared as separate rules under a
    `declare_syntax_cat` so the resulting `TSyntax `elfSchemaWidth`
    type is at root (rather than namespace-qualified as it would be
    with a plain `syntax elfSchemaWidth := ...` rule). -/
syntax "u8"  : elfSchemaWidth
syntax "u16" : elfSchemaWidth
syntax "u32" : elfSchemaWidth
syntax "u64" : elfSchemaWidth

/-- Each field-kind rule is a separate parser for `elfSchemaField`.
    The DSL supports 6 kinds (8 named syntax rules; `fieldRaw`
    vs `fieldRawSf` and `fieldEmbed` vs `fieldEmbedPrec` differ
    only in optional clauses):
    1. plain primitive: `name : width @ offset`
    2. wrapped primitive (UIntN-backed):
       `name : width @ offset wrap WT proj`
    3. wrapped primitive (Nat-backed):
       `name : width @ offset wrap_nat WT proj`
       (used by the Nat-backed wrappers in Layout.lean —
       FileOffset / VirtualAddr / PhysicalAddr / ByteSize / Alignment)
    4. codec primitive: `name : CType via width @ offset
       codec encodeFn decodeFn reverseId forwardId`
       (`reverseId : ∀ u, encodeFn (decodeFn u) = u` for the
       byte-roundtrip; `forwardId : ∀ x, decodeFn (encodeFn x) = x`
       for the forward roundtrip).
    5. raw bytes: `name : raw_bytes N @ offset [with_size_field sf]`
    6. embedded sub-struct: `name : embed SubType bytes N
       write_as W decode_as D roundtrip_as R
       [forward_as F append_left_as AL] @ offset [with_prec]` -/

syntax (name := fieldPrim)
  ident " : " elfSchemaWidth " @ " num : elfSchemaField

syntax (name := fieldWrap)
  ident " : " elfSchemaWidth " @ " num &"wrap" ident ident : elfSchemaField

/-- Wrapped primitive whose underlying field type is `Nat` (rather than
    `UIntN`).  Decoder emits `name := ⟨(readUN bs ...).toNat⟩`; writer
    emits `writeUN x.name.proj.toUInt{N}`.  Used for the 5 wrappers
    (`FileOffset`, `VirtualAddr`, `PhysicalAddr`, `ByteSize`,
    `Alignment`) whose `val` is `Nat` so layout-engine arithmetic
    isn't bottlenecked by UInt64 fit obligations.

    The byte-roundtrip closes via `UInt{N}.ofNat_toNat` (the
    `(u : UInt{N}).toNat.toUInt{N} = u` direction; unconditional).

    The forward roundtrip carries a `< UInt{N}.size` precondition per
    wrap_nat field; the DSL emits these as hypotheses and threads
    them through via `UInt{N}.toNat_ofNat_of_lt'`. -/
syntax (name := fieldWrapNat)
  ident " : " elfSchemaWidth " @ " num &"wrap_nat" ident ident : elfSchemaField

syntax (name := fieldCodec)
  ident " : " ident &"via" elfSchemaWidth " @ " num
    &"codec" ident ident ident ident : elfSchemaField

syntax (name := fieldRaw)
  ident " : " &"raw_bytes" num " @ " num : elfSchemaField

syntax (name := fieldRawSf)
  ident " : " &"raw_bytes" num " @ " num &"with_size_field" ident
    : elfSchemaField

syntax (name := fieldEmbed)
  ident " : " &"embed" ident &"bytes" num
    &"write_as" ident &"decode_as" ident &"roundtrip_as" ident " @ " num
    : elfSchemaField

/-- Variant of `embed` for sub-structs whose decoder itself takes a
    precondition `(h : off + N ≤ bs.size)` (e.g. because the sub-struct
    uses raw_bytes-with-size-field). The generated outer decoder
    passes through a derived proof. The outer schema must be
    `skip_bytewidth`.

    The trailing `forward_as` + `append_left_as` clauses name the
    sub-struct's forward roundtrip lemma `<sub>_decode_write` and
    the prefix-peel helper `<decodeName>_append_left`.  These are
    consumed by the outer schema's forward roundtrip emission
    (`Foo_decode_write` for the embedding struct). -/
syntax (name := fieldEmbedPrec)
  ident " : " &"embed" ident &"bytes" num &"with_prec"
    &"write_as" ident &"decode_as" ident &"roundtrip_as" ident
    &"forward_as" ident &"append_left_as" ident " @ " num
    : elfSchemaField

/-- Optional overrides + skip flags. Placed between `:= TOTAL` and the
    field list:
    * `decode_as <ident>` — decoder function name (default `decodeFoo`)
    * `roundtrip_as <ident>` — roundtrip theorem name
    * `bytewidth_as <ident>` — ByteWidth instance name
    * `skip_write` — the caller supplies `Foo.write` + `Foo.write_size`
      by hand; the DSL skips emitting them.
    * `skip_decode` — the caller supplies the decoder by hand; the DSL
      skips emitting it (but still references it by the `decode_as`
      name when building the roundtrip theorem and ByteWidth instance).
    * `skip_bytewidth` — the DSL skips emitting the `ByteWidth` bundle
      instance. Required for schemas whose decoder takes a precondition
      arg (structs with `raw_bytes … with_size_field …`) because the
      `ByteWidth.read` signature is preconditionless.

    `skip_write` implies the caller is responsible for the
    `Foo.write_size` simp lemma too — it's needed by the ByteWidth
    instance's `write_size` field. -/
syntax elfSchemaDecodeAs := "decode_as" ident

syntax elfSchemaRoundtripAs := "roundtrip_as" ident

syntax elfSchemaByteWidthAs := "bytewidth_as" ident

syntax elfSchemaSkipWrite := "skip_write"

syntax elfSchemaSkipDecode := "skip_decode"

syntax elfSchemaSkipByteWidth := "skip_bytewidth"

/-- Opt-in emission of the fixed-count-array decoder bundle:
    `with_array_decoder <Name>` emits `Name`, `Name_size`,
    `Name_getElem` as a thin wrapper over `Decode.buildArray`. Used
    by structs that the parser decodes in bulk (`decodePhdrs`,
    `decodeShdrs`, `decodeDynsym`). -/
syntax elfSchemaArrayDecoder := "with_array_decoder" ident

syntax elfSchemaOpt :=
  elfSchemaDecodeAs <|> elfSchemaRoundtripAs <|> elfSchemaByteWidthAs
    <|> elfSchemaSkipWrite <|> elfSchemaSkipDecode <|> elfSchemaSkipByteWidth
    <|> elfSchemaArrayDecoder

/-- `elf_schema Foo := TOTAL` followed by optional name-override clauses
    (`decode_as decodeFoo`, `roundtrip_as Foo_write_extract`) and indented
    field entries. `TOTAL` is the sum of the field widths; redundant but
    self-documenting and checked by the macro. -/
syntax (name := elfSchemaCmd) "elf_schema " ident " := " num
    elfSchemaOpt* elfSchemaField* : command

/-! ## Internal representation

    Each `FieldSpec` has a common header (`name`, `offset`, `byteSize`)
    plus a kind-specific payload. `byteSize` is the on-disk size the
    field occupies; for primitive/codec it's the primitive width, for
    raw_bytes it's `N`, for embed it's the sub-struct's size. -/

private inductive FieldKind where
  /-- Plain primitive: `UInt{8,16,32,64}`. `width` is in bytes. -/
  | primitive (width : Nat)
  /-- Wrapped primitive: the Lean-level field type is a 1-field
      structure around a primitive. `width` is in bytes;
      `wrapperType` is the one-field structure's name;
      `projection` is the primitive field inside it. -/
  | wrapped   (width : Nat) (wrapperType : Name) (projection : Name)
  /-- Wrapped primitive whose underlying field type is `Nat`.  `width`
      is in bytes (the on-disk UIntN width).  Decoder converts via
      `.toNat`; writer converts back via `.toUInt{N}`.  Forward
      roundtrip carries a `< UInt{N}.size` fit precondition. -/
  | wrappedNat (width : Nat) (wrapperType : Name) (projection : Name)
  /-- Codec-encoded primitive: the Lean-level type is `codecType`,
      encoded via `encodeFn : codecType → UIntN` and decoded via
      `decodeFn : UIntN → codecType`. `reverseId` is a proof of
      `∀ u, encodeFn (decodeFn u) = u` (used by the byte-roundtrip
      theorem: `write ∘ decode = extract`). `forwardId` is a proof
      of `∀ x, decodeFn (encodeFn x) = x` (used by the forward
      roundtrip: `decode ∘ write = id`). -/
  | codec     (width : Nat) (codecType : Name)
              (encodeFn : Name) (decodeFn : Name)
              (reverseId : Name) (forwardId : Name)
  /-- Raw-bytes slice of fixed length `N`. `sizeField` is the optional
      dependent size-proof field name (e.g. `head_size` asserting
      `head.size = N`). -/
  | rawBytes  (byteSize : Nat) (sizeField : Option Name)
  /-- Embedded sub-struct. `subType`/`writeFn`/`decodeFn`/`roundtripLemma`
      are all names; `byteSize` is the sub-struct's encoded size.
      `needsPrec` says the sub-struct's decoder takes a
      `(h : off + N ≤ bs.size)` precondition (i.e. was generated with
      `skip_bytewidth` because of raw_bytes-with-size-field or a
      nested embed_prec field). When `needsPrec = true`, the outer
      schema must also be `skip_bytewidth`.

      For prec embeds (`needsPrec = true`), the additional
      `forwardLemma` and `appendLeftLemma` names enable the outer
      schema's forward roundtrip emission. They're `none` for
      non-prec embeds (whose forward direction isn't needed by any
      consumer). -/
  | embed     (byteSize : Nat) (subType : Name)
              (writeFn : Name) (decodeFn : Name) (roundtripLemma : Name)
              (needsPrec : Bool := false)
              (forwardLemma : Option Name := none)
              (appendLeftLemma : Option Name := none)
  deriving Inhabited

/-- The on-disk byte-size a field occupies. -/
private def FieldKind.byteSize : FieldKind → Nat
  | .primitive w          => w
  | .wrapped w _ _        => w
  | .wrappedNat w _ _     => w
  | .codec w _ _ _ _ _    => w
  | .rawBytes n _         => n
  | .embed n _ _ _ _ _ _ _ => n

private structure FieldSpec where
  name   : Name
  offset : Nat
  kind   : FieldKind
  deriving Inhabited

private def FieldSpec.byteSize (f : FieldSpec) : Nat := f.kind.byteSize

private def parseWidthTok? :
    TSyntax `elfSchemaWidth → CommandElabM Nat
  | `(elfSchemaWidth| u8)  => pure 1
  | `(elfSchemaWidth| u16) => pure 2
  | `(elfSchemaWidth| u32) => pure 4
  | `(elfSchemaWidth| u64) => pure 8
  | w => throwErrorAt w "elf_schema: unknown width"

private def parseFieldStx (stx : TSyntax `elfSchemaField) :
    CommandElabM FieldSpec := do
  -- Each field kind has its own quotation pattern; the order of
  -- branches doesn't matter because the patterns are mutually
  -- exclusive on `stx.getKind`.  Quotation-pattern matching is
  -- robust to new tokens (positional indexing was not).
  match stx with
  | `(elfSchemaField| $fname:ident : $w:elfSchemaWidth @ $off:num) =>
    let width ← parseWidthTok? w
    return { name := fname.getId, offset := off.getNat,
             kind := .primitive width }
  | `(elfSchemaField|
        $fname:ident : $w:elfSchemaWidth @ $off:num wrap $wt:ident $proj:ident) =>
    let width ← parseWidthTok? w
    return { name := fname.getId, offset := off.getNat,
             kind := .wrapped width wt.getId proj.getId }
  | `(elfSchemaField|
        $fname:ident : $w:elfSchemaWidth @ $off:num wrap_nat $wt:ident $proj:ident) =>
    let width ← parseWidthTok? w
    return { name := fname.getId, offset := off.getNat,
             kind := .wrappedNat width wt.getId proj.getId }
  | `(elfSchemaField|
        $fname:ident : $ct:ident via $w:elfSchemaWidth @ $off:num
          codec $enc:ident $dec:ident $rid:ident $fid:ident) =>
    let width ← parseWidthTok? w
    return { name := fname.getId, offset := off.getNat,
             kind := .codec width ct.getId enc.getId dec.getId rid.getId fid.getId }
  | `(elfSchemaField| $fname:ident : raw_bytes $n:num @ $off:num) =>
    return { name := fname.getId, offset := off.getNat,
             kind := .rawBytes n.getNat none }
  | `(elfSchemaField|
        $fname:ident : raw_bytes $n:num @ $off:num with_size_field $sf:ident) =>
    return { name := fname.getId, offset := off.getNat,
             kind := .rawBytes n.getNat (some sf.getId) }
  | `(elfSchemaField|
        $fname:ident : embed $sub:ident bytes $n:num
          write_as $wf:ident decode_as $df:ident roundtrip_as $rl:ident
          @ $off:num) =>
    return { name := fname.getId, offset := off.getNat,
             kind := .embed n.getNat sub.getId wf.getId df.getId rl.getId false none none }
  | `(elfSchemaField|
        $fname:ident : embed $sub:ident bytes $n:num with_prec
          write_as $wf:ident decode_as $df:ident roundtrip_as $rl:ident
          forward_as $fl:ident append_left_as $apl:ident
          @ $off:num) =>
    return { name := fname.getId, offset := off.getNat,
             kind := .embed n.getNat sub.getId wf.getId df.getId rl.getId true
                       (some fl.getId) (some apl.getId) }
  | _ => throwErrorAt stx "elf_schema: malformed field entry"

/-! ## Code generation via Lean 4 quotations

    This DSL emits commands via `TSyntax `command` built with
    quotations (`` `(...) ``).  Key patterns used throughout:

      * `Array (TSyntax c)` with `$xs:c,*` splice — for separator-
        separated sequences (struct instance fields, simp hints).

      * `foldlM` over an Array to build chains like `a ++ b ++ c`
        via `xs.foldlM (fun acc e => `($acc ++ $e)) init`.

      * `mkIdent (name ++ `subName)` for external identifiers —
        fully-qualified name construction avoids hygiene-taint `✝`
        suffixes that appear when bare names are written in a
        quotation.

    Implementation note: emission is fully quotation-based.
    The roundtrip-proof tactic generator builds an
    `Array (TSyntax `tactic)` and splices it as `by $tacs:tactic*`
    via `roundtripProofTactics`.  String concatenation is not used
    on the hot path.

    There are NO calls to `Parser.runParserCategory` — every
    command goes through `TSyntax `command` + `elabCommand`. -/

/-! ## Name-construction helpers -/

/-- Root-qualified `Patchelf.Elf`.  The `_root_` prefix lets the
    emitted declarations use fully-qualified names regardless of
    whether the caller has already entered `namespace Patchelf.Elf`. -/
private def rootElfNs : Name := `_root_ ++ `Patchelf ++ `Elf

/-- `_root_.Patchelf.Elf.Decode`. -/
private def rootDecodeNs : Name := rootElfNs ++ `Decode

/-- `_root_.Patchelf.Elf.ByteWidth`. -/
private def rootByteWidthNs : Name := rootElfNs ++ `ByteWidth

/-- `Writer.writeU{N}` / `Reader.readU{N}` for byte-width `w`.  The
    width is given in BYTES (1/2/4/8); the generated name uses the
    corresponding bit-width (8/16/32/64). -/
private def writeUIdent (w : Nat) : Ident :=
  mkIdent (`Patchelf ++ `Elf ++ `Writer ++ .mkSimple s!"writeU{8 * w}")

private def readUIdent (w : Nat) : Ident :=
  mkIdent (`Patchelf ++ `Elf ++ `Reader ++ .mkSimple s!"readU{8 * w}")

/-- `Patchelf.Elf.writeU{N}_readU{N}_extract` lemma name for width `w`. -/
private def writeReadExtractIdent (w : Nat) : Ident :=
  mkIdent (`Patchelf ++ `Elf
    ++ .mkSimple s!"writeU{8 * w}_readU{8 * w}_extract")

/-- Build a `TSyntax `term` for writing a single field.  Used by
    `writeBodyQuoted` to assemble the full write chain.  Shape per
    field kind (with `prefix = x.`):
    * primitive:   `writeUN x.name`
    * wrapped:     `writeUN x.name.proj`
    * codec:       `writeUN (encodeFn x.name)`
    * raw_bytes:   `x.name` (the field is already a ByteArray)
    * embed:       `SubType.write x.name`

    `bareNames := true` switches to using bare local names (e.g.
    `writeUN name` instead of `writeUN x.name`) — used by the
    forward-roundtrip proof for prec schemas, where after a
    `cases x with | mk name ... =>` the field names are local
    bindings rather than projections of `x`. -/
private def writeFieldTerm (f : FieldSpec) (bareNames : Bool := false) :
    CommandElabM (TSyntax `term) := do
  let fieldAccess ←
    if bareNames then `($(mkIdent f.name):ident) else `(x.$(mkIdent f.name):ident)
  match f.kind with
  | .primitive w =>
    `($(writeUIdent w) $fieldAccess)
  | .wrapped w _ proj =>
    let projected ← `($fieldAccess.$(mkIdent proj):ident)
    `($(writeUIdent w) $projected)
  | .wrappedNat w _ proj =>
    -- `x.f.proj : Nat`; convert to UIntN at the wire boundary.
    let projected ← `($fieldAccess.$(mkIdent proj):ident)
    let toUIntId : Ident :=
      mkIdent (`Nat ++ .mkSimple s!"toUInt{8 * w}")
    `($(writeUIdent w) ($toUIntId $projected))
  | .codec w _ enc _ _ _ =>
    let encId : Ident := mkIdent enc
    `($(writeUIdent w) ($encId $fieldAccess))
  | .rawBytes _ _ => pure fieldAccess
  | .embed _ _ wf _ _ _ _ _ =>
    let wfId : Ident := mkIdent wf
    `($wfId $fieldAccess)

/-- Build the full write function body: chain of `++` applications. -/
private def writeBodyQuoted (fields : Array FieldSpec) :
    CommandElabM (TSyntax `term) := do
  let parts ← fields.mapM writeFieldTerm
  match parts.toList with
  | []      => `((ByteArray.empty))
  | x :: xs => xs.foldlM (fun acc e => `($acc ++ $e)) x

/-- Build field assignments for the decoder's struct literal.

    Each field emits one structInstField, except raw_bytes with
    size_field which emits TWO (the bytes + the size-proof). -/
private def decodeFieldAssigns (fields : Array FieldSpec) :
    CommandElabM (Array (TSyntax ``Lean.Parser.Term.structInstField)) := do
  let rdPfx : Name := `Patchelf ++ `Elf ++ `Reader
  let readBytesId     : Ident := mkIdent (rdPfx ++ `readBytes)
  let readBytesSizeId : Ident := mkIdent (rdPfx ++ `readBytes_size)
  let mut assigns : Array (TSyntax ``Lean.Parser.Term.structInstField) := #[]
  for f in fields do
    let fieldId : Ident := mkIdent f.name
    let offsetLit : TSyntax `num := Syntax.mkNumLit (toString f.offset)
    match f.kind with
    | .primitive w =>
      assigns := assigns.push (← `(Lean.Parser.Term.structInstField|
        $fieldId:ident := $(readUIdent w) bs (off + $offsetLit)))
    | .wrapped w _ _ =>
      assigns := assigns.push (← `(Lean.Parser.Term.structInstField|
        $fieldId:ident := ⟨$(readUIdent w) bs (off + $offsetLit)⟩))
    | .wrappedNat w _ _ =>
      -- Convert UIntN → Nat at the wire boundary.
      assigns := assigns.push (← `(Lean.Parser.Term.structInstField|
        $fieldId:ident := ⟨($(readUIdent w) bs (off + $offsetLit)).toNat⟩))
    | .codec w _ _ dec _ _ =>
      let decId : Ident := mkIdent dec
      assigns := assigns.push (← `(Lean.Parser.Term.structInstField|
        $fieldId:ident := $decId ($(readUIdent w) bs (off + $offsetLit))))
    | .rawBytes n sizeField =>
      let nLit : TSyntax `num := Syntax.mkNumLit (toString n)
      assigns := assigns.push (← `(Lean.Parser.Term.structInstField|
        $fieldId:ident := $readBytesId bs (off + $offsetLit) $nLit))
      if let some sf := sizeField then
        let sfId : Ident := mkIdent sf
        assigns := assigns.push (← `(Lean.Parser.Term.structInstField|
          $sfId:ident := $readBytesSizeId bs (off + $offsetLit) $nLit (by omega)))
    | .embed _ _ _ df _ needsPrec _ _ =>
      let dfId : Ident := mkIdent df
      if needsPrec then
        assigns := assigns.push (← `(Lean.Parser.Term.structInstField|
          $fieldId:ident := $dfId bs (off + $offsetLit) (by omega)))
      else
        assigns := assigns.push (← `(Lean.Parser.Term.structInstField|
          $fieldId:ident := $dfId bs (off + $offsetLit)))
  pure assigns

/-! ## Roundtrip-proof term construction

    Helpers for building the post-rewrite term that the `show` tactic
    targets (the canonical chain of per-field primitives).  Kept as
    a separate helper so tests can verify just the term-building
    without running the whole proof. -/

/-- Build the per-field "post-rewrite" term — what we want each
    field's write∘decode to reduce to.  This is the target of the
    `show` tactic and also the form to which the per-field rewrites
    (writeUN_readUN_extract, Reader.readBytes, embed roundtrip) drive
    the LHS. -/
private def postRewriteFieldTerm (f : FieldSpec) :
    CommandElabM (TSyntax `term) := do
  let offsetLit : TSyntax `num := Syntax.mkNumLit (toString f.offset)
  match f.kind with
  | .primitive w | .wrapped w _ _ | .wrappedNat w _ _ | .codec w _ _ _ _ _ =>
    `($(writeUIdent w) ($(readUIdent w) bs (off + $offsetLit)))
  | .rawBytes n _ =>
    let nLit : TSyntax `num := Syntax.mkNumLit (toString n)
    `(bs.extract (off + $offsetLit) (off + $offsetLit + $nLit))
  | .embed _ sub _ df _ needsPrec _ _ =>
    let subWriteId : Ident := mkIdent (sub ++ `write)
    let dfId       : Ident := mkIdent df
    if needsPrec then
      `($subWriteId ($dfId bs (off + $offsetLit) (by omega)))
    else
      `($subWriteId ($dfId bs (off + $offsetLit)))

/-- Build the byte-roundtrip proof as an Array of tactic syntaxes.
    Replaces the string-based `roundtripProof` with quotation-based
    emission.  Each tactic is a `TSyntax `tactic` built via
    `` `(tactic| ...) ``; external identifiers come from `mkIdent`. -/
private def roundtripProofTactics (writeId decodeId : Ident) (total : Nat)
    (fields : Array FieldSpec) :
    CommandElabM (Array (TSyntax `tactic)) := do
  let n := fields.size
  let rdPfx : Name := `Patchelf ++ `Elf ++ `Reader
  let readBytesId : Ident := mkIdent (rdPfx ++ `readBytes)
  let extractAppExId : Ident := mkIdent (`ByteArray ++ `extract_append_extract)
  let mut tacs : Array (TSyntax `tactic) := #[]
  -- 1. Unfold write and decode.
  tacs := tacs.push (← `(tactic| unfold $writeId $decodeId))
  -- 2a. Pre-rewrite wrap_nat fields: `Nat.toUIntN (UIntN.toNat u) = u`.
  -- After `unfold write decode`, the byte-roundtrip target contains
  -- `writeUN ((readUN bs k).toNat.toUInt{N})`.  Collapsing
  -- `(.toNat).toUInt{N} = id` reduces it to `writeUN (readUN bs k)`,
  -- discharged by the standard primitive roundtrip lemma.  Uses
  -- `simp only [UIntN.ofNat_toNat]` (rather than `rw`) so the rewriter
  -- sees through the reducible `Nat.toUInt{N} = UInt{N}.ofNat`.
  -- Collected per-width to issue one simp call (multiple identical
  -- rewrites would trip "made no progress").
  let mut wrapNatWidths : List Nat := []
  for f in fields do
    match f.kind with
    | .wrappedNat w _ _ =>
      if !wrapNatWidths.contains w then
        wrapNatWidths := w :: wrapNatWidths
    | _ => pure ()
  if !wrapNatWidths.isEmpty then
    let mut hints : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
    for w in wrapNatWidths do
      let ofNatId : Ident :=
        mkIdent ((.mkSimple s!"UInt{8 * w}") ++ `ofNat_toNat)
      hints := hints.push (← `(Lean.Parser.Tactic.simpLemma| $ofNatId:ident))
    tacs := tacs.push (← `(tactic| simp only [$hints,*]))
  -- 2b. Pre-rewrite codec identity lemmas.
  for f in fields do
    match f.kind with
    | .codec _ _ _ _ reverseId _ =>
      let lemId : Ident := mkIdent reverseId
      tacs := tacs.push (← `(tactic| rw [$lemId:term]))
    | _ => pure ()
  -- If any raw_bytes, unfold Reader.readBytes to its extract form.
  if fields.any (match ·.kind with | .rawBytes _ _ => true | _ => false) then
    let hint ← `(Lean.Parser.Tactic.simpLemma| $readBytesId:ident)
    tacs := tacs.push (← `(tactic| simp only [$hint]))
  -- 3. Show target: chain of post-rewrite terms ≡ bs.extract off (off+total).
  let postParts ← fields.mapM postRewriteFieldTerm
  let postChain : TSyntax `term ←
    match postParts.toList with
    | [] => `(ByteArray.empty)
    | x :: xs => xs.foldlM (fun acc e => `($acc ++ $e)) x
  let totalLit : TSyntax `num := Syntax.mkNumLit (toString total)
  tacs := tacs.push (← `(tactic|
    show $postChain = bs.extract off (off + $totalLit)))
  -- 4. Per-field fit hypotheses (only for non-rawBytes fields).
  for i in [0:n] do
    let f := fields[i]!
    match f.kind with
    | .rawBytes _ _ => pure ()
    | _ =>
      let hName := mkIdent (.mkSimple s!"hFit{i}")
      let offLit  : TSyntax `num := Syntax.mkNumLit (toString f.offset)
      let bszLit  : TSyntax `num := Syntax.mkNumLit (toString f.byteSize)
      tacs := tacs.push (← `(tactic|
        have $hName:ident : off + $offLit + $bszLit ≤ bs.size := by omega))
  -- 5. Per-field roundtrip rewrites.
  for i in [0:n] do
    let f := fields[i]!
    let hName := mkIdent (.mkSimple s!"hFit{i}")
    let offLit : TSyntax `num := Syntax.mkNumLit (toString f.offset)
    match f.kind with
    | .primitive w | .wrapped w _ _ | .wrappedNat w _ _ | .codec w _ _ _ _ _ =>
      tacs := tacs.push (← `(tactic|
        rw [$(writeReadExtractIdent w):term bs (off + $offLit) $hName:term]))
    | .rawBytes _ _ => pure ()
    | .embed _ _ _ _ rl _ _ _ =>
      let rlId : Ident := mkIdent rl
      tacs := tacs.push (← `(tactic|
        rw [$rlId:term bs (off + $offLit) $hName:term]))
  -- 6. Arithmetic normalization.
  if n > 0 && fields[0]!.offset = 0 then
    tacs := tacs.push (← `(tactic| rw [show off + 0 = off from by omega]))
  for i in [0:n] do
    let f := fields[i]!
    let endOff := f.offset + f.byteSize
    let offLit : TSyntax `num := Syntax.mkNumLit (toString f.offset)
    let bszLit : TSyntax `num := Syntax.mkNumLit (toString f.byteSize)
    let endLit : TSyntax `num := Syntax.mkNumLit (toString endOff)
    tacs := tacs.push (← `(tactic|
      rw [show off + $offLit + $bszLit = off + $endLit from by omega]))
  -- 7. Merge adjacent extracts pairwise left-to-right.
  for i in [1:n] do
    let prevEnd := fields[i-1]!.offset + fields[i-1]!.byteSize
    let curEnd  := fields[i]!.offset + fields[i]!.byteSize
    let prevLit : TSyntax `num := Syntax.mkNumLit (toString prevEnd)
    let curLit  : TSyntax `num := Syntax.mkNumLit (toString curEnd)
    tacs := tacs.push (← `(tactic|
      rw [$extractAppExId:term (a := bs) (i := off) (j := off + $prevLit) (k := off + $curLit)]))
    tacs := tacs.push (← `(tactic|
      rw [show min off (off + $prevLit) = off from by omega]))
    tacs := tacs.push (← `(tactic|
      rw [show max (off + $prevLit) (off + $curLit) = off + $curLit from by omega]))
  pure tacs

/-! ## Forward roundtrip proof construction (`decode ∘ write = id`)

    The DSL emits a per-struct theorem `decodeFoo (Foo.write x) 0 = x`
    whose proof template is uniform across the non-prec schemas
    (no `raw_bytes … with_size_field` and no `embed … with_prec`).

    Per-field tactic shape: peel `(n - 1 - i)` left appends
    (`readU{w}_append_left`) at offset `f.offset`, then if `i > 0`
    align the offset to the prefix end via
    `show $offLit = $prefixChain.size + 0`, peel one right append
    (`readU{w}_append_right _ _ 0`), and close the primitive read
    via `readU{w}_writeU{w}`.

    Wrapped fields close by structure η (1-field wrapper).  Codec
    fields require a final `rw [$forwardId]` to reduce
    `decodeFn (encodeFn x.f) = x.f`. -/

/-- Build explicit binders `(hFit_<fname> : x.<fname>.val < UInt{w}.size)`
    for every `wrap_nat` field, threaded into the forward-roundtrip
    theorem signature.  Returns the binder syntax array (empty when no
    `wrap_nat` fields are present).  `bareNames := true` produces bare
    `<fname>.val` instead of `x.<fname>.val` (used inside the prec
    proof shape after `cases x with | mk ...`). -/
private def wrapNatFitBinders (fields : Array FieldSpec)
    (bareNames : Bool := false) :
    CommandElabM (Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) := do
  let mut binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  for f in fields do
    match f.kind with
    | .wrappedNat w _ proj =>
      let fitHypId : Ident := mkIdent (.mkSimple s!"hFit_{f.name.toString}")
      let sizeId : Ident :=
        mkIdent ((.mkSimple s!"UInt{8 * w}") ++ `size)
      let valAccess ←
        if bareNames then
          `($(mkIdent f.name):ident.$(mkIdent proj):ident)
        else
          `(x.$(mkIdent f.name):ident.$(mkIdent proj):ident)
      let binder ← `(Lean.Parser.Term.bracketedBinderF|
          ($fitHypId : $valAccess < $sizeId))
      binders := binders.push binder
    | _ => pure ()
  pure binders

/-- Build the writer-prefix chain for fields `0..upTo`: a `++`-chain
    of per-field write expressions used in the `show $offLit =
    $prefix.size + 0` step.  `bareNames` propagates to
    `writeFieldTerm`. -/
private def writePrefixChain (fields : Array FieldSpec) (upTo : Nat)
    (bareNames : Bool := false) :
    CommandElabM (TSyntax `term) := do
  let parts ← (fields.extract 0 upTo).mapM (writeFieldTerm · bareNames)
  match parts.toList with
  | []      => `((ByteArray.empty))
  | x :: xs => xs.foldlM (fun acc e => `($acc ++ $e)) x

/-- Build per-field rewrites for one field at index `i` of `n`,
    closing the primitive read down to `<x.field>` (or to
    `decodeFn (encodeFn <x.field>)` for codec fields).

    `sizeHints` is a simp-lemma set used in the `(by simp …)` size
    proofs.  Empty for non-prec schemas; for prec schemas (with an
    embed prefix) it includes the embed sub-struct's `write_size`
    lemma so simp can normalize `(SubType.write …).size`.

    `bareNames := true` produces bare local names (post-`cases`
    destructuring) instead of `x.<field>` projections; required for
    the prec proof shape's prefix-chain step. -/
private def forwardFieldTactics (fields : Array FieldSpec) (i : Nat)
    (sizeHints : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[])
    (bareNames : Bool := false) :
    CommandElabM (Array (TSyntax `tactic)) := do
  let n := fields.size
  let f := fields[i]!
  let offLit : TSyntax `num := Syntax.mkNumLit (toString f.offset)
  let mut tacs : Array (TSyntax `tactic) := #[]
  -- Width and the matching read/write/roundtrip names.
  let w : Nat ←
    match f.kind with
    | .primitive w | .wrapped w _ _ | .wrappedNat w _ _ | .codec w _ _ _ _ _ => pure w
    | _ => throwError "forwardFieldTactics: unsupported field kind"
  let readApLeftId  : Ident := mkIdent (`Patchelf ++ `Elf ++ .mkSimple s!"readU{8 * w}_append_left")
  let readApRightId : Ident := mkIdent (`Patchelf ++ `Elf ++ .mkSimple s!"readU{8 * w}_append_right")
  let readWriteId   : Ident := mkIdent (`Patchelf ++ `Elf ++ .mkSimple s!"readU{8 * w}_writeU{8 * w}")
  -- (n - 1 - i) left peels at offset f.offset.
  let leftPeels := n - 1 - i
  for _ in [0:leftPeels] do
    tacs := tacs.push (← `(tactic|
      rw [$readApLeftId:term _ _ $offLit (by simp [$sizeHints,*])]))
  -- For i > 0: align offset to prefix.size + 0 and peel one right append.
  if i > 0 then
    let pfx ← writePrefixChain fields i bareNames
    tacs := tacs.push (← `(tactic|
      rw [show ($offLit : Nat) = ($pfx).size + 0 from by simp [$sizeHints,*]]))
    tacs := tacs.push (← `(tactic|
      rw [$readApRightId:term _ _ 0 (by simp [$sizeHints,*])]))
  -- Close the primitive read.
  tacs := tacs.push (← `(tactic| rw [$readWriteId:term]))
  -- For codec fields, apply the forward identity to reduce
  -- `decodeFn (encodeFn x.f)` to `x.f`.
  match f.kind with
  | .codec _ _ _ _ _ forwardId =>
    let fid : Ident := mkIdent forwardId
    tacs := tacs.push (← `(tactic| rw [$fid:term]))
  | .wrappedNat w _ _ =>
    -- After the primitive readU{w}_writeU{w}, the goal has
    -- `⟨(x.f.val.toUInt{w}).toNat⟩`.  Apply the fit hypothesis
    -- `hFit_<fname> : x.f.val < UInt{w}.size` via
    -- `UInt{w}.toNat_ofNat_of_lt'` to reduce to `⟨x.f.val⟩`, which is
    -- structurally equal to `x.f` (1-field wrapper).
    let fitHypName : Name := .mkSimple s!"hFit_{f.name.toString}"
    let fitHypId : Ident := mkIdent fitHypName
    let toNatOfNatId : Ident :=
      mkIdent ((.mkSimple s!"UInt{8 * w}") ++ `toNat_ofNat_of_lt')
    tacs := tacs.push (← `(tactic| rw [$toNatOfNatId:term $fitHypId]))
  | _ => pure ()
  pure tacs

/-- Build the forward roundtrip proof tactic list for non-prec
    schemas.  Assumes every field is `.primitive`, `.wrapped`, or
    `.codec` — `.rawBytes` and `.embed-with-prec` are handled by
    `forwardProofTacticsPrec`. -/
private def forwardProofTactics (writeId decodeId : Ident)
    (fields : Array FieldSpec) :
    CommandElabM (Array (TSyntax `tactic)) := do
  let n := fields.size
  let mut tacs : Array (TSyntax `tactic) := #[]
  tacs := tacs.push (← `(tactic| unfold $decodeId $writeId))
  tacs := tacs.push (← `(tactic| simp only [Nat.zero_add]))
  for i in [0:n] do
    let fieldTacs ← forwardFieldTactics fields i
    tacs := tacs ++ fieldTacs
  pure tacs

/-- Build the forward roundtrip proof tactic list for prec schemas
    whose first field is `embed … with_prec` and remaining fields
    are primitive/wrapped/codec.  Currently the only consumer is
    `ElfHeader` (1 ElfIdent embed at offset 0 + 13 primitive/wrapped
    fields).

    Proof shape:
      cases x with | mk f0 f1 ... fn-1 =>
      have hSz : (subType.write f0).size = embedSize := subType.write_size f0
      unfold $decodeId $writeId
      simp only [Nat.zero_add, $TypeName.mk.injEq]
      refine ⟨?_, ?_, ..., ?_⟩
      <per-leg tactics>

    The embed leg uses `iterate (n-1) rw [<appendLeftLemma> ...]`
    to peel through the suffix-append chain, then closes with
    `exact <forwardLemma> f0 _`.

    Each non-embed leg uses `forwardFieldTactics` with size hints
    `[ByteArray.size_append, hSz]` and `bareNames := true`. -/
private def forwardProofTacticsPrec (typeName : Name) (writeId decodeId : Ident)
    (fields : Array FieldSpec) :
    CommandElabM (Array (TSyntax `tactic)) := do
  let n := fields.size
  -- Validate: field 0 must be embed-with-prec; all other fields
  -- must be primitive/wrapped/codec.
  let f0 := fields[0]!
  let (subType, embedSize, forwardLemma, appendLeftLemma) ←
    match f0.kind with
    | .embed sz subType _ _ _ true (some forwardLemma) (some appendLeftLemma) =>
      pure (subType, sz, forwardLemma, appendLeftLemma)
    | _ => throwError "forwardProofTacticsPrec: schema's first field must be `embed … with_prec` with `forward_as` and `append_left_as`"
  for i in [1:n] do
    match fields[i]!.kind with
    | .primitive _ | .wrapped _ _ _ | .wrappedNat _ _ _
    | .codec _ _ _ _ _ _ => pure ()
    | _ => throwError s!"forwardProofTacticsPrec: field {fields[i]!.name} must be primitive/wrapped/codec (only the first field can be embed)"
  -- Build the cases pattern: ` mk f0 f1 ... fn-1 ` (one binder per
  -- non-Prop field).  We rely on field-name matching — the user's
  -- `structure` declaration must list fields in the same order as
  -- the schema.
  let fieldIdents : Array Ident := fields.map fun f => mkIdent f.name
  -- Build `refine ⟨?_, ?_, ..., ?_⟩` with `n` underscores.
  let underscores : Array (TSyntax `term) ← Array.range n |>.mapM (fun _ => `(?_))
  let refineTuple : TSyntax `term ← `(⟨$underscores,*⟩)
  -- Identifiers
  let qSubWriteSize : Ident := mkIdent (subType ++ `write_size)
  let qSubWrite     : Ident := mkIdent (subType ++ `write)
  let qInjEq        : Ident := mkIdent (typeName ++ `mk ++ `injEq)
  let qFwd          : Ident := mkIdent forwardLemma
  let qApL          : Ident := mkIdent appendLeftLemma
  let f0Id          : Ident := fieldIdents[0]!
  let embedSizeLit  : TSyntax `num := Syntax.mkNumLit (toString embedSize)
  -- Size simp hints used by the per-leg primitive proofs.
  let hSzId : Ident := mkIdent `hSz
  let mut sizeHints : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
  sizeHints := sizeHints.push (← `(Lean.Parser.Tactic.simpLemma| ByteArray.size_append))
  sizeHints := sizeHints.push (← `(Lean.Parser.Tactic.simpLemma| $hSzId:ident))
  let mut tacs : Array (TSyntax `tactic) := #[]
  -- 1. Cases-destructure x.
  tacs := tacs.push (← `(tactic|
    cases x with | mk $fieldIdents* => ?_))
  -- 2. Establish hSz.
  tacs := tacs.push (← `(tactic|
    have $hSzId:ident : ($qSubWrite $f0Id).size = $embedSizeLit := $qSubWriteSize $f0Id))
  -- 3. Unfold + simp + refine.
  tacs := tacs.push (← `(tactic| unfold $decodeId $writeId))
  tacs := tacs.push (← `(tactic|
    simp only [Nat.zero_add, $qInjEq:ident]))
  tacs := tacs.push (← `(tactic| refine $refineTuple))
  -- 4. Per-leg tactics, wrapped in `· …` blocks.
  let embedLeftPeels := n - 1
  let mut legs : Array (TSyntax `tactic) := #[]
  -- Embed leg (field 0).
  do
    let mut embedTacs : Array (TSyntax `tactic) := #[]
    for _ in [0:embedLeftPeels] do
      embedTacs := embedTacs.push (← `(tactic|
        rw [$qApL:term _ _ (by simp [$sizeHints,*])
              (by simp [$sizeHints,*])
              (by simp [$sizeHints,*])]))
    embedTacs := embedTacs.push (← `(tactic|
      exact $qFwd $f0Id _))
    legs := legs.push (← `(tactic| · $embedTacs:tactic*))
  -- Non-embed legs (fields 1..n-1).
  for i in [1:n] do
    let fieldTacs ← forwardFieldTactics fields i sizeHints (bareNames := true)
    legs := legs.push (← `(tactic| · $fieldTacs:tactic*))
  tacs := tacs ++ legs
  pure tacs

/-! ## Top-level elaborator -/

/-- Parsed option bundle. -/
private structure SchemaOpts where
  decodeOver     : Option Name := none
  rtOver         : Option Name := none
  bwOver         : Option Name := none
  skipWrite      : Bool        := false
  skipDecode     : Bool        := false
  skipByteWidth  : Bool        := false
  /-- Name of the fixed-count-array decoder to emit (e.g. `decodePhdrs`);
      `none` skips emission. Emits `<name>`, `<name>_size`,
      `<name>_getElem` as a `buildArray`-based bundle. -/
  arrayDecoder   : Option Name := none

/-- Extract optional `decode_as` / `roundtrip_as` / `bytewidth_as` /
    `skip_write` / `skip_decode` / `skip_bytewidth` /
    `with_array_decoder` clauses. -/
private def parseOpts
    (optsStx : TSyntaxArray `Patchelf.Elf.SchemaDSL.elfSchemaOpt)
    : CommandElabM SchemaOpts := do
  let mut opts : SchemaOpts := {}
  for o in optsStx do
    match o with
    | `(elfSchemaOpt| decode_as $n:ident) =>
      opts := { opts with decodeOver := some n.getId }
    | `(elfSchemaOpt| roundtrip_as $n:ident) =>
      opts := { opts with rtOver := some n.getId }
    | `(elfSchemaOpt| bytewidth_as $n:ident) =>
      opts := { opts with bwOver := some n.getId }
    | `(elfSchemaOpt| skip_write) =>
      opts := { opts with skipWrite := true }
    | `(elfSchemaOpt| skip_decode) =>
      opts := { opts with skipDecode := true }
    | `(elfSchemaOpt| skip_bytewidth) =>
      opts := { opts with skipByteWidth := true }
    | `(elfSchemaOpt| with_array_decoder $n:ident) =>
      opts := { opts with arrayDecoder := some n.getId }
    | _ => throwErrorAt o "elf_schema: unknown option clause"
  return opts

@[command_elab elfSchemaCmd]
def elabElfSchema : CommandElab := fun stx => do
  match stx with
  | `(elf_schema $typeName:ident := $totalStx:num $optsStx:elfSchemaOpt* $fieldsStx:elfSchemaField*) =>
    let total := totalStx.getNat
    let opts ← parseOpts optsStx
    let fields ← fieldsStx.mapM parseFieldStx
    -- Validation: at least one field; contiguous starting at 0;
    -- sum of widths equals the declared TOTAL; no duplicate field
    -- names (duplicates would pass structInstField validation but
    -- yield a downstream struct-literal error with worse
    -- localization).
    if fields.size = 0 then
      throwError "elf_schema: at least one field is required"
    let mut seen : NameSet := {}
    for f in fields do
      if seen.contains f.name then
        throwError s!"elf_schema: duplicate field name '{f.name}'"
      seen := seen.insert f.name
    let mut running := 0
    for f in fields do
      if f.offset ≠ running then
        throwError s!"elf_schema: field '{f.name}' has offset {f.offset}, expected {running} (contiguous fields only)"
      running := running + f.byteSize
    if running ≠ total then
      throwError s!"elf_schema: total size {total} does not match sum of field byte-sizes {running}"
    -- Canonical names for emitted artifacts, respecting overrides.
    -- The `baseName` is the struct's name; in practice `elf_schema`
    -- is always invoked with a single identifier so `baseName.toString`
    -- has no dots.  Default emitted names therefore embed the
    -- stringified base in a single atom (via `.mkSimple`); user-
    -- supplied overrides are taken as `Name` values verbatim.
    let baseName  : Name   := typeName.getId
    let baseStr   : String := baseName.toString
    let decodeName : Name :=
      opts.decodeOver.getD (.mkSimple s!"decode{baseStr}")
    let roundtripName : Name :=
      opts.rtOver.getD (.mkSimple s!"{baseStr}_write_decode{baseStr}_extract")
    let bwInstName : Name :=
      opts.bwOver.getD (.mkSimple s!"of_{baseStr}")
    -- Each emitted command wraps its body in `open Patchelf.Elf
    -- Patchelf.Elf.Reader Patchelf.Elf.Writer in …` so that bare
    -- names like `writeU16` / `readU32` / `ByteArray.extract` /
    -- `extract_append_extract` resolve without a leading namespace
    -- prefix.  All declaration names themselves are fully-qualified
    -- via `mkIdent` with the `_root_.Patchelf.Elf` prefix so a
    -- caller already inside `namespace Patchelf.Elf` doesn't
    -- double-prefix.
    let mut cmds : Array (TSyntax `command) := #[]
    -- (1) Write function + size lemma (unless `skip_write`).
    if !opts.skipWrite then
      let qBaseId    : Ident := mkIdent (rootElfNs ++ typeName.getId)
      let qWriteId   : Ident := mkIdent (rootElfNs ++ typeName.getId ++ `write)
      let body ← writeBodyQuoted fields
      let writeCmd ← `(command|
        open Patchelf.Elf Patchelf.Elf.Reader Patchelf.Elf.Writer in
        def $qWriteId (x : $qBaseId) : ByteArray :=
          $body)
      cmds := cmds.push writeCmd
      -- Build the simp set for the write_size proof.  The hints reduce
      -- the size chain (a chain of `++`s) to a numeric sum that `omega`
      -- would close — but we use `simp` here because the arithmetic
      -- is simple (just `Nat.add_assoc` / constants).
      --
      -- Hints included:
      --   * `ByteArray.size_append` — always; size of A ++ B.
      --   * `x.<sf>` — for each raw_bytes-with-size-field field `sf`,
      --     rewrites `x.name.size` to the declared byte count.
      --   * `<Sub>.write_size` — for each embedded sub-struct, rewrites
      --     `(Sub.write x.name).size` to the sub-struct's byte count.
      --
      -- The hints are built as `TSyntax `Lean.Parser.Tactic.simpLemma`
      -- values — simp's argument list requires that specific category,
      -- not plain `term`.
      let mut hintLemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
      -- ByteArray.size_append always first.
      hintLemmas := hintLemmas.push (← `(Lean.Parser.Tactic.simpLemma|
        ByteArray.size_append))
      for f in fields do
        match f.kind with
        | .rawBytes _ (some sf) =>
          let sfTerm ← `(Lean.Parser.Tactic.simpLemma| x.$(mkIdent sf):ident)
          hintLemmas := hintLemmas.push sfTerm
        | .embed _ sub _ _ _ _ _ _  =>
          let subId := mkIdent (sub ++ `write_size)
          let subTerm ← `(Lean.Parser.Tactic.simpLemma| $subId:ident)
          hintLemmas := hintLemmas.push subTerm
        | _ => pure ()
      let qBaseId      : Ident := mkIdent (rootElfNs ++ typeName.getId)
      let qWriteId     : Ident := mkIdent (rootElfNs ++ typeName.getId ++ `write)
      let qWriteSizeId : Ident := mkIdent (rootElfNs ++ typeName.getId ++ `write_size)
      let totalLit : TSyntax `num := Syntax.mkNumLit (toString total)
      let writeSizeCmd ← `(command|
        open Patchelf.Elf Patchelf.Elf.Reader Patchelf.Elf.Writer in
        @[simp] theorem $qWriteSizeId (x : $qBaseId) :
            ($qWriteId x).size = $totalLit := by
          unfold $qWriteId
          simp [$hintLemmas,*])
      cmds := cmds.push writeSizeCmd
    -- Does the decoder need an `off + total ≤ bs.size` precondition?
    -- Yes iff any of:
    --   * `raw_bytes … with_size_field …` field is present (the size-
    --     proof assignment calls `Reader.readBytes_size` which needs
    --     the in-bounds fact).
    --   * `embed … with_prec …` field is present (the embedded
    --     sub-struct's decoder itself takes a precondition that the
    --     outer decoder must thread through).
    let decodeNeedsPrec := fields.any fun f =>
      match f.kind with
      | .rawBytes _ (some _)           => true
      | .embed _ _ _ _ _ true _ _      => true
      | _                              => false
    if decodeNeedsPrec && !opts.skipByteWidth then
      throwError "elf_schema: this schema has a field that makes the decoder take an `off + total ≤ bs.size` precondition (either `raw_bytes ... with_size_field ...` or `embed ... with_prec ...`), which is incompatible with the ByteWidth instance's preconditionless read. Add `skip_bytewidth` to this schema."
    -- (2) Decoder (unless `skip_decode`).
    if !opts.skipDecode then
      let qBaseId   : Ident := mkIdent (rootElfNs ++ typeName.getId)
      let qDecodeId : Ident := mkIdent (rootDecodeNs ++ decodeName)
      let totalLit  : TSyntax `num := Syntax.mkNumLit (toString total)
      let fieldAssigns ← decodeFieldAssigns fields
      let decodeCmd ← if decodeNeedsPrec then
        `(command|
          open Patchelf.Elf Patchelf.Elf.Reader Patchelf.Elf.Writer in
          def $qDecodeId (bs : ByteArray) (off : Nat) (h : off + $totalLit ≤ bs.size) :
              $qBaseId :=
            { $fieldAssigns:structInstField,* })
      else
        `(command|
          open Patchelf.Elf Patchelf.Elf.Reader Patchelf.Elf.Writer in
          def $qDecodeId (bs : ByteArray) (off : Nat) : $qBaseId :=
            { $fieldAssigns:structInstField,* })
      cmds := cmds.push decodeCmd
    -- (3) Byte-roundtrip theorem.
    --
    -- The proof is built as an Array of TSyntax `tactic values via
    -- `roundtripProofTactics`; spliced into the theorem quotation
    -- with `$tactics:tactic*`.  Since signature + proof live in the
    -- same quotation, bound variables `bs`, `off`, `h` are in scope
    -- for the proof without hygiene workarounds.
    let qWriteId   : Ident := mkIdent (rootElfNs ++ typeName.getId ++ `write)
    let qDecodeId  : Ident := mkIdent (rootDecodeNs ++ decodeName)
    let qRoundId   : Ident := mkIdent (rootElfNs ++ roundtripName)
    let totalLit : TSyntax `num := Syntax.mkNumLit (toString total)
    let tacs ← roundtripProofTactics qWriteId qDecodeId total fields
    let rtCmd ← if decodeNeedsPrec then
      `(command|
        open Patchelf.Elf Patchelf.Elf.Reader Patchelf.Elf.Writer in
        theorem $qRoundId (bs : ByteArray) (off : Nat)
            (h : off + $totalLit ≤ bs.size) :
            $qWriteId ($qDecodeId bs off h) = bs.extract off (off + $totalLit) := by
          $tacs:tactic*)
    else
      `(command|
        open Patchelf.Elf Patchelf.Elf.Reader Patchelf.Elf.Writer in
        theorem $qRoundId (bs : ByteArray) (off : Nat)
            (h : off + $totalLit ≤ bs.size) :
            $qWriteId ($qDecodeId bs off) = bs.extract off (off + $totalLit) := by
          $tacs:tactic*)
    cmds := cmds.push rtCmd
    -- (3.5) Forward roundtrip theorem: `decode (write x) 0 = x`.
    -- Three branches:
    --   1. Non-prec schema (all fields primitive/wrapped/codec):
    --      simple chain-rewrite shape via `forwardProofTactics`.
    --   2. Prec schema with `embed … with_prec` at offset 0 and
    --      remaining fields primitive/wrapped/codec (e.g. ElfHeader):
    --      cases-and-refine shape via `forwardProofTacticsPrec`.
    --      Decoder takes a precondition `h`, so the theorem signature
    --      is `decode (write x) 0 (by simp) = x` — the size proof
    --      derives from `write_size`.
    --   3. Other prec schemas (e.g. raw_bytes-with-size-field as in
    --      ElfIdent): not auto-emitted; user hand-writes.
    let isPrecEmbedAt0 :=
      decodeNeedsPrec && fields.size > 0 &&
      (match fields[0]!.kind with
       | .embed _ _ _ _ _ true (some _) (some _) => true
       | _ => false) &&
      (Array.range fields.size).all fun i =>
        i = 0 || (match fields[i]!.kind with
                  | .primitive _ | .wrapped _ _ _ | .wrappedNat _ _ _
                  | .codec _ _ _ _ _ _ => true
                  | _ => false)
    if !decodeNeedsPrec then
      let qBaseId    : Ident := mkIdent (rootElfNs ++ typeName.getId)
      let qWriteId   : Ident := mkIdent (rootElfNs ++ typeName.getId ++ `write)
      let qDecodeId  : Ident := mkIdent (rootDecodeNs ++ decodeName)
      let qFwdId     : Ident := mkIdent (rootElfNs ++ baseName.appendAfter "_decode_write")
      let fwdTacs ← forwardProofTactics qWriteId qDecodeId fields
      let fitBinders ← wrapNatFitBinders fields
      let fwdCmd ← `(command|
        open Patchelf.Elf Patchelf.Elf.Reader Patchelf.Elf.Writer in
        theorem $qFwdId (x : $qBaseId) $fitBinders* :
            $qDecodeId ($qWriteId x) 0 = x := by
          $fwdTacs:tactic*)
      cmds := cmds.push fwdCmd
    else if isPrecEmbedAt0 then
      let qBaseId    : Ident := mkIdent (rootElfNs ++ typeName.getId)
      let qWriteId   : Ident := mkIdent (rootElfNs ++ typeName.getId ++ `write)
      let qDecodeId  : Ident := mkIdent (rootDecodeNs ++ decodeName)
      let qFwdId     : Ident := mkIdent (rootElfNs ++ baseName.appendAfter "_decode_write")
      let totalLit   : TSyntax `num := Syntax.mkNumLit (toString total)
      let fwdTacs ← forwardProofTacticsPrec baseName qWriteId qDecodeId fields
      -- Prec proof uses bare names after `cases x with | mk ... =>`,
      -- so wrap_nat fit hypotheses are also expressed in bare form.
      let fitBinders ← wrapNatFitBinders fields (bareNames := false)
      let fwdCmd ← `(command|
        set_option maxHeartbeats 8000000 in
        open Patchelf.Elf Patchelf.Elf.Reader Patchelf.Elf.Writer in
        theorem $qFwdId (x : $qBaseId) (h : 0 + $totalLit ≤ ($qWriteId x).size)
            $fitBinders* :
            $qDecodeId ($qWriteId x) 0 h = x := by
          $fwdTacs:tactic*)
      cmds := cmds.push fwdCmd
    -- (4) ByteWidth instance (unless `skip_bytewidth`).
    if !opts.skipByteWidth then
      let qBaseId    : Ident := mkIdent (rootElfNs ++ typeName.getId)
      let qWriteId   : Ident := mkIdent (rootElfNs ++ typeName.getId ++ `write)
      let qWriteSzId : Ident := mkIdent (rootElfNs ++ typeName.getId ++ `write_size)
      let qInstId    : Ident := mkIdent (rootByteWidthNs ++ bwInstName)
      let qDecodeId  : Ident := mkIdent (rootDecodeNs ++ decodeName)
      let qRoundId   : Ident := mkIdent (rootElfNs ++ roundtripName)
      let totalLit   : TSyntax `num := Syntax.mkNumLit (toString total)
      let bwCmd ← `(command|
        open Patchelf.Elf Patchelf.Elf.Reader Patchelf.Elf.Writer in
        def $qInstId : ByteWidth $qBaseId :=
          ⟨$totalLit, by decide, $qWriteId, $qDecodeId,
            fun x => $qWriteSzId x,
            fun bs off h => $qRoundId bs off h⟩)
      cmds := cmds.push bwCmd
    -- (5) Array-lift theorem `writeArray_Foo_write_extract`: thin
    -- wrapper around `writeArray_of_width` using the just-emitted
    -- ByteWidth instance. Only emitted when `ByteWidth.foo` is
    -- available (i.e. not `skip_bytewidth`).
    if !opts.skipByteWidth then
      -- Build identifiers from the canonical names.
      let qBaseId    : Ident := mkIdent (rootElfNs ++ typeName.getId)
      let qWriteId   : Ident := mkIdent (rootElfNs ++ typeName.getId ++ `write)
      let qInstId    : Ident := mkIdent (rootByteWidthNs ++ bwInstName)
      let qDecodeId  : Ident := mkIdent (rootDecodeNs ++ decodeName)
      let qLiftId    : Ident := mkIdent (rootElfNs ++
          (baseName.appendBefore "writeArray_").appendAfter "_write_extract")
      let totalLit   : TSyntax `num := Syntax.mkNumLit (toString total)
      let liftCmd ← `(command|
        open Patchelf.Elf Patchelf.Elf.Reader Patchelf.Elf.Writer in
        theorem $qLiftId (bs : ByteArray) (off : Nat)
            (arr : Array $qBaseId)
            (hFit : off + arr.size * $totalLit ≤ bs.size)
            (hEachDecoded : ∀ (i : Nat) (hi : i < arr.size),
              arr[i] = $qDecodeId bs (off + i * $totalLit)) :
            writeArray $qWriteId arr = bs.extract off (off + arr.size * $totalLit) :=
          writeArray_of_width $qInstId bs off arr hFit hEachDecoded)
      cmds := cmds.push liftCmd
    -- (6) Fixed-count array decoder bundle (opt-in via
    -- `with_array_decoder <Name>`). Emits `Decode.<Name>`,
    -- `Decode.<Name>_size`, `Decode.<Name>_getElem` as a thin
    -- `buildArray`-based wrapper over the per-entry decoder. Used by
    -- structs that the parser decodes in bulk (phdrs, shdrs, dynsym).
    if let some arrName := opts.arrayDecoder then
      let qBaseId    : Ident := mkIdent (rootElfNs ++ typeName.getId)
      let qDecodeId  : Ident := mkIdent (rootDecodeNs ++ decodeName)
      let qArrId     : Ident := mkIdent (rootDecodeNs ++ arrName)
      let qArrSizeId : Ident :=
        mkIdent (rootDecodeNs ++ arrName.appendAfter "_size")
      let qArrGetId  : Ident :=
        mkIdent (rootDecodeNs ++ arrName.appendAfter "_getElem")
      -- Fully qualify `Decode.buildArray{,_size,_getElem}` to avoid
      -- hygiene/resolution issues in the quotation.
      let buildArrId       : Ident := mkIdent (rootDecodeNs ++ `buildArray)
      let buildArrSizeId   : Ident := mkIdent (rootDecodeNs ++ `buildArray_size)
      let buildArrGetElId  : Ident := mkIdent (rootDecodeNs ++ `buildArray_getElem)
      let totalLit   : TSyntax `num := Syntax.mkNumLit (toString total)
      let arrCmd ← `(command|
        open Patchelf.Elf Patchelf.Elf.Reader Patchelf.Elf.Writer in
        def $qArrId (bs : ByteArray) (baseOff n : Nat) : Array $qBaseId :=
          $buildArrId n (fun i => $qDecodeId bs (baseOff + i * $totalLit)))
      cmds := cmds.push arrCmd
      let arrSizeCmd ← `(command|
        open Patchelf.Elf Patchelf.Elf.Reader Patchelf.Elf.Writer in
        @[simp] theorem $qArrSizeId (bs : ByteArray) (baseOff n : Nat) :
            ($qArrId bs baseOff n).size = n := by
          unfold $qArrId; exact $buildArrSizeId n _)
      cmds := cmds.push arrSizeCmd
      let arrGetElemCmd ← `(command|
        open Patchelf.Elf Patchelf.Elf.Reader Patchelf.Elf.Writer in
        theorem $qArrGetId (bs : ByteArray) (baseOff n : Nat) (i : Nat)
            (hi : i < ($qArrId bs baseOff n).size) :
            ($qArrId bs baseOff n)[i] = $qDecodeId bs (baseOff + i * $totalLit) := by
          unfold $qArrId
          exact $buildArrGetElId n _ i (by rw [$qArrId:ident] at hi; exact hi))
      cmds := cmds.push arrGetElemCmd
    cmds.forM elabCommand
  | _ => throwUnsupportedSyntax

end Patchelf.Elf.SchemaDSL
