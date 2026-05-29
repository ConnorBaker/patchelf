# Lean Patchelf Inventory

Root: `/Users/cbaker2/ext-sources/patchelf/lean/Patchelf`

This inventory lists every theorem/lemma, def, structure/inductive/class, abbrev, and instance in declaration order per file. **No `sorry` or `axiom` declarations exist anywhere in the codebase** (greps for both confirmed; only documentation comments mention "sorry"). All proofs are complete.

Notes on coverage:
- Files marked `(M)` below contain DSL-emitted boilerplate; the DSL itself in `SchemaDSL.lean` generates many `def`/`theorem` bodies that don't appear by name in source.
- The `instance` lines listed are mostly anonymous `Decidable` instances; they show their goal type.

---

## Patchelf/Main.lean

| Line | Kind | Name | Signature |
|---|---|---|---|
| 31 | def | `versionString` | `String` |
| 33 | def | `reportParse` | `(v : ParsedElf) -> IO Unit` |
| 42 | def | `usage` | `String` |
| 97 | def (private) | `reportSuite` | `(tag : String) (suite : List (String x Bool)) -> IO Unit` |
| 105 | def | `runSmoke` | `IO UInt32` |
| 110 | def | `runParseOnly` | `(path : String) -> IO UInt32` |
| 121 | def | `runOneOp` | `(opts : Options) (op : Op) (bs : ByteArray) -> IO (Except CliError ByteArray)` |
| 136 | def | `parseRenameMap` | `(text : String) -> List (String x String)` |
| 146 | def | `applyOneRename` | `(opts : Options) (bs : ByteArray) (oldName newName : String) -> IO (Except CliError ByteArray)` |
| 160 | def | `applyRenameMap` | `(opts : Options) (bs : ByteArray) (mapPath : System.FilePath) -> IO (Except CliError ByteArray)` |
| 177 | def (partial) | `runOps` | `(opts : Options) (bs : ByteArray) -> List Op -> IO ...` |
| 189 | def | `runPipeline` | `(inv : Invocation) -> IO UInt32` |
| 214 | def | `main` | `(args : List String) -> IO UInt32` |

## Patchelf/CLI.lean

| Line | Kind | Name | Signature |
|---|---|---|---|
| 62 | inductive | `RpathTagPolicy` | `\| default \| force` |
| 68 | inductive | `Op` | (CLI op variants — `addNeeded`, `removeNeeded`, `setRpath`, `setSoname`, etc.) |
| 111 | structure | `Options` | (CLI options bundle) |
| 123 | structure | `Invocation` | (parsed CLI invocation) |
| 130 | inductive | `CliError` | (CLI error variants) |
| 137 | def | `CliError.exitCode` | `CliError -> UInt32` |
| 143 | def | `CliError.message` | `CliError -> String` |
| 155 | def | `parseOsAbi` | `(s : String) -> Except CliError OsAbi` |
| 168 | def | `splitColonDelimited` | `(s : String) -> List String` |
| 172 | structure | `State` | (parser state) |
| 183 | def | `State.push` | `(s : State) (op : Op) -> State` |
| 187 | def | `needArg` | `(flag : String) (args : List String) -> Except CliError (String x List String)` |
| 195 | def (partial) | `parseLoop` | `State -> List String -> Except CliError State` |
| 289 | def | `resolveArgument` | `(s : String) -> IO (Except CliError String)` |
| 303 | def | `resolveArgs` | `(args : List String) -> IO (Except CliError (List String))` |
| 322 | def | `parseArgs` | `List String -> Except CliError Invocation` |
| 343 | def | `resolveDynstrName` | `(e : ElfFile) (off : UInt64) -> Option String` |
| 350 | def | `neededLibs` | `(e : ElfFile) -> List String` |
| 358 | def | `findDynstrByTag` | `(e : ElfFile) (tag : DynTag) -> Option String` |
| 365 | def | `rpathValue` | `(e : ElfFile) -> Option String` |
| 369 | def | `sonameValue` | `(e : ElfFile) -> Option String` |
| 374 | def | `execstackState` | `(e : ElfFile) -> Option Bool` |
| 385 | def | `readInterpPath` | `(ib : ByteArray) -> Option ByteArray` |
| 392 | inductive | `RunResult` | (op execution result variants) |
| 401 | def (private) | `badPrecondition` | `(opName detail : String) -> CliError` |
| 405 | def (private) | `policyForce` | `(p : RpathTagPolicy) -> Bool` |
| 417 | def (private) | `runDynOp` | dispatch on dynamic-section ops |
| 434 | def (private) | `runOpNoPre` | dispatch on no-precondition ops |
| 447 | def | `runOp` | `(_opts : Options) (op : Op) (v : ParsedElf) -> Except CliError RunResult` |

## Patchelf/Elf/Basic.lean

| Line | Kind | Name | Signature |
|---|---|---|---|
| 33 | inductive | `OsAbi` | OS/ABI byte enum (sysv, hpux, netbsd, linux, ..., raw) |
| 41 | instance | `DecidableEq OsAbi` | |
| 58 | def | `OsAbi.encode` | `OsAbi -> UInt8` |
| 70 | def | `OsAbi.ofByte` | `(b : UInt8) -> OsAbi` |
| 79 | theorem | `OsAbi.encode_ofByte` | `(b : UInt8) -> (OsAbi.ofByte b).encode = b` |
| 98 | theorem | `OsAbi.ofByte_encode` | `(a : OsAbi) -> OsAbi.ofByte a.encode = a` |
| 111 | def | `OsAbi.display` | `OsAbi -> String` |
| 119 | structure | `ElfIdent` | head + osAbi + tail bytes |
| 135 | structure | `ElfHeader` | ident, type, machine, version, entry, phoff, shoff, flags, ehsize, phentsize, phnum, shentsize, shnum, shstrndx |
| 154 | def | `DynTag.RawDisjoint` | `(t : Int64) -> Prop` |
| 159 | instance | `DecidablePred DynTag.RawDisjoint` | |
| 169 | inductive | `DynTag` | Dynamic tag enum (null, needed, pltrelsz, ..., raw) |
| 190 | instance | `DecidableEq DynTag` | |
| 276 | def | `DynTag.encode` | `DynTag -> Int64` |
| 300 | def | `DynTag.isAddressTag` | `DynTag -> Bool` |
| 308 | theorem | `DynTag.encode_toUInt64_toInt64` | `(d : DynTag) -> d.encode.toUInt64.toInt64 = d.encode` |
| 315 | def | `DynTag.decode` | `(t : Int64) -> DynTag` |
| 344 | theorem | `DynTag.decode_encode` | `(t : Int64) -> (DynTag.decode t).encode = t` |
| 407 | theorem | `DynTag.decode_encode_dyntag` | `(a : DynTag) -> DynTag.decode a.encode = a` |
| 439 | structure | `DynEntry` | `tag : DynTag, value : UInt64` |
| 446 | def | `DynTag.encodeU64` | `DynTag -> UInt64` |
| 450 | def | `DynTag.decodeU64` | `UInt64 -> DynTag` |
| 457 | theorem | `DynTag.encodeU64_decodeU64` | `(u : UInt64) -> ...` |
| 468 | theorem | `DynTag.decodeU64_encodeU64` | `(t : DynTag) -> ...` |
| 475 | def | `DynEntry.isRpathish` | `DynEntry -> Bool` |
| 481 | def | `DynEntry.isStringRef` | `DynEntry -> Bool` |
| 488 | theorem | `DynEntry.isStringRef_iff` | iff form of `isStringRef` |
| 496 | theorem | `DynEntry.not_rpathish_of_null` | `{d : DynEntry} -> d.tag = null -> ¬ d.isRpathish` |
| 510 | structure | `Symbol` | name, info, other, shndx, value, size |
| 527 | structure | `Vernaux` | hash, flags, other, name, next |
| 548 | structure | `Verneed` | vn_version, vn_cnt, vn_file, vn_aux, vn_next, aux (Array Vernaux) |
| 582 | structure | `SysVHashTable` | nbuckets, nchain, buckets, chain |
| 607 | structure | `GnuHashTable` | nbuckets, symoffset, bloomShift, bloom, buckets, chain |
| 617 | structure | `StringTable` | `bytes : ByteArray` |
| 624 | def | `WellFormed` | `(st : StringTable) -> Prop` (null-termination) |
| 627 | instance | `Decidable st.WellFormed` | |
| 638 | def | `findNullFrom` | `(bs : ByteArray) (lo i : Nat) -> Option ByteArray` |
| 647 | def | `lookup` | `(st : StringTable) (offset : Nat) -> Option ByteArray` |
| 655 | def | `findOffsetOf` | `(st : StringTable) (target : ByteArray) -> Option Nat` |
| 668 | def | `append` | `(st : StringTable) (s : String) -> StringTable x Nat` |
| 675 | theorem | `append_size` | size after append |
| 684 | theorem | `append_size_le` | original size ≤ size after append |
| 691 | `@[simp]` theorem | `append_offset` | offset returned equals pre-size |
| 695 | theorem (private) | `triple_append_last` | extract of `(st.bytes ++ payload ++ x)` recovers payload tail |
| 711 | theorem | `append_offset_toNat_lt_appended_u64` | UInt64 fit on append |
| 718 | theorem | `append_offset_toNat_lt_appended_u32` | UInt32 fit on append |
| 735 | def | `NoNullBytes` | `ByteArray -> Prop` |
| 738 | instance | `Decidable (NoNullBytes bs)` | |
| 747 | theorem | `findNullFrom_of_runway` | finds null byte after runway |
| 777 | theorem (private) | `triple_extract_middle` | extract of `(a ++ b)` middle |
| 796 | theorem | `append_lookup` | post-append, the new offset looks up the new string |
| 866 | theorem | `append_lookup_u64` | UInt64 wrapper |
| 877 | theorem | `append_lookup_u32` | UInt32 wrapper |
| 886 | theorem | `append_wellFormed` | append preserves WellFormed |
| 915 | def | `sysvHash` | `ByteArray -> UInt32` |
| 932 | def | `gnuHash` | `ByteArray -> UInt32` |
| 945 | structure | `ProgramHeader` | type, flags, offset, vaddr, paddr, filesz, memsz, align |
| 958 | structure | `SectionHeader` | name, type, flags, addr, offset, size, link, info, addralign, entsize |
| 972 | theorem | `Option.get_witness` | `{α : Type} {o : Option α} (h : o.isSome) -> ...` |

## Patchelf/Elf/ByteLevel.lean (M)

This file contains DSL-emitted lemma factories. Listed individually:

| Line | Kind | Name | Signature |
|---|---|---|---|
| 37–40 | `@[simp]` theorems | `writeU8_size`, `writeU16_size`, `writeU32_size`, `writeU64_size` | size of write is bytewidth |
| 58 | def (private) | `buildReadByteLemma` | macro helper (Lean elab) |
| 79, 93, 102 | private theorems (DSL-emitted) | per-byte `readU{16,32,64}_eq_byte_combine` family | byte-level decomposition |
| 112 | def (private) | `buildGetElemLemma` | macro helper |
| 154 | theorem | `writeU8_readU8_extract` | readU8 of writeU8-into-buf at off recovers v |
| 172 | theorem | `writeU16_readU16_extract` | readU16 of writeU16-into-buf at off recovers v |
| 192 | theorem | `writeU32_readU32_extract` | readU32 of writeU32-into-buf at off recovers v |
| 216 | theorem | `writeU64_readU64_extract` | readU64 of writeU64-into-buf at off recovers v |
| 279 | theorem | `readU8_writeU8` | rfl |
| 281 | theorem | `readU16_writeU16` | `readU16 (writeU16 v) 0 = v` |
| 291 | theorem | `readU32_writeU32` | `readU32 (writeU32 v) 0 = v` |
| 305 | theorem | `readU64_writeU64` | `readU64 (writeU64 v) 0 = v` |
| 331/336/341 | theorems | `writeU{16,32,64}_decodeU{...}_extract` | extract reads recover writer values |
| 357–417 | theorems | `readU{8,16,32,64}_append_{left,right}` | reading from `(a ++ b)` reduces to `a` or `b` |
| 438 | theorem | `writeArray_fixed_extract` | `{α} (N : Nat) ... (...) -> ...` (general writeArray + extract identity) |
| 542/553/565 | theorems | `writeArray_writeU{16,32,64}_extract` | writeArray + writeU extract identity |
| 585 | theorem | `writeArray_push` | `writeArray f (l.push x) = ...` |
| 596 | theorem (private) | `writeArray_uniform_extract_aux` | uniform-width auxiliary |
| 665 | theorem | `writeArray_uniform_extract_at_index` | extract at index in uniform writeArray |
| 671 | theorem (private) | `readU32_writeArray_aux` | induction helper |
| 710 | theorem | `readU32_writeArray` | `readU32 (writeArray writeU32 arr) (i*4) = arr[i]` |
| 714 | theorem (private) | `readU64_writeArray_aux` | induction helper |
| 753 | theorem | `readU64_writeArray` | UInt64 analogue |
| 757 | theorem (private) | `readU16_writeArray_aux` | induction helper |
| 796 | theorem | `readU16_writeArray` | UInt16 analogue |
| 806 | structure | `ByteWidth (α : Type)` | uniform fixed-width byte writer/reader bundle (`size`, `write`, `decode`, `lift`) |
| 817 | theorem | `writeArray_of_width` | uniform extract via ByteWidth |
| 828 | def | `ByteWidth.u16` | `ByteWidth UInt16` |
| 836 | def | `ByteWidth.u32` | `ByteWidth UInt32` |
| 844 | def | `ByteWidth.u64` | `ByteWidth UInt64` |
| 859 | theorem | `readU8_extract_eq` | reading from extract = reading from base |
| 869 | theorem | `readU16_extract_eq` | "" |
| 877 | theorem | `readU32_extract_eq` | "" |
| 889 | theorem | `readU64_extract_eq` | "" |
| 904 | theorem | `ByteArray.extract_extract_window` | extract-of-extract sliding window identity |
| 926 | theorem | `ByteArray.extract_append_left_within` | extract within left side of `a ++ b` |
| 940 | theorem | `ByteArray.extract_empty_of_size_le` | extract returns empty when out-of-range |

## Patchelf/Elf/ByteRoundtrip.lean (M)

This is the largest verification file (~2900 LOC). Mostly private threading-lemmas; the public surface is the master theorems near the end.

**Public master theorems / surface:**

| Line | Kind | Name | Signature |
|---|---|---|---|
| 83 | theorem | `encode_size_eq` | `(e : ElfFile) -> (encode e).size = encodedFileSize e` |
| 353 | structure | `IdentBytesValid` | head_size + magic bytes + classByte + dataByte (7 fields) |
| 484 | theorem | `parseHeader_encode` | `(e : ElfFile) (... preconditions ...) -> parseHeader (encode e) = .ok e.header` |
| 808 | theorem | `phdrs_decode_encode` | decodePhdrs over `encode e` = `e.phdrs` (under preconditions) |
| 1069 | theorem | `shdrs_decode_encode` | decodeShdrs over `encode e` = shdr-projection of `e.sections` |
| 1428 | theorem | `decodeDynamic_writeArray_eq` | decoder over writeArray identity |
| 1944 | theorem | `isValid_to_hDynWF` | `(e : ElfFile) (hVal : e.IsValid) -> ... hDynWF` (dynamic well-formedness) |
| 2004 | theorem | `section_decode_encode` | per-section decodeSectionContent recovers original content |
| 2162 | structure | `DecodeRoundtripWitness` | bundle: `parseHeader_ok`, `phdrs_decode`, `shdrs_decode`, `section_decode` |
| 2208 | structure | `EncodePreconditions` | 10-field bundle: syncOk, spliceDisjoint, identValid, sizeFit, nullEmpty, headerFit_{entry,phoff,shoff}, phdrFit, shdrFit (typesMatch dropped after IR migration; see STATUS.md) |
| 2251 | theorem | `EncodePreconditions.layoutOk` | precondition-bundle implies layoutAlreadyValid |
| 2259 | theorem | `decodeRoundtripWitness_of_preconditions` | `IsValid + EncodePreconditions -> DecodeRoundtripWitness` |
| 2327 | theorem | **`parse_encode_roundtrip`** | **MASTER**: `(e : ParsedElf) (hPre : EncodePreconditions e.elf) -> parse (encode e.elf) = .ok e` |
| 2350 | theorem | `parse_encode_roundtrip_witness` | bundle-form variant |
(stale: `sectionFromShdr_typeContentMatches` and `sectionsFromShdrs_typeContentMatch` removed by the SectionContent IR migration — type↔content match is now structural)
| 2439 | theorem | `identBytesValid_of_decodeHeader` | parser output satisfies IdentBytesValid |
| 2481 | theorem | `parseHeader_byte_facts` | byte-level facts about parser output |
| 2590 | theorem | `syncDtStrszInFile_eq_id` | `dynStrszCoherent -> syncDtStrszInFile e = e` |
| 2667 | theorem | `identBytesValid_of_header` | IdentBytesValid is invariant under non-header changes |
| 2695 | theorem | `identBytesValid_of_parseHeader_ok` | parser-derived ElfFile has IdentBytesValid |
| 2714 | theorem | `sectionFromShdr_encodedSize_le` | size-bound preservation |
| 2763 | theorem | `sectionFromShdr_null_empty` | SHT_NULL produces empty raw content |
| 2811 | theorem | `encodePreconditions_of_parser` | parser output satisfies EncodePreconditions |

**Private threading-lemma families (~50 lemmas, listed by anchor lines):**
- `readU{8,16,32,64}_encode_in_header` (127, 228, 240, 251)
- `getElem_encode_in_header` (264), `extract_encode_eq_header_write` (279), `decodeHeader_encode` (311)
- `write_extract_head` (371), `extract_encode_eq_ident_head` (426), `readU8_encode_eq_ident_head` (443)
- `readU{8,16,32,64}_encode_in_phdr` (577, 667, 681, 701)
- `getElem_encode_in_phdr` (716), `extract_encode_eq_phdrs_writer` (733), `decodePhdr_writeArray_at_index` (761)
- `readU{8,16,32,64}_encode_in_shdr` (896, 965, 979, 999)
- `getElem_encode_in_shdr` (1015), `extract_encode_eq_shdrs_writer` (1031)
- `readU{8,16}_encode_in_section` (1151, 1221)
- `readBytes_writeContent_eq` (1245), `readBytes_encode_in_section` (1260)
- `decodeDynEntry_writeArray_at_index` (1302), `decodeDynamicLoop_writeArray_step` (1327)
- `decodeDynamicLoop_congr` (1446), `decodeDynamic_congr` (1477), `decodeDynamic_encode_dynamic` (1492)
- `decodeSym_writeArray_at_index` (1614)
- `readU16_writeArray_writeU16_at` (1637), `decodeVersym_encode_versym` (1651)
- `decodeDynsym_encode_dynsym` (1697), `decodeStringTable_encode_strtab` (1798)
- `decodeRaw_encode_raw` (1825), `decodeRaw_encode_null` (1859)
- `encodedSize_toUInt64_toNat` (1912), `dynamic_eq_some_of_section` (1921)
- `uint64_toNat_toUInt64` (2562), `updateSectionContent_eq_self` (2568)
- `sectionsFromShdrs_eq` (2285)

## Patchelf/Elf/SchemaDSL.lean (M)

Internal Lean macro implementation; nothing public. Key entries:

| Line | Kind | Name | Notes |
|---|---|---|---|
| 255 | inductive (private) | `FieldKind` | DSL field kinds (raw, wrap_nat, wrap, prec, embedAt, etc.) |
| 303 | def (private) | `FieldKind.byteSize` | `FieldKind -> Nat` |
| 311 | structure (private) | `FieldSpec` | one field's spec (name, kind, width) |
| 317 | def (private) | `FieldSpec.byteSize` | accessor |
| 319 | def (private) | `parseWidthTok?` | width literal parser |
| 327 | def (private) | `parseFieldStx` | field syntax -> FieldSpec |
| 407/410/413 | def (private) | `rootElfNs`, `rootDecodeNs`, `rootByteWidthNs` | namespace helpers |
| 418/421/425 | def (private) | `writeUIdent`, `readUIdent`, `writeReadExtractIdent` | ident builders |
| 443 | def (private) | `writeFieldTerm` | field-term emitter |
| 468 | def (private) | `writeBodyQuoted` | DSL write body |
| 479 | def (private) | `decodeFieldAssigns` | DSL decode field assignment |
| 533 | def (private) | `postRewriteFieldTerm` | rewrite helper |
| 554 | def (private) | `roundtripProofTactics` | tactic block for roundtrip proof |
| 680 | def (private) | `wrapNatFitBinders` | binder builder for fit hypotheses |
| 705 | def (private) | `writePrefixChain` | concat chain |
| 725 | def (private) | `forwardFieldTactics` | tactic block (forward fields) |
| 779/811 | def (private) | `forwardProofTactics`, `forwardProofTacticsPrec` | forward proof tactic emitters |
| 885 | structure (private) | `SchemaOpts` | DSL options (precond?, decoder kind, etc.) |
| 900 | def (private) | `parseOpts` | options syntax parser |
| 924 | def | `elabElfSchema : CommandElab` | the `elf_schema` macro elaborator |

The DSL emits, per schema invocation: `<T>.write` (def), `<T>.decode` (def), `<T>_decode_write` (theorem), `<T>_write_decode<T>_extract` (theorem; e.g. `DynEntry_write_decodeDynEntry_extract`), `ByteWidth <T>` (def), and array variants.

## Patchelf/Elf/Schemas.lean

| Line | Kind | Name | Signature |
|---|---|---|---|
| 59 | theorem | `writeArray_DynEntry_size` | `writeArray DynEntry.write dyn |.size = dyn.size * 16` |
| 96 | theorem | `ElfIdent_decode_write` | `ElfIdent.decode (ElfIdent.write id) 0 _ = id` |
| 138 | theorem | `decodeElfIdent_append_left` | decode with extra bytes appended is invariant |
| 170 | structure | `DecodedIdent` | (intermediate decoder result) |
| 179 | def | `decodeIdent` | `(bs : ByteArray) (off : Nat) (h : off + 16 ≤ bs.size) -> ...` |
| 281 | def | `decodeDynamicLoop` | recursive decoder for `.dynamic` |
| 296 | def | `decodeDynamic` | top-level dynamic decoder |
| 300 | theorem | `decodeDynamicLoop_size_le` | output size bound |
| 322 | theorem | `decodeDynamic_size_le` | output size bound |
| 332 | def | `decodeVernauxChain` | chain decoder |
| 337 | def | `decodeVerneed` | one Verneed |
| 348 | def | `decodeVerneedChain` | chain decoder |
| 352 | theorem | `decodeVerneedChain_size_le` | size bound |
| 357 | theorem | `decodeVernauxChain_size_le` | size bound |
| 427 | def | `decodeHeaderSlice` | `(bs : ByteArray) (h : 64 ≤ bs.size) -> ElfHeader` |
| 436 | theorem | `decodeHeader_eq_slice` | header decoder = slice variant |
| 489 | theorem | `decodePhdr_eq_slice` | phdr decoder = slice |
| 507 | theorem | `decodeDynEntry_eq_slice` | dyn entry decoder = slice |
| 519 | theorem | `decodeSym_eq_slice` | symbol decoder = slice |
| 532 | theorem | `decodeShdr_eq_slice` | shdr decoder = slice |
| 555 | def | `Verneed.writeHeader` | header-only writer |
| 563 | def | `Verneed.write` | full Verneed writer |
| 568 | def | `SysVHashTable.write` | writer |
| 576 | def | `GnuHashTable.write` | writer |

(Note: this file also imports `elf_schema` — DSL invocations earlier in the file emit additional `ElfIdent.write/decode/lemmas`, `ProgramHeader.write/decode/lemmas`, etc., that don't appear via the simple grep.)

## Patchelf/Elf/ElfFile.lean

| Line | Kind | Name | Signature |
|---|---|---|---|
| 44 | inductive | `SectionContent` | `\| raw (bytes) \| strtab (st) \| dynamic (entries) \| dynsym (syms) \| versym (entries) \| nobits` |
| 56 | def | `SectionContent.WellFormed` | `SectionContent -> Prop` |
| 65 | instance | `Decidable c.WellFormed` | |
| 80 | structure | `Section` | name, type, flags, addr, offset, link, info, addralign, entsize, content |
| 97 | def | `Section.encodedSize` | `Section -> Nat` |
| 112 | structure | `ElfFile` | header + phdrs + sections (no `bytes` field) |
| 125 | def | `firstIdxWhereIn` | `(sections : Array Section) (p : Section -> Bool) -> Option Nat` |
| 136 | def | `firstIdxWhere` | wrapper |
| 143 | def | `findUniqueTypeIdx` | `ElfFile -> ShType -> Option Nat` |
| 147 | def | `shstrtab` | `ElfFile -> Option StringTable` |
| 158 | def | `findIdxByName` | `ElfFile -> ByteArray -> Option Nat` |
| 169–176 | def | `dynamicIdx`, `dynsymIdx`, `sysvHashIdx`, `verneedIdx`, `versymIdx`, `gnuHashIdx`, `dynstrIdx`, `interpIdx` | section-index accessors |
| 180 | def | `contentAt` | `ElfFile -> Option Nat -> Option SectionContent` |
| 198–208 | def (DSL-emitted via `section_content_accessor`) | `dynamic`, `dynstr`, `dynsym`, `interp`, `versym`, `verneedRaw`, `sysvHashRaw`, `gnuHashRaw` | content-typed accessors |
| 213 | def | `headerCountsConsistent` | `ElfFile -> Prop` |
| 220 | instance | `Decidable e.headerCountsConsistent` | |
| 224 | def | `sectionsWellFormed` | sections[0] is SHT_NULL |
| 227 | instance | `Decidable e.sectionsWellFormed` | |
| 232 | def | `Section.strtabWellFormedB` | `Section -> Bool` |
| 240 | def | `strtabsWellFormed` | `ElfFile -> Prop` |
| 243 | instance | `Decidable e.strtabsWellFormed` | |
| 247 | def | `Section.contentWellFormedB` | `Section -> Bool` |
| 251 | def | `sectionsContentWellFormed` | |
| 254 | instance | `Decidable e.sectionsContentWellFormed` | |
(stale: `Section.typeContentMatchesB` and `sectionsTypeContentMatch` removed by the SectionContent IR migration — `Section.type` is now derived from `content.type`, and `SectionContent.raw` carries a non-structural-type proof)
| 298 | def | `dynamicTerminated` | last `.dynamic` entry is null |
| 305 | instance | `Decidable e.dynamicTerminated` | |
| 323 | def | `dynamicStringRefsValid` | string-ref offsets in bounds |
| 328 | instance | `Decidable e.dynamicStringRefsValid` | |
| 344 | def | `dynamicWellFormed` | conjunction |
| 347 | instance | `Decidable e.dynamicWellFormed` | |
| 351 | def | `dynsymNamesInBounds` | symbol names in dynstr |
| 355 | instance | `Decidable e.dynsymNamesInBounds` | |
| 369 | def | `typeUniqueAt` | per-type uniqueness |
| 375 | instance | `Decidable (e.typeUniqueAt ty)` | |
| 381 | theorem | `findUniqueTypeIdx_eq_some` | iff lemma |
| 421 | def | `sectionsAtDistinctTypes` | structural types unique |
| 429 | instance | `Decidable e.sectionsAtDistinctTypes` | |
| 433 | def | `nameUniqueAt` | named-section uniqueness |
| 440 | instance | `Decidable (e.nameUniqueAt st nm)` | |
| 446 | def | `namedSectionsUnique` | conjunction over named sections |
| 453 | instance | `Decidable e.namedSectionsUnique` | |
| 459 | structure | `IsValid` | 8 fields: header_counts, sections_wf, strtabs_wf, dynamic_wf, dynsym_wf, content_wf, types_distinct, names_unique |
| 469 | instance | `Decidable e.IsValid` | |
| 502 | def | `IntervalDisjoint` | `(a₁ a₂ b₁ b₂ : Nat) -> Prop := a₂ ≤ b₁ ∨ b₂ ≤ a₁` |
| 505 | instance | `Decidable (IntervalDisjoint ...)` | |
| 512 | def | `sectionsNonOverlapping` | `ElfFile -> Prop` |
| 523 | instance | `Decidable e.sectionsNonOverlapping` | |
| 527 | def | `ptInterpAgreement` | PT_INTERP offset matches `.interp` section |
| 536 | instance | `Decidable e.ptInterpAgreement` | |
| 540 | def | `ptDynamicAgreement` | PT_DYNAMIC offset matches `.dynamic` section |
| 549 | instance | `Decidable e.ptDynamicAgreement` | |
| 553 | def | `segmentCongruence` | PT_LOAD vaddr/offset alignment congruence |
| 560 | instance | `Decidable e.segmentCongruence` | |
| 578 | def | `headerPhdrDisjoint` | IntervalDisjoint over the 4 splice regions |
| 583 | instance | `Decidable e.headerPhdrDisjoint` | |
| 587 | def | `headerShdrDisjoint` | |
| 592 | instance | `Decidable e.headerShdrDisjoint` | |
| 596 | def | `phdrShdrDisjoint` | |
| 601 | instance | `Decidable e.phdrShdrDisjoint` | |
| 605 | def | `headerSectionDisjoint` | |
| 613 | instance | `Decidable e.headerSectionDisjoint` | |
| 617 | def | `phdrSectionDisjoint` | |
| 625 | instance | `Decidable e.phdrSectionDisjoint` | |
| 629 | def | `shdrSectionDisjoint` | |
| 637 | instance | `Decidable e.shdrSectionDisjoint` | |
| 648 | structure | `spliceRegionsDisjoint` | 7-field bundle of all splice-region disjointness |
| 657 | instance | `Decidable e.spliceRegionsDisjoint` | |
| 671 | structure | `IsLoadable` | extends IsValid + sections_nonoverlapping + pt_interp_agrees + pt_dynamic_agrees + segment_congruent |
| 677 | instance | `Decidable e.IsLoadable` | |
| 695 | def | `dynAddressCoherentForTag` | per-tag dyn-address coherence |
| 706 | instance | `Decidable (dynAddressCoherentForTag ...)` | |
| 727 | def | `dynStrszCoherent` | DT_STRSZ matches `.dynstr.bytes.size` |
| 732 | instance | `Decidable e.dynStrszCoherent` | |
| 746 | structure | `dynamicAddressCoherent` | 6-field bundle |
| 754 | instance | `Decidable e.dynamicAddressCoherent` | |
| 768 | structure | `IsFullyValid` | extends IsLoadable + dyn_addrs_coherent |
| 771 | instance | `Decidable e.IsFullyValid` | |

## Patchelf/Elf/Encoder.lean

| Line | Kind | Name | Signature |
|---|---|---|---|
| 48 | def | `Section.writeContent` | `Section -> ByteArray` |
| 59 | def | `toShdr` | `Section -> SectionHeader` |
| 66 | def | `encodedFileSize` | `ElfFile -> Nat` |
| 77 | def | `zeroBytes` | `Nat -> ByteArray` |
| 80 | `@[simp]` theorem | `zeroBytes_size` | `(zeroBytes n).size = n` |
| 91 | def | `syncDtStrszInFile` | `ElfFile -> ElfFile` (sync DT_STRSZ before encode) |
| 102 | def | `sectionFoldStep` | foldl step for sections into buffer |
| 114 | `@[irreducible]` def | `encodeBody` | `ElfFile -> ByteArray` |
| 127 | theorem | `encodeBody_eq` | unfolds the irreducible body |
| 148 | `@[irreducible]` def | `encode` | `ElfFile -> ByteArray` (top-level encoder) |
| 153 | theorem | `encode_eq` | unfolds the irreducible top-level |
| 169 | theorem | `Section_writeContent_size_eq` | `(s.writeContent).size = s.encodedSize` |
| 203 | theorem | `readU8_foldl_section_splice_preserved` | reading at off outside section regions is preserved by section foldl |
| 265 | theorem | `readU16_foldl_section_splice_preserved` | UInt16 analogue |
| 283 | theorem | `readU32_foldl_section_splice_preserved` | UInt32 analogue |
| 305 | theorem | `readU64_foldl_section_splice_preserved` | UInt64 analogue |
| 343 | theorem | `readU8_foldl_section_recovers` | reading inside section recovers section content |
| 518 | theorem | `encodeBody_size_eq` | `(encodeBody e).size = encodedFileSize e` |
| 535 | theorem | `encodedFileSize_ge_ehdr` | size ≥ 64 |
| 542 | theorem | `encodeBody_size_ge_ehdr` | corollary |
| 569 | theorem | `phdr_end_le_encodedFileSize` | phdr-table end fits |
| 576 | theorem | `shdr_end_le_encodedFileSize` | shdr-table end fits |
| 585 | theorem | `section_end_le_encodedFileSize` | per-section end fits |

## Patchelf/Elf/Decode.lean

| Line | Kind | Name | Signature |
|---|---|---|---|
| 29 | def | `buildArray` | `{α} (n : Nat) (f : Nat -> α) -> Array α` |
| 32 | `@[simp]` theorem | `buildArray_size` | `(buildArray n f).size = n` |
| 40 | theorem | `buildArray_getElem` | element at i = f i |
| 52 | def | `decodeStringTable` | `ByteArray -> Nat -> Nat -> StringTable` |
| 60 | theorem | `decodeStringTable_bytes_size` | size lemma |
| 71 | theorem | `bytes_extract_size` | extract size lemma |
| 81 | def | `decodeVersym` | `(bs : ByteArray) (off n : Nat) -> Array UInt16` |
| 84 | `@[simp]` theorem | `decodeVersym_size` | `(decodeVersym bs off n).size = n` |
| 93 | def | `decodeChainLoop` | generic chain decoder |
| 109 | def | `decodeChain` | wrapper |
| 117 | theorem | `decodeChainLoop_size_le` | output size bound |
| 135 | theorem | `decodeChain_size_le` | output size bound |
| 144 | def (private) | `readU32Array` | `(bs : ByteArray) (off n : Nat) -> Array UInt32` |
| 148 | def (private) | `readU64Array` | analogue |
| 154 | `@[simp]` theorem | `readU32Array_eq` | normalization to buildArray form |
| 157 | `@[simp]` theorem | `readU64Array_eq` | analogue |
| 166 | def | `decodeSysVHash` | `ByteArray -> Nat -> Nat -> SysVHashTable` |
| 180 | def | `decodeGnuHash` | `ByteArray -> Nat -> Nat -> GnuHashTable` |
| 201 | `@[simp]` theorem | `decodeSysVHash_buckets_size` | |
| 209 | `@[simp]` theorem | `decodeSysVHash_chain_size` | |
| 217 | `@[simp]` theorem | `decodeGnuHash_bloom_size` | |
| 225 | `@[simp]` theorem | `decodeGnuHash_buckets_size` | |
| 235 | `@[simp]` theorem | `decodeGnuHash_chain_size` | |

## Patchelf/Elf/Layout.lean

This file is mostly Nat wrappers and constants.

| Line | Kind | Name | Signature |
|---|---|---|---|
| 27 | structure | `FileOffset` | `val : Nat` deriving DecidableEq, Repr |
| 29 | structure | `VirtualAddr` | `val : Nat` |
| 31 | structure | `PhysicalAddr` | `val : Nat` |
| 33 | structure | `ByteSize` | `val : Nat` |
| 35 | structure | `Alignment` | `val : Nat` |
| 48–56 | def | `ehdrSize`, `phdrSize`, `shdrSize`, `dynEntrySize`, `symEntrySize` | constants 64, 56, 64, 16, 24 |
| 62–71 | def | `EI_MAG0`..`EI_NIDENT` | EI_* index constants |
| 74 | def | `magic` | `ByteArray := <0x7f, 'E', 'L', 'F'>` |
| 81 | inductive | `ElfClass` | `\| elf32 \| elf64 \| raw (b : UInt8)` |
| 84 | def | `ElfClass.encode` | `ElfClass -> UInt8` |
| 90 | inductive | `ElfData` | `\| lsb \| msb \| raw (b : UInt8)` |
| 93 | def | `ElfData.encode` | `ElfData -> UInt8` |
| 107 | inductive | `Ehdr` | byte-offset enum (type, machine, version, ...) |
| 113 | def | `Ehdr.byteOffset` | `Ehdr -> Nat` |
| 130 | inductive | `Phdr` | byte-offset enum |
| 134 | def | `Phdr.byteOffset` | `Phdr -> Nat` |
| 145 | inductive | `Shdr` | byte-offset enum |
| 149 | def | `Shdr.byteOffset` | `Shdr -> Nat` |
| 162 | inductive | `Sym` | byte-offset enum |
| 166 | def | `Sym.byteOffset` | `Sym -> Nat` |
| 176/179 | def | `verneedSize`, `vernauxSize` | `Nat := 16` |
| 183 | inductive | `VerneedField` | byte-offset enum |
| 187 | def | `VerneedField.byteOffset` | |
| 195 | inductive | `VernauxField` | byte-offset enum |
| 199 | def | `VernauxField.byteOffset` | |
| 214 | structure | `ShType` | `raw : UInt32` |
| 216 | structure | `PhType` | `raw : UInt32` |
| 219–235 | def | `SHT_NULL`, `SHT_PROGBITS`, ..., `SHT_GNU_VERSYM` | constants |
| 239–249 | def | `PT_NULL`, `PT_LOAD`, ..., `PT_GNU_EH_FRAME` | constants |
| 255–264 | def | `PF_X`, `PF_W`, `PF_R`, `PF_R_ONLY`, `PF_RW` | program flag constants |
| 274 | def | `roundUp` | `(n align : Nat) -> Nat` |

## Patchelf/Elf/LayoutEngine.lean

| Line | Kind | Name | Signature |
|---|---|---|---|
| 30 | def (private) | `Section.withOffset` | `(s : Section) (newOff : Nat) -> Section` |
| 33 | def (private) | `phdrWithOffsetSize` | phdr offset/size update helper |
| 46 | def | `layoutAlreadyValid` | `ElfFile -> Bool` |
| 49 | theorem | `layoutAlreadyValid_iff` | iff form |
| 55 | theorem | `layoutAlreadyValid_of_spliceRegionsDisjoint` | implication from disjointness |
| 63 | def (private) | `layoutStep` | foldl step `(Array Section x Nat) -> (Nat x Section) -> ...` |
| 84 | def (private) | `layoutSectionsFold` | foldl driver |
| 92 | def (private) | `relocatePhdr` | phdr relocation helper |
| 126 | def | `layoutForEncoding` | `ElfFile -> ElfFile` (the layout engine entry point) |
| 156 | def | `layoutFullyValid` | `ElfFile -> Bool := decide e.spliceRegionsDisjoint` |
| 158 | theorem | `layoutFullyValid_iff` | iff form |
| 162 | theorem | `spliceRegionsDisjoint_of_layoutFullyValid` | implication |
| 171/174/177/182 | `@[simp]` private theorems | `withOffset_type`, `withOffset_content`, `withOffset_encodedSize`, `withOffset_addralign` | accessor lemmas |
| 187 | theorem | `le_roundUp` | `n ≤ roundUp n align` |
| 207 | theorem (private) | `step_size_eq` | array size after step |
| 216 | theorem (private) | `step_cursor_mono` | cursor monotonicity |
| 232 | theorem (private) | `layoutStep_getElem_lt` | element access bound |
| 243 | theorem (private) | `size_eq` | foldl preserves size |
| 261 | theorem (private) | `cursor_floor` | cursor lower bound |
| 286 | structure (private) | `Placement` | placement invariant motive |
| 303/329 | theorems (private) | `placement_step_existing`, `placement_step_new` | motive preservation |
| 390 | theorem (private) | `Placement.exempt_to_NOBITS_or_NULL` | exempt sections classification |
| 415 | def (private) | `PairDisjoint` | pairwise disjointness motive |
| 426 | theorem (private) | `pairDisjoint_symm` | symmetry |
| 444 | theorem (private) | `pairDisjoint_step_existing` | step preserves PairDisjoint (existing pair) |
| 466 | theorem (private) | `pairDisjoint_step_new_vs_old` | step new-vs-old pair |
| 524 | structure (private) | `LayoutInv` | combined invariant motive (Placement + PairDisjoint) |
| 541 | theorem | `layoutSectionsFold_inv` | invariant preserved |
| 626 | theorem | `layoutSectionsFold_placement` | output satisfies Placement |
| 635 | theorem | `layoutSectionsFold_pairDisjoint` | output satisfies PairDisjoint |
| 672 | theorem | **`layoutForEncoding_produces_spliceRegionsDisjoint`** | the structural piece for ROADMAP 1.3a |

## Patchelf/Elf/Adapter.lean

| Line | Kind | Name | Signature |
|---|---|---|---|
| 35 | inductive | `AdapterError` | error variants |
| 63 | def (private) | `fallbackStringSection` | `StringSection` (empty fallback) |
| 75 | def | `mkStringSection` | `StringTable -> StringSection` |
| 81 | def | `mkStringSectionOpt` | `Option StringTable -> StringSection` |
| 87 | def | `typedSymOfByteSymbol` | `(ds : StringSection) (idx : Nat) (s : Symbol) -> Option (TypedSymbol ds)` |
| 101 | def | `symbolSectionOf` | `(ds : StringSection) (syms : Array Symbol) -> SymbolSection ds` |
| 107 | def | `interpOfBytes` | `ByteArray -> InterpSection` |
| 121 | def | `ofElfFile` | `(e : ElfFile) -> Except AdapterError ValidElfFile` |
| 174 | def | `symbolOfTyped` | `{ds} (s : TypedSymbol ds) -> Symbol` |
| 192 | def | `patchDynamicEntries` | typed -> byte dyn entries |
| 295–342 | def (private) | `applyDynstr`, `applyDynsym`, `applyDynamic`, `applyVersym`, `applySysvHash`, `applyGnuHash`, `applyVerneed`, `applyInterp` | per-section apply helpers |
| 353 | def | `toElfFile` | `(template : ElfFile) (typed : ValidElfFile) -> ElfFile` |

## Patchelf/Elf/AdapterRoundtrip.lean

| Line | Kind | Name | Signature |
|---|---|---|---|
| 36 | `@[simp]` theorem | `toElfFile_header` | `(toElfFile template t).header = template.header` |
| 39 | `@[simp]` theorem | `toElfFile_phdrs` | analogue |
| 51 | theorem | `ofElfFile_header` | parse output preserves header |
| 61 | theorem | `ofElfFile_phdrs` | preserves phdrs |
| 72 | theorem | `ofElfFile_dynstr` | preserves dynstr |
| 82 | theorem | `ofElfFile_versym` | preserves versym |
| 93 | theorem | `roundtrip_header` | `toElfFile e (ofElfFile e) = e` (header part) |
| 98 | theorem | `roundtrip_phdrs` | analogue for phdrs |

## Patchelf/Elf/AuxSections.lean

| Line | Kind | Name | Signature |
|---|---|---|---|
| 24 | structure | `VerneedSection` | typed Verneed wrapper |
| 29 | structure | `SysVHashSection` | typed SysV hash wrapper |
| 34 | structure | `GnuHashSection` | typed GNU hash wrapper |

## Patchelf/Elf/DynamicEncode.lean

| Line | Kind | Name | Signature |
|---|---|---|---|
| 38 | structure | `LayoutCtx` | encoder layout context |
| 56 | `@[inline]` def | `emitNeeded` | `{ds} (off : Fin ds.size) -> DynEntry` |
| 60 | `@[inline]` def | `emitRpath` | analogue |
| 63 | `@[inline]` def | `emitRunpath` | analogue |
| 66 | `@[inline]` def | `emitSoname` | analogue |
| 73 | def | `emitCoherenceTags` | `(ds : StringSection) (ctx : LayoutCtx) -> Array DynEntry` |
| 89 | def | `emitStructuredEntries` | `{ds} (d : DynamicSection ds) -> Array DynEntry` |
| 104 | def | `emitNeededEntries` | `{ds} (d : DynamicSection ds) -> Array DynEntry` |
| 132 | def | `assembleEntries` | `{ds} (d : DynamicSection ds) -> ... -> Array DynEntry` |
| 141 | `@[simp]` theorem | `assembleEntries_back?_null` | last entry is DT_NULL |
| 151 | theorem | `assembleEntries_size` | size lemma |
| 174 | theorem | `needed_offset_emitted` | DT_NEEDED entries are emitted at expected offsets |
| 210 | theorem | `emitNeeded_value_lt` | `{ds} (off : Fin ds.size) -> emitNeeded off |.value < ds.size.toUInt64` |

## Patchelf/Elf/DynamicLemmas.lean

| Line | Kind | Name | Signature |
|---|---|---|---|
| 24 | def | `syncDtStrszEntry` | `(newSize : UInt64) (d : DynEntry) -> DynEntry` |
| 28 | def | `syncDtStrsz` | `(dyn : Array DynEntry) (newSize : UInt64) -> Array DynEntry` |
| 31 | `@[simp]` theorem | `syncDtStrsz_size` | size preserved |
| 35 | `@[simp]` theorem | `syncDtStrszEntry_tag` | tag preserved |
| 40 | `@[simp]` theorem | `syncDtStrszEntry_isStringRef` | predicate preserved |
| 47 | theorem | `syncDtStrszEntry_eq_self` | identity if already in sync |
| 59 | theorem | `syncDtStrsz_eq_id` | array-level identity |

## Patchelf/Elf/DynamicParse.lean

| Line | Kind | Name | Signature |
|---|---|---|---|
| 51 | inductive | `DynamicParseError` | error variants |
| 61 | def (private) | `tryMkFin` | `(ds : StringSection) (v : UInt64) -> Option (Fin ds.size)` |
| 71 | def (private) | `stepEntry` | one-step parser |
| 104 | def | `empty` | `(ds : StringSection) -> DynamicSection ds` |
| 118 | def | `parseFrom` | `(ds : StringSection) (raw : Array DynEntry) -> Except DynamicParseError (DynamicSection ds)` |
| 125 | `@[simp]` theorem | `empty_needed` | empty section has no NEEDED |
| 129 | theorem | `stepEntry_needed_ok` | NEEDED parsing success |
| 145 | theorem | `stepEntry_needed_error` | NEEDED parsing error |
| 167 | theorem | `stepEntry_needed_preservation` | preservation lemma |
| 185 | theorem | `parseFrom_singleton_needed` | singleton parse |
| 205 | theorem | `stepEntry_strtab_dropped` | DT_STRTAB dropped |
| 213 | theorem | `stepEntry_strsz_dropped` | DT_STRSZ dropped |
| 221 | theorem | `stepEntry_coherence_dropped` | coherence tags dropped |

## Patchelf/Elf/DynamicSection.lean

| Line | Kind | Name | Signature |
|---|---|---|---|
| 40 | structure | `DynamicSection (ds : StringSection)` | needed (Array (Fin ds.size)), rpath, runpath, soname (Option Fin ds.size), flags1 (Option UInt64; DT_FLAGS_1), debug (Option UInt64; DT_DEBUG) |
| 61 | def | `rebase` | `{ds ds'} (h : SizeLE ds ds') -> DynamicSection ds -> DynamicSection ds'` |
| 78 | def | `pushNeeded` | `{ds} (d : DynamicSection ds) (off : Fin ds.size) -> DynamicSection ds` |
| 85 | def | `filterNeeded` | filter NEEDED entries by predicate |
| 90 | def | `setRpath` | set RPATH |
| 95 | def | `clearRpath` | clear RPATH |
| 99 | def | `setRunpath` | set RUNPATH |
| 104 | def | `setSoname` | set SONAME |
| 111 | def | `addDebugTag` | add DT_DEBUG |
| 119 | def | `setNoDefaultLib` | set DF_1_NODEFLIB |
| 123 | def | `stripRpath` | clear both RPATH+RUNPATH |
| 128 | def | `setRpathTag` | choose RPATH or RUNPATH per policy |
| 137 | def | `replaceNeededBy` | rewrite NEEDED entries by mapping |
| 145 | def | `filterNeededBy` | filter NEEDED by predicate |
| 153 | def | `setSonameOff` | set SONAME by offset |
| 158 | def | `removeSoname` | clear SONAME |
| 168 | `@[simp]` theorem | `rebase_needed_size` | size after rebase |
| 177 | `@[simp]` theorem | `rebase_needed_getElem` | element after rebase |
| 189 | `@[simp]` theorem | `pushNeeded_needed` | needed after push |
| 197 | `@[simp]` theorem | `pushNeeded_back?` | last element after push |

## Patchelf/Elf/InterpSection.lean

| Line | Kind | Name | Signature |
|---|---|---|---|
| 15 | structure | `InterpSection` | `path : ByteArray` |
| 22 | def | `toBytes` | `(s : InterpSection) -> ByteArray` (path + null) |
| 25 | `@[simp]` theorem | `toBytes_size` | `(toBytes s).size = s.path.size + 1` |
| 32 | def | `ofString` | `String -> InterpSection` |

## Patchelf/Elf/ObservableCombinators.lean

| Line | Kind | Name | Signature |
|---|---|---|---|
| 45 | def | `growDynstrDynamicOp` | combinator: grow dynstr + adjust dynamic |
| 66 | theorem | `growDynstrDynamicOp_observable` | observable property after combinator |
| 101 | def | `mapDynamicOp` | combinator: map over dynamic section |
| 109 | theorem | `mapDynamicOp_observable` | observable property |
| 131 | theorem | `filterNeededBy_lookup_preserved` | filter preserves lookup |
| 151 | theorem | `replaceNeededBy_getElem_rewritten` | replace rewrites element |

## Patchelf/Elf/ParseHeader.lean

| Line | Kind | Name | Signature |
|---|---|---|---|
| 17 | inductive | `ParseError` | parser error variants |
| 61 | def | `parseHeader` | `(bs : ByteArray) -> Except ParseError ElfHeader` |

## Patchelf/Elf/Parser.lean

| Line | Kind | Name | Signature |
|---|---|---|---|
| 63 | def | `decodeSectionContent` | `(bs : ByteArray) (sh : SectionHeader) -> SectionContent` |
| 82 | def | `sectionFromShdr` | `(bs : ByteArray) (sh : SectionHeader) -> Section` |
| 95 | def | `sectionsFromShdrs` | `(bs : ByteArray) (shdrs : Array SectionHeader) -> Array Section` |
| 105 | structure | `ParsedElf` | `elf : ElfFile, isValid : elf.IsValid` |
| 116 | def | `parse` | `(bs : ByteArray) -> Except ParseError ParsedElf` |

## Patchelf/Elf/Reader.lean

| Line | Kind | Name | Signature |
|---|---|---|---|
| 11 | def | `readU8` | `(bs : ByteArray) (off : Nat) -> UInt8` |
| 16 | theorem | `readU8_eq_getElem` | `readU8 bs i = bs[i]'h` |
| 21 | def | `readU16` | `(bs : ByteArray) (off : Nat) -> UInt16` (little-endian) |
| 27 | def | `readU32` | `(bs : ByteArray) (off : Nat) -> UInt32` |
| 35 | def | `readU64` | `(bs : ByteArray) (off : Nat) -> UInt64` |
| 42 | def | `readBytes` | `(bs : ByteArray) (off len : Nat) -> ByteArray` |
| 46 | theorem | `readBytes_size` | size of readBytes ≤ len, etc. |

## Patchelf/Elf/SectionOps.lean

| Line | Kind | Name | Signature |
|---|---|---|---|
| 24 | def | `ElfFile.updateSectionContent` | `(e : ElfFile) (i : Nat) (h : i < e.sections.size) (c : SectionContent) -> ElfFile` |
| 31 | `@[simp]` theorem | `ElfFile.updateSectionContent_header` | header preserved |
| 37 | `@[simp]` theorem | `ElfFile.updateSectionContent_phdrs` | phdrs preserved |
| 43 | `@[simp]` theorem | `ElfFile.updateSectionContent_sections_size` | size preserved |

## Patchelf/Elf/Serialize.lean

| Line | Kind | Name | Signature |
|---|---|---|---|
| 29 | def | `writeArray` | `{α} (f : α -> ByteArray) (arr : Array α) -> ByteArray` |
| 34 | theorem | `writeArray_size_of_uniform` | uniform-width size lemma |

## Patchelf/Elf/Splice.lean

| Line | Kind | Name | Signature |
|---|---|---|---|
| 13 | def | `splice` | `(bs : ByteArray) (off : Nat) (w : ByteArray) -> ByteArray` |
| 18 | `@[simp]` theorem | `splice_size` | `(splice bs off w).size = bs.size` (under bounds) |
| 34 | theorem (private) | `splice_getElem_outside` | element outside splice region preserved |
| 75 | theorem | `readU8_splice_disjoint` | disjoint readU8 preserved |
| 89 | theorem | `readU16_splice_disjoint` | analogue |
| 104 | theorem | `readU32_splice_disjoint` | analogue |
| 115 | theorem | `readU64_splice_disjoint` | analogue |
| 134 | theorem (private) | `extract_zero_zero` | `bs.extract 0 0 = empty` |
| 141 | theorem (private) | `splice_at_0_getElem` | element of splice at 0 |
| 168 | theorem (private) | `splice_at_off_getElem` | element of splice at general off |
| 199 | theorem | `readU8_splice_at_0_inside` | inside-splice readU8 = w[i] |
| 215 | theorem | `readU8_splice_at_off_inside` | inside-splice at off |
| 226 | theorem | `readU16_splice_at_off_inside` | analogue |
| 236 | theorem | `readU32_splice_at_off_inside` | analogue |
| 250 | theorem | `readU64_splice_at_off_inside` | analogue |
| 260 | theorem | `readU16_splice_at_0_inside` | analogue |
| 268 | theorem | `readU32_splice_at_0_inside` | analogue |
| 275 | theorem | `readU64_splice_at_0_inside` | analogue |

## Patchelf/Elf/StringSection.lean

| Line | Kind | Name | Signature |
|---|---|---|---|
| 30 | structure | `StringSection` | `bytes : ByteArray, wf : NoNullBytes ... ∧ ...` (typed null-terminated table) |
| 39 | `@[simp]` def | `size` | `(ss : StringSection) -> Nat := ss.bytes.size` |
| 43 | `@[simp]` def | `toTable` | `(ss : StringSection) -> StringTable` |
| 46 | def | `empty` | `StringSection` (empty literal) |
| 52 | def | `lookup` | `(ss : StringSection) (offset : Fin ss.size) -> Option ByteArray` |
| 59 | def | `findOffsetOf` | `(ss : StringSection) (target : ByteArray) -> Option (Fin ss.size)` |
| 77 | def | `append` | `(ss : StringSection) (s : String) -> StringSection x Nat` |
| 89 | `@[simp]` theorem | `append_size` | size after append |
| 109 | def | `SizeLE` | `(ss ss' : StringSection) -> Prop := ss.size ≤ ss'.size` |
| 112 | theorem | `size_le_append` | append yields larger section |
| 120 | def | `rebase` | `(ss ss' : StringSection) (h : SizeLE ss ss') (off : Fin ss.size) -> Fin ss'.size` |
| 126 | def | `rebaseAfterAppend` | combined rebase helper |
| 136 | def | `appendOffset` | `(ss : StringSection) (s : String) -> Fin (ss.append s).1.size` |
| 142 | theorem | `append_lookup` | post-append lookup of appended string |

## Patchelf/Elf/SymbolSection.lean

| Line | Kind | Name | Signature |
|---|---|---|---|
| 19 | structure | `TypedSymbol (ds : StringSection)` | st_name : Fin ds.size + other Symbol fields |
| 30 | structure | `SymbolSection (ds : StringSection)` | `symbols : Array (TypedSymbol ds)` |
| 37 | def | `rebase` | `{ds ds'} (h : SizeLE ds ds') -> SymbolSection ds -> SymbolSection ds'` |
| 43 | def | `renameAt` | `{ds} (s : SymbolSection ds) (i : Nat) (off : Fin ds.size) -> SymbolSection ds` |
| 51 | `@[simp]` theorem | `rebase_size` | size preserved |
| 56 | `@[simp]` theorem | `renameAt_size` | size preserved |

## Patchelf/Elf/ValidElfFile.lean

| Line | Kind | Name | Signature |
|---|---|---|---|
| 48 | structure | `ValidElfFile` | header, phdrs, dynstr (typed), dynsym/dynamic/versym/verneed/sysvHash/gnuHash/interp (Options) |
| 94 | def | `growDynstr` | `(e : ValidElfFile) (s : String) -> ValidElfFile x Fin (e.dynstr.append s).1.size` |
| 112 | def | `setInterp` | `(e : ValidElfFile) (path : String) -> ValidElfFile` |
| 116 | def | `setOsAbi` | `(e : ValidElfFile) (abi : OsAbi) -> ValidElfFile` |

## Patchelf/Elf/Writer.lean

| Line | Kind | Name | Signature |
|---|---|---|---|
| 13 | def | `writeU8` | `UInt8 -> ByteArray` |
| 17 | def | `writeU16` | `UInt16 -> ByteArray` (LE) |
| 23 | def | `writeU32` | `UInt32 -> ByteArray` |
| 31 | def | `writeU64` | `UInt64 -> ByteArray` |

## Patchelf/Elf/Ops/AddDebugTag.lean

| Line | Kind | Name | Signature |
|---|---|---|---|
| 13 | def | `addDebugTag` | `(e : ValidElfFile) (_h : e.dynamic.isSome) -> ValidElfFile` |
| 19 | theorem | `addDebugTag_observable` | result has debugTag = true |
| 29 | theorem | `addDebugTag_idempotent_value` | applying twice = once |
| 39 | theorem | `addDebugTag_insert_value` | inserts DT_DEBUG entry |

## Patchelf/Elf/Ops/AddNeeded.lean

| Line | Kind | Name | Signature |
|---|---|---|---|
| 18 | def | `addNeeded` | `(e : ValidElfFile) (lib : String) (_h : e.dynamic.isSome) -> ValidElfFile` |
| 25 | theorem | `addNeeded_observable` | resulting needed list contains lib |

## Patchelf/Elf/Ops/AddRpathEntry.lean

| Line | Kind | Name | Signature |
|---|---|---|---|
| 18 | def | `addRpathEntry` | `(e : ValidElfFile) (forceRpath : Bool) (newRpath : String) (_h : ...) -> ValidElfFile` |
| 24 | theorem | `addRpathEntry_rpath_observable` | RPATH path observed |
| 37 | theorem | `addRpathEntry_runpath_observable` | RUNPATH path observed |

## Patchelf/Elf/Ops/ClearSymbolVersion.lean

| Line | Kind | Name | Signature |
|---|---|---|---|
| 35 | def | `VER_NDX_GLOBAL` | `UInt16 := 1` |
| 41 | structure | `ClearSymbolVersionOk` | precondition bundle (versym.isSome, dynsym.isSome, sym exists) |
| 55 | def | `clearVersymEntries` | array transformer that sets entries to VER_NDX_GLOBAL |
| 68 | `@[simp]` theorem | `clearVersymEntries_size` | size preserved |
| 76 | theorem | `clearVersymEntries_getElem` | per-index value (VER_NDX_GLOBAL or original) |
| 96 | def | `clearSymbolVersion` | `(e : ValidElfFile) (symName : String) (h : ClearSymbolVersionOk e) -> ValidElfFile` |
| 106 | `@[simp]` theorem | `clearSymbolVersion_versym_isSome` | versym still present |
| 119 | theorem | `clearSymbolVersion_cleared` | matching symbol indices cleared |
| 145 | theorem | `clearSymbolVersion_preserved` | non-matching indices preserved |
| 182/185/188/191/194 | `@[simp]` theorems | `clearSymbolVersion_dynstr/dynsym/dynamic/header/phdrs` | unrelated fields preserved |
| 199 | theorem | `clearSymbolVersion_versym_size` | versym array size preserved |

## Patchelf/Elf/Ops/Execstack.lean

| Line | Kind | Name | Signature |
|---|---|---|---|
| 19 | def | `PF_X` | `UInt32 := 0x1` |
| 22 | inductive | `ExecstackMode` | `\| set \| clear` |
| 26 | def | `modifyExecstack` | `(e : ValidElfFile) (mode : ExecstackMode) -> ValidElfFile` |
| 36/38/40/43 | `@[simp]` theorems | `modifyExecstack_dynstr/dynamic/header/phdrs_size` | non-phdr fields preserved |

## Patchelf/Elf/Ops/Interpreter.lean

| Line | Kind | Name | Signature |
|---|---|---|---|
| 20 | def | `setInterpreter` | `(e : ValidElfFile) (newPath : String) -> ValidElfFile` |
| 33 | `@[simp]` theorem | `setInterpreter_interp` | new interp = ofString path |
| 36 | `@[simp]` theorem | `setInterpreter_dynstr` | dynstr preserved |
| 38 | `@[simp]` theorem | `setInterpreter_dynamic` | dynamic preserved |
| 44 | theorem | `setInterpreter_pt_interp_filesz` | PT_INTERP filesz updated |

## Patchelf/Elf/Ops/NoDefaultLib.lean

| Line | Kind | Name | Signature |
|---|---|---|---|
| 13 | def | `DF_1_NODEFLIB` | `UInt64 := 0x800` |
| 16 | def | `noDefaultLib` | `(e : ValidElfFile) (_h : e.dynamic.isSome) -> ValidElfFile` |
| 22 | theorem (private) | `or_and_same` | `(x \|\|\| y) &&& y = y` |
| 26 | theorem | `noDefaultLib_observable` | flags1 has DF_1_NODEFLIB bit |
| 42 | theorem | `noDefaultLib_insert_value` | inserts DT_FLAGS_1 if absent |
| 55 | theorem | `noDefaultLib_mutate_value` | mutates DT_FLAGS_1 if present |

## Patchelf/Elf/Ops/OsAbi.lean

| Line | Kind | Name | Signature |
|---|---|---|---|
| 17 | `@[inline]` def | `setOsAbi` | `(e : ValidElfFile) (abi : OsAbi) -> ValidElfFile` |
| 22 | `@[simp]` theorem | `setOsAbi_observable` | header.ident.osAbi = abi |
| 25/27/29 | `@[simp]` theorems | `setOsAbi_dynstr/dynamic/phdrs` | unrelated fields preserved |

## Patchelf/Elf/Ops/RemoveNeeded.lean

| Line | Kind | Name | Signature |
|---|---|---|---|
| 15 | def | `removeNeeded` | `(e : ValidElfFile) (libToRemove : String) (_h : e.dynamic.isSome) -> ValidElfFile` |
| 22 | theorem | `removeNeeded_observable` | result.needed.lookup libToRemove = none |

## Patchelf/Elf/Ops/RemoveRPath.lean

| Line | Kind | Name | Signature |
|---|---|---|---|
| 13 | def | `removeRpath` | `(e : ValidElfFile) (_h : e.dynamic.isSome) -> ValidElfFile` |
| 18 | theorem | `removeRpath_observable` | rpath = none, runpath = none |

## Patchelf/Elf/Ops/RenameDynamicSymbols.lean

| Line | Kind | Name | Signature |
|---|---|---|---|
| 24 | structure | `RenameDynamicSymbolsOk` | precondition bundle |
| 30 | def | `rebuildSysVHash` | `(ht : SysVHashTable) (ds : StringSection) -> SysVHashTable` |
| 61 | def | `renameTypedSymbol` | `{ds} (oldName : String) (off : Fin ds.size) -> ...` |
| 68 | def | `SymbolSection.rename` | `{ds} (ss : SymbolSection ds) (oldName : String) (off : Fin ds.size) -> SymbolSection ds` |
| 78 | def | `renameDynamicSymbols` | `(e : ValidElfFile) (oldName newName : String) (h : RenameDynamicSymbolsOk e newName) -> ValidElfFile` |
| 93 | theorem | `renameDynamicSymbols_dynstr` | dynstr extended with newName |
| 100 | theorem | `renameDynamicSymbols_dynsym_isSome` | dynsym preserved |
| 109 | theorem | `renameDynamicSymbols_gnuHash` | gnuHash preserved/rebuilt |
| 123 | theorem | `renameDynamicSymbols_observable` | symbol-name observation post-rename |

## Patchelf/Elf/Ops/ReplaceNeeded.lean

| Line | Kind | Name | Signature |
|---|---|---|---|
| 19 | def | `replaceNeededReuse` | reuse-existing-offset variant |
| 25 | def | `replaceNeeded` | `(e : ValidElfFile) (oldName newName : String) (_h : ...) -> ValidElfFile` |
| 32 | theorem | `replaceNeededReuse_observable` | reuse correctness |
| 49 | theorem | `replaceNeeded_observable_offset` | offset rewritten |

## Patchelf/Elf/Ops/Rpath.lean

| Line | Kind | Name | Signature |
|---|---|---|---|
| 15 | inductive | `RpathMode` | `\| set \| remove` |
| 19 | def | `modifyRPath` | `(e : ValidElfFile) (forceRpath : Bool) (mode : RpathMode) (newRpath : String) (_h : ...) -> ValidElfFile` |
| 28 | theorem | `modifyRPath_remove_observable` | remove correctness |
| 35 | theorem | `modifyRPath_set_rpath_observable` | set RPATH correctness |
| 48 | theorem | `modifyRPath_set_runpath_observable` | set RUNPATH correctness |

## Patchelf/Elf/Ops/Soname.lean

| Line | Kind | Name | Signature |
|---|---|---|---|
| 19 | inductive | `SonameMode` | `\| set \| remove` |
| 24 | def | `modifySoname` | `(e : ValidElfFile) (mode : SonameMode) (newName : String) (_h : ...) -> ValidElfFile` |
| 32 | theorem | `modifySoname_remove_observable` | soname = none |
| 38 | theorem | `modifySoname_set_observable` | soname = some name |

---

## Patchelf/Elf/OpAdapterPreservation.lean (§5.1 op-level Tier D)

Op→byte adapter preservation.  Tier-1 ops + the Tier-2/3 round-trip
scaffold + the three closed open-core obligations + the composed driver +
the two shrinking-op round-trips.  (Names only; see the file for full
signatures.)

| Kind | Name | What it gives |
|---|---|---|
| theorem | `isValid_of_phdrs_map` / `isLoadable_of_phdrs_map` | flags-only phdr map preserves IsValid/IsLoadable |
| theorem | `toElfFile_setOsAbi_{eq,sections,phdrs,preserves_valid,preserves_loadable}` | Tier-1 `setOsAbi` |
| theorem | `toElfFile_modifyExecstack_{eq,preserves_loadable}` | Tier-1 `modifyExecstack` |
| theorem | `encode_roundtrip_via_normalized` | scaffold spine: round-trip via normalized `en` |
| theorem | `spliceRegionsDisjoint_of_structural` / `_eo` | `en.spliceRegionsDisjoint` from 6 structural invariants on `syncDtStrszInFile eo` / on `eo` (§1.3a) |
| theorem | `encodePreconditions_of_layoutNormalized` | Obligation C: full `EncodePreconditions en` (A + scaffold + 4 eo-derived fields + 4 position-bound hyps) |
| theorem | `tierD_roundtrip` / `_of_valid` / `_of_eo_facts` | composed A+B+C drivers; `_of_eo_facts` states its entire surface on `eo` |
| theorem | `toElfFile_removeRpath_tierD_roundtrip` | full Tier-D round-trip for `removeRpath` |
| theorem | `toElfFile_removeNeeded_tierD_roundtrip` | full Tier-D round-trip for `removeNeeded` |

`encodePreconditions_of_layoutNormalized` derives 4 of its 8 residual
fields (`identValid`/`sizeFit`/`nullEmpty`/`headerFit_entry`) from the
matching facts on `eo`; only the 4 position-bound families
(`headerFit_phoff`/`shoff`, `phdrFit`, `shdrFit`) remain hypotheses.

Reusable shrink-monotonicity core (`SectionOps.lean`, op-independent):
`updateSectionContent_{headerPhdr,headerShdr,phdrShdr,headerSection,
phdrSection,shdrSection}Disjoint_shrink` + `_section0Null` +
`IntervalDisjoint_shrink_right` — a `.dynamic`-rewrite with
`newDyn.size ≤ oldDyn.size` preserves all 6 disjointness clauses +
section-0-NULL.  Plus the 3 added `syncDtStrszInFile_{headerShdr,phdrShdr,
shdrSection}Disjoint` lemmas (`Encoder.lean`) completing the
first-pre-pass transport.

Supporting §5.1 lemmas live in their home modules:
- Obligation A establishment/preservation in `Encoder.lean`
  (`syncDtStrszInFile_establishes_dynStrszCoherent`,
  `prepLayout_syncDtStrsz_dynStrszCoherent`) + `GrowEOF.lean`
  (`growEOFWith_dynamic`, `syncDtAddrTagsInFile_preserves_dynStrszCoherent`,
  `syncDtAddrEntry_eq_self_of_not_addressTag`).
- Obligation A/B capstones (`syncOk_of_normalized`, `renormalize_eq_self`,
  `encode_eq_encode_normalized`) in `ByteRoundtrip.lean`; validity capstone
  (`prepLayout_syncDtStrsz_preserves_valid`) + Obligation B helpers in
  `Encoder.lean`.
- Content-preservation getElem-dispatch (Obligation C residual derivation):
  `growEOFWith_sections_{map_content,content,shdrSize,type}` + per-branch
  `_sections_map_content` (`GrowEOF.lean`); pipeline
  `prepLayout_syncDtStrsz_sections_{shdrSize,type}` + `_header_{ident,entry}`
  (`Encoder.lean`); `{identValid,sizeFit,nullEmpty,headerFit_entry}_normalized_of_eo`
  + `identBytesValid_of_ident_eq` (`ByteRoundtrip.lean`).

---

## Patchelf/Elf/OpToElfFactor.lean (§5.1 op-through-toElfFile factoring)

Op-output structural-invariant DERIVATION (criterion 2), generic over
`mapDynamicOp f`.  Factors `toElfFile template (mapDynamicOp typed f)` as a single
`.dynamic`-shrink `updateSectionContent` on the no-op output and transports the
structural invariants; `removeRpath` / `modifyRPath.remove` / `removeNeeded`
instantiate it.  (Names only; see the file for full signatures.)

| Kind | Name | What it gives |
|---|---|---|
| theorem | `ElfFile.updateSectionContent_{comm,set_set}` | distinct-index commutation / same-index last-wins (getElem-characterization, no `Array.set` motive wall) |
| theorem | `ElfFile.getElem_content_congr{,_sections}` / `updateSectionContent_content_self` | content-projection congruences past the dependent bound |
| theorem | `ElfFile.{type_at_dynamicIdx,findUniqueTypeIdx_ne_dynamicIdx,updateSectionContent_dynamic_findUniqueTypeIdx,updateSectionContent_findUniqueTypeIdx_both_ne}` | dynamic-index facts for the commutation obligations |
| theorem | `applyOpt_{updateSectionContent_dynamic_comm,dynamicIdx,content_at_ne,sections_size}` | the `applyOpt` commutation/preservation primitives |
| theorem | `applyTypeOpt_{dynamic_comm,dynamicIdx,content_at}` | generic type-based outer-apply lemmas (ty ≠ SHT_DYNAMIC) — collapse the 4× versym/sysv/gnu/verneed duplication |
| theorem | `apply{Versym,SysvHash,GnuHash,Verneed}_{dynamic_comm,dynamicIdx,content_at,sections_size}` | thin per-type wrappers over the `applyTypeOpt_*` generics (names kept for call sites) |
| theorem | `apply{Interp,Dynamic}_*` | interp (name-based, parameterized on interp-vs-dynamic distinctness) + applyDynamic idx/content/size |
| theorem | `outerChain_dynamic_comm` | the whole `applyVersym…applyInterp` suffix commutes with the dynamic update (3 intermediate idx facts derived internally from `hIdxV`) |
| theorem | `ElfFile.with_header_phdrs_updateSectionContent` / `updateSectionContent_sections_eq_of_sections` | the header/phdrs override commutes; sections depend only on input sections |
| theorem | `applyDynamic_factor_general` / `innerChain_factor_general` / `toElfFile_mapDynamicOp_factor` | the factoring `eo = (toElfFile template typed).updateSectionContent iDyn (.dynamic (patch bd (f td)))`, generic over `f` |
| theorem | `toElfFile_content_at_dynamicIdx` | no-op output content at iDyn = `.dynamic (patchDynamicEntries (template bytes) typed.dynamic)` (calc/`.trans`, not `rw` — giant-term whnf timeout) |
| structure | `RemoveRpathFactorData` | per-op witnesses (prefix dynamic idx/content + interp distinctness); `f`-agnostic (all fields describe the no-op chain) — name kept for the regression-gated capstone |
| theorem | `mapDynamicOp_structural_transport` | the 6 disjointness invariants + section-0-NULL on `eo`, DERIVED from the no-op output's via the shrink core, taking the per-`f` `hSizeBound` |
| theorem | `toElfFile_mapDynamicOp_tierD_roundtrip_derived` | **generic capstone**: full byte round-trip, op-output structural invariants derived, parameterized on `f` + `hSizeBound` |
| theorem | `removeRpath_structural_transport` / `toElfFile_removeRpath_tierD_roundtrip_derived` | `removeRpath` instantiation (`f := ·.stripRpath`) — the §5.1 regression gate; statement + axioms unchanged |
| theorem | `toElfFile_modifyRPath_remove_tierD_roundtrip_derived` | `modifyRPath.remove` instantiation (same `f`, free) |
| theorem | `toElfFile_removeNeeded_tierD_roundtrip_derived` | `removeNeeded` instantiation (`f := ·.filterNeededBy lib.toUTF8`) |

Per-`f` relative size bounds + the compositional `patchDynamicEntries` machinery
live in `Adapter.lean`: `patchDynamicEntries_stripRpath_size_le` (`ShrinkRel` +
`tail_shrink_rpath`) and `patchDynamicEntries_filterNeededBy_size_le` (the
`NeededRel` potential function + `appendSurplusNeeded_size_exact` +
`patchStep_filterNeeded`/`loop_filterNeeded`/`tail_filterNeeded`), both over the
`PatchState`/`patchStep`/`patchInit`/`appendSurplusNeeded`/`appendUnless` +
`Array.foldl_rel` core.

---

## Summary statistics

- **Files scanned:** 45 Lean files
- **`sorry` placeholders:** 0
- **`axiom` declarations:** 0
- **Master theorem:** `parse_encode_roundtrip` at `Elf/ByteRoundtrip.lean:2327`
- **Master precondition bundle:** `EncodePreconditions` at `Elf/ByteRoundtrip.lean:2208` (11 fields)
- **Master witness bundle:** `DecodeRoundtripWitness` at `Elf/ByteRoundtrip.lean:2162` (4 fields)
- **Layout-engine structural correctness:** `layoutForEncoding_produces_spliceRegionsDisjoint` at `Elf/LayoutEngine.lean:672`
- **Validity-predicate hierarchy:** `IsValid` (8 fields) → `IsLoadable` (extends + 4 fields) → `IsFullyValid` (extends + 1 field), all in `Elf/ElfFile.lean`
- **Splice-region disjointness:** `spliceRegionsDisjoint` (7 fields), built from `IntervalDisjoint` primitive in `Elf/ElfFile.lean`
- **Op layer:** 14 ops in `Elf/Ops/`, each with a `def` + 1–6 observable/preservation theorems
- **DSL-emitted boilerplate:** the `elf_schema` macro in `Elf/SchemaDSL.lean` (~1215 LOC) auto-generates `<T>.write`, `<T>.decode`, `<T>_decode_write`, `<T>_write_decode`, `ByteWidth <T>`, and array variants. These declarations are not visible to the simple grep pattern but are produced for `ElfIdent`, `ElfHeader`, `ProgramHeader`, `SectionHeader`, `DynEntry`, `Symbol`, `Vernaux`, etc., as invoked from `Elf/Schemas.lean`.
- **Verification chain:** parser preconditions (`encodePreconditions_of_parser`) → master roundtrip (`parse_encode_roundtrip`); layout-engine produces the `spliceRegionsDisjoint` clause structurally.

Key architectural file paths:
- Type-level invariants: `/Users/cbaker2/ext-sources/patchelf/lean/Patchelf/Elf/ElfFile.lean`, `/Users/cbaker2/ext-sources/patchelf/lean/Patchelf/Elf/ValidElfFile.lean`
- Master verification: `/Users/cbaker2/ext-sources/patchelf/lean/Patchelf/Elf/ByteRoundtrip.lean`
- Layout engine + structural invariants: `/Users/cbaker2/ext-sources/patchelf/lean/Patchelf/Elf/LayoutEngine.lean`
- Encoder: `/Users/cbaker2/ext-sources/patchelf/lean/Patchelf/Elf/Encoder.lean`
- DSL: `/Users/cbaker2/ext-sources/patchelf/lean/Patchelf/Elf/SchemaDSL.lean`
- CLI entry points: `/Users/cbaker2/ext-sources/patchelf/lean/Patchelf/Main.lean`, `/Users/cbaker2/ext-sources/patchelf/lean/Patchelf/CLI.lean`
