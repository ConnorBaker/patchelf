# Research-Doc Gap Catalog

> **ARCHIVED — superseded.** Written against the
> `lean/Patchelf/Spec/{Invariants,AntiRegressions,Validity}.lean`
> module layout that no longer exists.  Every `file:line`
> citation in this document is broken — that directory and its
> 38-field `IsValidELF` structure were retired with the move to
> the pure-IR + typed-section-algebra architecture.  The
> ELF-spec citations at the core of each gap entry (gABI
> sections, phdr/shdr invariants, loader behavior, etc.) remain
> factually accurate as reference material; the "Current Lean
> status" fields are all wrong.  Kept for historical record
> until a fresh gap catalog is written.

## Abstract

This document enumerates invariants, ABI requirements, bug classes, and
anti-regression patterns described in `research/00-overview.md` through
`research/05-edge-cases-and-gaps.md` that are either absent, weaker, or
only partially captured in `lean/Patchelf/Spec/{Invariants,AntiRegressions,Validity}.lean`.

## Caveats

- This catalog is the output of a single Explore-agent reading pass; entries have not been independently verified against the current Lean spec layer.
- Priority assignments (HIGH/MED/LOW) reflect one reviewer's judgment about whether a real ELF in the wild could trigger the issue. Some disagreements with the assigned priority are known — see Open Questions.
- Lean `file:line` citations point at a Spec/* directory layout that has since been retired (see archive banner above).  Treat all Lean citations in this document as historical; verify any claim against the current tree before use.
- Proposed Lean predicates use identifier names that may not exist in the project's current enumerations (e.g. `ELFOSABI_SYSV`, `EM_NONE`, `ET_LOOS`); these are suggestions, not literal code to copy.
- Resolved footnote definitions referenced by this catalog (`[^8]`, `[^21]`, etc.) live in the research documents being cited, not in this file.
- Subsystem counts vary across the document — the Summary Statistics section has rough counts; the Python-driven tally at the end of the Summary is authoritative.

## Table of contents

- [A. Header & Ident](#a-header--ident) — 10 gaps
- [B. Program Headers & Segments](#b-program-headers--segments) — 16 gaps
- [C. Section Headers & Sections](#c-section-headers--sections) — 14 gaps
- [D. Dynamic Section](#d-dynamic-section) — 14 gaps
- [E. Symbol Tables](#e-symbol-tables) — 10 gaps
- [F. String Tables](#f-string-tables) — 3 gaps
- [G. Hash Tables](#g-hash-tables) — 8 gaps
- [H. Version Tables](#h-version-tables) — 3 gaps
- [I. Relocations](#i-relocations) — 5 gaps
- [J. Notes](#j-notes) — 8 gaps
- [K. Cross-Subsystem / File-Wide](#k-cross-subsystem--file-wide) — 18 gaps
- [L. Bug-Class Anti-Regressions](#l-bug-class-anti-regressions) — 15 gaps
- [Additional Cross-Cutting Gaps](#additional-cross-cutting-gaps-missed-by-prior-reviews) — 11 gaps

Total: 135 gaps.

---

## A. Header & Ident

**Gap 1: `EI_OSABI` is unconstrained, but IFUNC-processing tools inspect it**
- Source: `research/02-gnu-extensions.md` §Other Extensions (`ELFOSABI_GNU = 3`); `research/05-edge-cases-and-gaps.md` §GNU Indirect Functions footnote [^27a]
- Current Lean status: **ABSENT** — `IsValidHeader` (`Elf/Header.lean:102-113`) does not touch `ident.osabi`; no predicate references it
- Suggested Lean predicate: `def OsabiConsistentWithIfunc (elf) : Prop := (∃ s, s.symType = STT_GNU_IFUNC) → elf.header.ident.osabi ∈ {ELFOSABI_SYSV, ELFOSABI_GNU}`
- Priority: **LOW** (diagnostic only — glibc ignores osabi for IFUNC resolution)

**Gap 2: `EI_ABIVERSION` is not validated**
- Source: `research/02-gnu-extensions.md` §Other Extensions; gABI Ch. 4 ELF Header
- Current Lean status: **ABSENT**
- Suggested Lean predicate: `def AbiVersionZeroOrGnu (elf) : Prop := elf.header.ident.abiVersion = 0 ∨ elf.header.ident.osabi = ELFOSABI_GNU`
- Priority: **LOW**

**Gap 3: `e_version` vs `ei_version` dual-field equality**
- Source: `research/01-elf-specification.md` §ELF File Structure Overview; gABI "both `ei_version` and `e_version` shall hold `EV_CURRENT`"
- Current Lean status: **WEAKER** — `IsValidHeader` (line 103-105) checks each equals 1 but not their equality-to-each-other as a derived fact is only implicit
- Suggested Lean predicate: Strengthen `IsValidHeader` to include `h.ident.version.toNat = h.fileVersion.toNat`
- Priority: **LOW**

**Gap 4: `e_type` membership in the recognised enumeration**
- Source: `research/01-elf-specification.md` §ELF File Structure Overview (ET_NONE/ET_REL/ET_EXEC/ET_DYN/ET_CORE)
- Current Lean status: **ABSENT** — no predicate restricts `elf.header.fileType`
- Suggested Lean predicate: `def ValidFileType (h : ElfHeader) : Prop := h.fileType ∈ {ET_REL, ET_EXEC, ET_DYN, ET_CORE} ∨ (h.fileType ≥ ET_LOOS ∧ h.fileType ≤ ET_HIPROC)`
- Priority: **MED**

**Gap 5: `e_machine` validity / endianness (research doc flags FIXME)**
- Source: `research/04-patchelf-invariants.md` §Endianness in getElfType() [^24]
- Current Lean status: **ABSENT** — no invariant pins `e_machine` to the decoded endianness
- Suggested Lean predicate: blocked on providing an enumeration of valid `EM_*` values; at minimum `def MachineNonzeroForDynamic : ∃ pt ∈ elf.programHeaders, pt.type = PT_DYNAMIC → elf.header.machine ≠ EM_NONE`
- Priority: **MED** (FIXME in C++ source is a known fragility)

**Gap 6: `e_entry` must lie in an executable PT_LOAD for ET_EXEC / PIE**
- Source: gABI Ch. 4 ELF Header; `research/03-dynamic-linking.md` §PT_INTERP (AT_ENTRY transfer)
- Current Lean status: **ABSENT**
- Suggested Lean predicate: `def EntryPointInExecLoad (elf) : Prop := elf.header.fileType ∈ {ET_EXEC, ET_DYN-with-PT_INTERP} → ∃ ph ∈ elf.programHeaders, ph.type = PT_LOAD ∧ ph.flags.executable = true ∧ ph.vaddr ≤ elf.header.entry ∧ elf.header.entry < ph.vaddr + ph.memsz`
- Priority: **HIGH** (corrupted `e_entry` → immediate SIGSEGV on exec)

**Gap 7: `e_phoff`, `e_shoff` in-file-bounds**
- Source: `research/01-elf-specification.md` §ELF File Structure Overview
- Current Lean status: **ABSENT** at the `ElfFile` level (the record doesn't retain a single monolithic byte buffer)
- Suggested Lean predicate: blocked on re-threading a file-size field; statable as `elf.header.phoff ≤ totalFileSize ∧ elf.header.phoff + elf.header.phnum * elf.header.phentsize ≤ totalFileSize`
- Priority: **MED**

**Gap 8: PN_XNUM sentinel handling**
- Source: `research/05-edge-cases-and-gaps.md` §PN_XNUM — Extended Program Header Count [^21][^22]
- Current Lean status: **WEAKER** — `ParseError.pnXnumNotSupported` exists (`Validity.lean:123`) and a comment sits in `Elf/Header.lean:110-113`, but no invariant asserts that a loaded ElfFile has `phnum ≠ 0xFFFF` or provides the overflow-via-sh_info path
- Suggested Lean predicate: `def PhnumNotSentinel (h : ElfHeader) : Prop := h.phnum.toNat ≠ 0xFFFF` as a precondition for the `phnum_matches_size` invariant to be meaningful
- Priority: **MED** (rare in-wild; core dumps trigger it)

**Gap 9: `e_shnum = 0` / `e_shstrndx = SHN_XINDEX` overflow**
- Source: `research/05-edge-cases-and-gaps.md` §PN_XNUM (shnum and shstrndx overflow go to `sh_size` / `sh_link` of sh[0])
- Current Lean status: **ABSENT**
- Suggested Lean predicate: `def ShnumNotOverflowSentinel (h : ElfHeader) : Prop := h.shnum.toNat ≠ 0 ∧ h.shstrndx.toNat ≠ 0xFFFF`
- Priority: **LOW**

**Gap 10: `e_ehsize`, `e_phentsize`, `e_shentsize` match ELFCLASS**
- Source: `research/01-elf-specification.md` §ELF File Structure Overview
- Current Lean status: **EQUIVALENT** — `IsValidHeader` lines 106-108 check all three against `expectedEhsize/Phentsize/Shentsize`
- (no gap; included for accounting)

---

## B. Program Headers & Segments

**Gap 11: PT_INTERP at most one, preceding any PT_LOAD**
- Source: `research/03-dynamic-linking.md` §PT_INTERP (lines 105-107)
- Current Lean status: **ABSENT** — no ordering or cardinality invariant for PT_INTERP
- Suggested Lean predicate: `def PtInterpOrdering (elf) : Prop := (AtMostOne phdrs PT_INTERP) ∧ ∀ i j, phdrs[i].type = PT_INTERP → phdrs[j].type = PT_LOAD → i < j`
- Priority: **HIGH** (kernel scans in order; misordering is loader-detectable)

**Gap 12: PT_PHDR at most one**
- Source: `research/04-patchelf-invariants.md` §Section/Segment Synchronization [^8]
- Current Lean status: **WEAKER** — `PtPhdrSelfConsistent` (`Invariants.lean:229-233`) constrains fields when present but a second PT_PHDR passes both clauses independently
- Suggested Lean predicate: add `AtMostOneProgramHeader elf SegmentType.PT_PHDR` clause
- Priority: **MED**

**Gap 13: PT_PHDR must precede any PT_LOAD**
- Source: `research/03-dynamic-linking.md` §PT_PHDR (constraints, line 120)
- Current Lean status: **ABSENT**
- Suggested Lean predicate: `∀ i j, phdrs[i].type = PT_PHDR → phdrs[j].type = PT_LOAD → i < j`
- Priority: **MED**

**Gap 14: PT_PHDR only present if PHT is in memory image (covered by a PT_LOAD)**
- Source: `research/03-dynamic-linking.md` §PT_PHDR; `research/04-patchelf-invariants.md` line 69-70 and [^9]
- Current Lean status: **ABSENT** — `MetadataSegmentsContainedInPtLoad` covers PT_DYNAMIC/PT_NOTE/PT_GNU_RELRO but not PT_PHDR
- Suggested Lean predicate: extend `MetadataSegmentsContainedInPtLoad` to include PT_PHDR
- Priority: **HIGH**

**Gap 15: Program header table fully covered by a PT_LOAD**
- Source: `research/04-patchelf-invariants.md` lines 69-70 (`rewriteHeaders` ensures this)
- Current Lean status: **PARTIAL** — covered only indirectly via PT_PHDR containment when PT_PHDR is present; if PT_PHDR is absent the PHT may not be mapped
- Suggested Lean predicate: `def PhtCoveredByPtLoad (elf) : Prop := ∃ ph ∈ elf.programHeaders, ph.type = PT_LOAD ∧ ph.offset ≤ elf.header.phoff ∧ elf.header.phoff + elf.header.phnum*elf.header.phentsize ≤ ph.offset + ph.filesz`
- Priority: **HIGH**

**Gap 16: `p_align` is a power of 2 (or 0/1)**
- Source: gABI Ch. 5 Program Header — "Values 0 and 1 mean no alignment is required. Otherwise, p_align should be a positive, integral power of 2"
- Current Lean status: **ABSENT**
- Suggested Lean predicate: `def PtAlignPowerOfTwo (ph) : Prop := ph.align = 0 ∨ ph.align = 1 ∨ ∃ k, ph.align = 2^k`
- Priority: **LOW**

**Gap 17: `p_align` congruence sanity under shiftFile correction**
- Source: `research/04-patchelf-invariants.md` §Page Alignment [^6] — shiftFile may rewrite `p_align` to page size when congruence breaks
- Current Lean status: **PARTIAL** — `IsPtLoadAligned` captures the congruence but not that corrections must set `p_align = pageSize`
- Suggested Lean predicate: post-condition on `shiftFile`-style ops: `∀ ph in result.programHeaders, ph.type = PT_LOAD → ph.align ≥ getPageSize elf`
- Priority: **MED**

**Gap 18: New PT_LOAD from shiftFile gets hardcoded PF_R|PF_W (known risk)**
- Source: `research/04-patchelf-invariants.md` §shiftFile() point 5 (lines 234-239); risk: original RO replaced with RW
- Current Lean status: **ABSENT** — no anti-regression captures this
- Suggested Lean predicate: `theorem shiftFile_preserves_segment_permissions : ∀ original new, new ∈ mappedTo(original) → new.flags = original.flags`
- Priority: **HIGH** (changes memory-protection semantics silently)

**Gap 19: PT_GNU_STACK kernel "last-wins" convention**
- Source: `research/02-gnu-extensions.md` §PT_GNU_STACK [^5][^5a]
- Current Lean status: **ABSENT**
- Suggested Lean predicate: Either assert `AtMostOne phdrs PT_GNU_STACK` (stricter than kernel requires), or formalise the semantics as "the effective flags are from the last entry"
- Priority: **MED**

**Gap 20: PT_GNU_PROPERTY kernel "last-wins with interpreter priority"**
- Source: `research/02-gnu-extensions.md` §PT_GNU_PROPERTY [^10a]
- Current Lean status: **ABSENT**
- Suggested Lean predicate: `def PtGnuPropertyAtMostOne : AtMostOne phdrs PT_GNU_PROPERTY` (tighter than kernel, easier to reason about)
- Priority: **LOW**

**Gap 21: PT_TLS segment handling (TLS risks)**
- Source: `research/05-edge-cases-and-gaps.md` §Thread-Local Storage (TLS) [^28][^29][^30]
- Current Lean status: **ABSENT** — no invariant or op-blocker references PT_TLS
- Suggested Lean predicate: add `hasPtTls : Bool` helper and op-precondition `¬ elf.hasPtTls ∨ ¬ opMovesLoadSegments` (analogous to the RELR gate)
- Priority: **HIGH** (TLS-using libraries are ubiquitous; Local Exec offsets cannot be rewritten)

**Gap 22: Empty PT_NOTE segments (backward-compat skip path)**
- Source: `research/04-patchelf-invariants.md` §normalizeNoteSegments() [^34]
- Current Lean status: **ABSENT** — no predicate handles `ph.type = PT_NOTE ∧ ph.filesz = 0`
- Suggested Lean predicate: `def NoteSegmentNonemptyOrBenign (elf) : Prop := ∀ ph ∈ elf.programHeaders, ph.type = PT_NOTE → ph.filesz > 0 ∨ skipLegacyEmpty`
- Priority: **LOW**

**Gap 23: Only one PT_LOAD may straddle shiftFile's insertion point**
- Source: `research/04-patchelf-invariants.md` §Hardcoded Assumptions [^27] ("Single split point in shiftFile()")
- Current Lean status: **ABSENT** — C++ asserts this; Lean has no corresponding obligation
- Suggested Lean predicate: precondition for `shiftFile`-style op: `AtMostOne { ph | ph.type = PT_LOAD ∧ ph.offset < startOffset < ph.offset + ph.filesz }`
- Priority: **MED**

**Gap 24: PT_LOAD `p_memsz > p_filesz` only (BSS invariant specifically PT_LOAD)**
- Source: `research/03-dynamic-linking.md` §BSS Handling (lines 72-77)
- Current Lean status: **EQUIVALENT** — `PtLoadFileszMemsz` (`Invariants.lean:49-51`) captures this exactly
- (no gap; included for accounting)

**Gap 25: PT_LOAD in-memory non-overlap (vaddr ranges disjoint)**
- Source: implicit from gABI ascending vaddr ordering + practical loader behaviour
- Current Lean status: **PARTIAL** — `LoadableSegmentFileOffsetNonOverlap` (line 244-255) covers file offsets only; vaddr overlap is not forbidden
- Suggested Lean predicate: analogous `LoadableSegmentVaddrNonOverlap` (for `p_vaddr, p_memsz`)
- Priority: **HIGH**

**Gap 26: p_paddr reserved/mirrored for applications**
- Source: `research/03-dynamic-linking.md` table of PT_LOAD fields (p_paddr "reserved, unused for applications")
- Current Lean status: **ABSENT**
- Suggested Lean predicate: `∀ ph, ph.type = PT_LOAD → ph.paddr = ph.vaddr` (common practice) OR no constraint; document the non-load of the physical addr field
- Priority: **LOW**

---

## C. Section Headers & Sections

**Gap 27: Section 0 is SHT_NULL (beyond just type)**
- Source: gABI Ch. 4 Sections — "The first entry of a section header table [...] is reserved. [...] its type is SHT_NULL"
- Current Lean status: **EQUIVALENT** — `section0IsNull` in `IsValidELF` captures the type; however the full sh[0] zero-fields specification (zero name, zero flags, zero addr, zero offset, zero link, zero info, zero addralign, zero entsize) is not asserted
- Suggested Lean predicate: Strengthen to `∀ h, sectionHeaders[0] = SectionHeader.zero` except that `sh_info`, `sh_size`, `sh_link` may carry PN_XNUM overflow
- Priority: **MED**

**Gap 28: `.shstrtab` null-termination**
- Source: `research/04-patchelf-invariants.md` §String Table Null-Termination [^15]
- Current Lean status: **PARTIAL** — `StrtabNullTerminated` is defined but `IsValidELF.dynstrNullTerminated` only enforces it on `.dynstr`. `.shstrtab` is not checked, even though `shstrndxValid` locates it
- Suggested Lean predicate: add field `shstrtabNullTerminated : StrtabNullTerminated (sectionData[shstrndx] as StringTable)`
- Priority: **MED**

**Gap 29: `sh_offset` + `sh_size` within file bounds (for non-NOBITS)**
- Source: gABI Ch. 4 Sections
- Current Lean status: **ABSENT** at `ElfFile` level (file-size not retained)
- Suggested Lean predicate: blocked on retaining file-size; once retained: `∀ sh, sh.type ≠ SHT_NOBITS → sh.offset + sh.size ≤ fileSize`
- Priority: **MED**

**Gap 30: `sh_addralign` must be a power of 2**
- Source: gABI Ch. 4 Sections — sh_addralign "must be a positive, integral power of 2"
- Current Lean status: **ABSENT**
- Suggested Lean predicate: `def ShAddralignPowerOfTwo (sh) : Prop := sh.addralign = 0 ∨ ∃ k, sh.addralign = 2^k`
- Priority: **LOW**

**Gap 31: `sh_addr mod sh_addralign = 0` when SHF_ALLOC is set**
- Source: gABI Ch. 4 Sections "sh_addr ... shall be congruent to 0, modulo the value of sh_addralign"
- Current Lean status: **ABSENT**
- Suggested Lean predicate: `∀ sh, sh.flags.alloc → sh.addralign > 0 → sh.addr % sh.addralign = 0`
- Priority: **MED**

**Gap 32: Replaced-section alignment clamp (C++ sets sh_addralign = sectionAlignment)**
- Source: `research/04-patchelf-invariants.md` §Open Questions (line 346-347) — "`writeReplacedSections()` unconditionally sets `sh_addralign` to `sectionAlignment` for all replaced sections (line 709)"
- Current Lean status: **ABSENT** — this is itself a C++ latent bug the research flags
- Suggested Lean predicate: post-condition on any Op that replaces a section: `result.sh.addralign ≥ orig.sh.addralign`
- Priority: **MED** (potentially invalidates larger-aligned sections)

**Gap 33: `sh_link`/`sh_info` cross-reference preservation under section reorder**
- Source: `research/04-patchelf-invariants.md` §Section Header Cross-References [^14]
- Current Lean status: **PARTIAL** — `DynsymShLinkPointsToDynstr` and `HashShLinkPointsToDynsym` cover two specific cases; generic preservation is absent. SHT_REL/SHT_RELA `sh_info` (targeted-section index) is uncovered
- Suggested Lean predicate: add `RelShInfoPointsToTargetSection`, `DynamicShLinkPointsToDynstr`, `VerdefShLinkPointsToDynstr`, `VerneedShLinkPointsToDynstr` clauses
- Priority: **HIGH**

**Gap 34: `.dynamic` sh_link points to `.dynstr`**
- Source: gABI Ch. 5 Dynamic Section (sh_link holds the dynstr index)
- Current Lean status: **ABSENT** (only dynsym→dynstr is captured)
- Suggested Lean predicate: `def DynamicShLinkPointsToDynstr (elf) : Prop := match findSection ".dynamic", findSection ".dynstr" with | some di, some si => sectionHeaders[di].link.toNat = si | _ => True`
- Priority: **HIGH**

**Gap 35: Compressed sections (SHF_COMPRESSED) restrictions**
- Source: `research/05-edge-cases-and-gaps.md` §Compressed Sections [^23][^24][^25]
- Current Lean status: **ABSENT**
- Suggested Lean predicate: `def NoAllocCompressed (elf) : Prop := ∀ sh, sh.flags.compressed → ¬ sh.flags.alloc`; plus a decoder for `Elf_Chdr` + ZSTD/ZLIB algorithm validity
- Priority: **LOW** (patchelf never touches these; preservation-in-bytes is the current-spec story)

**Gap 36: SHT_NOBITS sections have zero bytes in sectionData**
- Source: gABI Ch. 4 "SHT_NOBITS: A section of this type occupies no space in the file but otherwise resembles SHT_PROGBITS"
- Current Lean status: **PARTIAL** — validity enforces `sectionDataSizeMatches` (sizes of arrays match) but not `sh.type = SHT_NOBITS → sectionData[i] = ByteArray.empty`
- Suggested Lean predicate: `def NobitsEmpty (elf) : Prop := ∀ i, sectionHeaders[i].type = SHT_NOBITS → sectionData[i].size = 0`
- Priority: **MED**

**Gap 37: Section-name uniqueness (soft)**
- Source: gABI Ch. 4 — names are not strictly required unique, but `findSection ".dynstr"` assumes uniqueness
- Current Lean status: **ABSENT** — `findSection` returns the first match; two sections named `.dynstr` silently lose the second
- Suggested Lean predicate: `def DistinctSectionNames (elf) : Prop := ∀ i j, i ≠ j → resolvedName i ≠ resolvedName j`
- Priority: **LOW**

**Gap 38: `sh_entsize` matches the encoded struct size for typed sections**
- Source: gABI Ch. 4 — e.g., SHT_SYMTAB entsize = sizeof(Elf_Sym)
- Current Lean status: **PARTIAL** — `DT_SYMENT_matches` covers the dynamic tag, but no invariant checks `sectionHeaders[dynsym].entsize` matches ELF-class sym size
- Suggested Lean predicate: `def ShEntsizeConsistent (elf) : Prop := ∀ sh, sh.type = SHT_DYNSYM → sh.entsize = symEntSize elf.header.ident.fileClass` and similar for SHT_RELA, SHT_REL, SHT_DYNAMIC, SHT_GNU_VERSYM
- Priority: **HIGH**

**Gap 39: Substring sharing in string tables (preservation)**
- Source: `research/03-dynamic-linking.md` §Open Questions — "The gABI spec permits substring sharing within string tables"
- Current Lean status: **ABSENT** — no predicate, and patchelf's RPATH-sharing detection (`research/04` [^38]) has no Lean counterpart
- Suggested Lean predicate: anti-regression: `∀ other DT-entry referencing the old string, the referenced bytes are unchanged after an RPATH replace`
- Priority: **MED**

**Gap 40: `.dynstr` index 0 is null byte**
- Source: `research/03-dynamic-linking.md` §String Tables — "Index 0 is always a null byte, representing the empty string"
- Current Lean status: **ABSENT** — `StrtabNullTerminated` covers the *last* byte but not byte[0]
- Suggested Lean predicate: `def StrtabFirstByteZero (st) : Prop := st.bytes.size = 0 ∨ st.bytes[0]? = some 0`
- Priority: **MED**

---

## D. Dynamic Section

**Gap 41: DT_NULL termination preserved in encoded bytes**
- Source: `research/03-dynamic-linking.md` §The .dynamic Section ("array is terminated by a DT_NULL entry")
- Current Lean status: **PARTIAL** — the Validity layer notes `Dynamic.entries` "terminator stripped"; no invariant asserts re-encoding re-appends DT_NULL
- Suggested Lean predicate: post-condition on `Ops.Write.write` that the encoded `.dynamic` ends with a DT_NULL entry
- Priority: **HIGH** (missing DT_NULL = UB in ld.so iteration)

**Gap 42: DT_PLTRELSZ consistency with SHT_REL/SHT_RELA for .plt**
- Source: `research/03-dynamic-linking.md` §Standard Tags (DT_PLTRELSZ = total PLT reloc bytes)
- Current Lean status: **ABSENT**
- Suggested Lean predicate: `def DT_PLTRELSZ_matches (elf) : Prop := match DT_PLTRELSZ, DT_JMPREL-target-section with | some v, some sh => v = sh.size | _ => True`
- Priority: **HIGH**

**Gap 43: DT_RELSZ / DT_RELAENT / DT_RELENT size/entsize consistency**
- Source: `research/03-dynamic-linking.md` §Standard Tags
- Current Lean status: **ABSENT**
- Suggested Lean predicate: `def DT_RELSZ_matches`, `def DT_RELASZ_matches`, `def DT_RELAENT_matches`, `def DT_RELENT_matches` (parallel to existing `DT_STRSZ_matches`)
- Priority: **HIGH**

**Gap 44: DT_PLTREL value ∈ {DT_REL, DT_RELA}**
- Source: `research/03-dynamic-linking.md` §Standard Tags ("Type of PLT relocations (DT_REL or DT_RELA)")
- Current Lean status: **ABSENT**
- Suggested Lean predicate: `def DT_PLTREL_valid (elf) : Prop := ∀ d ∈ dyn.entries, d.tag = DT_PLTREL → d.value ∈ {DT_REL.toNat, DT_RELA.toNat}`
- Priority: **MED**

**Gap 45: DT_RPATH superseded / paired with DT_RUNPATH**
- Source: `research/02-gnu-extensions.md` §DT_RUNPATH vs DT_RPATH (ignored when DT_RUNPATH present)
- Current Lean status: **PARTIAL** — `NoDuplicateSingletonDynTags` says each appears ≤1 times but does not forbid simultaneous presence
- Suggested Lean predicate: `def RpathRunpathNotBoth (elf) : Prop := (∃ d, d.tag = DT_RPATH) → (∀ d, d.tag ≠ DT_RUNPATH) ∨ ignoreRpathPromise`
- Priority: **MED** (patchelf's `--force-rpath` does produce both; real bug surface)

**Gap 46: DT_PREINIT_ARRAY valid only in executables**
- Source: `research/03-dynamic-linking.md` Standard Tags [^13a] ("processed only in an executable file; it is ignored if contained in a shared object")
- Current Lean status: **ABSENT**
- Suggested Lean predicate: `def DT_PREINIT_ARRAY_onlyExec (elf) : Prop := (∃ d, d.tag = DT_PREINIT_ARRAY) → elf.header.fileType = ET_EXEC ∨ hasPtInterp elf`
- Priority: **LOW**

**Gap 47: DT_INIT_ARRAY / DT_FINI_ARRAY / DT_PREINIT_ARRAY size consistency**
- Source: `research/03-dynamic-linking.md` §Standard Tags
- Current Lean status: **ABSENT**
- Suggested Lean predicate: `def DT_INIT_ARRAYSZ_matches (elf) : Prop := ...` and `DT_FINI_ARRAYSZ_matches`, `DT_PREINIT_ARRAYSZ_matches`
- Priority: **MED**

**Gap 48: DT_DEBUG uniqueness and opt-in**
- Source: `research/03-dynamic-linking.md` §Standard Tags (DT_DEBUG "value unspecified by ABI")
- Current Lean status: **PARTIAL** — `NoDuplicateSingletonDynTags` does not include `DT_DEBUG`
- Suggested Lean predicate: extend `NoDuplicateSingletonDynTags` to include `DT_DEBUG`
- Priority: **LOW**

**Gap 49: DT_TEXTREL ⇔ `DF_TEXTREL` in DT_FLAGS parity**
- Source: `research/03-dynamic-linking.md` Standard Tags + `DT_FLAGS (DF_*)`
- Current Lean status: **ABSENT**
- Suggested Lean predicate: `def DT_TEXTREL_matches_DF_TEXTREL (elf) : Prop := (∃ d, d.tag = DT_TEXTREL) ↔ hasDflag elf DF_TEXTREL`
- Priority: **LOW**

**Gap 50: DT_BIND_NOW ⇔ DF_BIND_NOW ⇔ DF_1_NOW cross-flag parity**
- Source: `research/02-gnu-extensions.md` §DT_FLAGS_1 and DF_1_* Flags [^34] ("both `DF_BIND_NOW` and `DF_1_NOW` trigger eager binding; some linkers set both")
- Current Lean status: **ABSENT**
- Suggested Lean predicate: `def BindNowFlagsConsistent (elf) : Prop := hasBindNow DT_BIND_NOW → hasBindNow DF_BIND_NOW ∧ hasBindNow DF_1_NOW` (one-way implication)
- Priority: **MED**

**Gap 51: DT_RELACOUNT / DT_RELCOUNT hint accuracy**
- Source: `research/02-gnu-extensions.md` §Open Questions ("Should patchelf update DT_RELACOUNT/DT_RELCOUNT when sections are moved?")
- Current Lean status: **ABSENT**
- Suggested Lean predicate: `def DT_RELACOUNT_matches (elf) : Prop := ∀ d, d.tag = DT_RELACOUNT → d.value = count-of-RELATIVE-in-rela-section`
- Priority: **MED**

**Gap 52: DT_SONAME coherence (the value is a valid offset into .dynstr)**
- Source: `research/03-dynamic-linking.md` Standard Tags (DT_SONAME d_val = strtab offset)
- Current Lean status: **ABSENT** — no general "DT_* string-offset is valid" predicate
- Suggested Lean predicate: `def DynamicStrOffsetsValid (elf) : Prop := ∀ d ∈ entries, d.tag ∈ {DT_NEEDED, DT_SONAME, DT_RPATH, DT_RUNPATH} → d.value.toNat < da.strtab.bytes.size ∧ da.strtab.bytes[d.value.toNat.pred]? ≠ some 0` (well-formed null-terminated string rooted at that offset)
- Priority: **HIGH** (directly cited in Issue #244, Issue #115)

**Gap 53: DT_HASH becoming optional in gABI v4.3**
- Source: `research/01-elf-specification.md` §Open Questions; `research/02-gnu-extensions.md` §Open Questions
- Current Lean status: **ABSENT** — no predicate enforces "at least one of DT_HASH/DT_GNU_HASH is present"
- Suggested Lean predicate: `def AtLeastOneHash (elf) : Prop := elf.dynArea = some da → da.hashSysv.isSome ∨ da.hashGnu.isSome`
- Priority: **LOW**

**Gap 54: DT_FLAGS_1 write path missing endianness conversion (bug)**
- Source: `research/04-patchelf-invariants.md` §Missing Endianness Conversion in noDefaultLib() [^28b]
- Current Lean status: **ABSENT** from anti-regressions — the Lean port presumably serialises via a proper encoder, but no theorem states this
- Suggested Lean predicate: `theorem noDefaultLib_endianness_correct : (noDefaultLib elf).encodedDynamic = swapIfNeeded elf.header.ident.dataEncoding (rawFlags ∪ DF_1_NODEFLIB)`
- Priority: **MED**

---

## E. Symbol Tables

**Gap 55: STT_GNU_IFUNC symbol-type preservation across rename**
- Source: `research/05-edge-cases-and-gaps.md` §GNU Indirect Functions [^26][^27]
- Current Lean status: **ABSENT**
- Suggested Lean predicate: `theorem renameSymbol_preserves_ifunc_type : ∀ old new, (renameSymbol elf old new).dynsym[i].symType = elf.dynsym[i].symType`
- Priority: **HIGH**

**Gap 56: IRELATIVE relocations' addends survive section moves**
- Source: `research/05-edge-cases-and-gaps.md` §GNU Indirect Functions (2nd bullet) — "`IRELATIVE` relocations [...] store the resolver's virtual address in the relocation addend; if patchelf moves the section containing the resolver [...] the addend becomes stale. Patchelf does not update `IRELATIVE` relocation addends"
- Current Lean status: **ABSENT**
- Suggested Lean predicate: op-precondition for any section-moving op: `¬ hasIrelative elf ∨ opDoesNotMoveIrelativeTargetSection`
- Priority: **HIGH**

**Gap 57: `st_value` updated for non-STT_SECTION symbols on section move (research flags as FIXME)**
- Source: `research/04-patchelf-invariants.md` §Incomplete Fixes [^23] and §Open Questions
- Current Lean status: **ABSENT** — no theorem forces `st_value` rewrite when sections move
- Suggested Lean predicate: `theorem section_move_preserves_st_value : ∀ s, resolveSymbolAddr s elf = resolveSymbolAddr s (moveSection elf)` (harder — blocked on a layout-aware semantics)
- Priority: **MED**

**Gap 58: Symbol `st_info` binding/type field well-formedness**
- Source: `research/03-dynamic-linking.md` §Symbol Tables (STB_LOCAL/GLOBAL/WEAK, STT_NOTYPE/OBJECT/FUNC/SECTION/FILE)
- Current Lean status: **ABSENT** — no enumeration validity
- Suggested Lean predicate: `def StInfoValid (s : Sym) : Prop := s.binding ∈ recognisedBindings ∧ s.symType ∈ recognisedTypes`
- Priority: **LOW**

**Gap 59: Symbol `st_shndx` SHN_ABS / SHN_COMMON / SHN_XINDEX handled**
- Source: gABI Ch. 4 Symbol Table (SHN_ABS, SHN_COMMON, SHN_XINDEX sentinels)
- Current Lean status: **PARTIAL** — `SymbolSectionIndicesInBounds` requires `regularIndexInBounds n`, implicitly allowing SHN_ABS/COMMON/UNDEF; SHN_XINDEX (→ `.symtab_shndx`) is unaddressed
- Suggested Lean predicate: add explicit SHN_XINDEX handling with a companion `.symtab_shndx` section-data carrier
- Priority: **MED**

**Gap 60: Versym index parallel alignment (≥ 0 and < verdef/verneed count)**
- Source: `research/02-gnu-extensions.md` §GNU Symbol Versioning — §How It Works (values 2-0x7ffe reference verdef/verneed)
- Current Lean status: **PARTIAL** — `VersymLengthMatchesDynsym` covers length but not index bounds
- Suggested Lean predicate: `def VersymIndicesInBounds (elf) : Prop := ∀ v ∈ versym, v.lowBits = 0 ∨ v.lowBits = 1 ∨ ∃ vd ∈ verdef, v.lowBits = vd.ndx ∨ ∃ vn ∈ verneed.aux, v.lowBits = vn.other`
- Priority: **HIGH**

**Gap 61: `vn_file` offset is a valid null-terminated string in `.dynstr`**
- Source: `research/04-patchelf-invariants.md` §replaceNeeded() Cross-Table Updates [^55]
- Current Lean status (post-R4): **PARTIAL** — `VernedVnFileMatchesNeeded` was defined standalone by T15 in `Spec/Invariants.lean`; a sorried bridge theorem `vernedVnFileMatchesNeeded_on_valid` connects validity to the predicate. `addNeeded_verneed_coherent` was closed; `replaceNeeded_preserves_verneed_coherence` remains sorried. Predicate is **not yet a field** of `IsValidELF` (blocked on positional refine — T11 picked Option B, leaving field-addition still Op-breaking).
- Suggested Lean predicate: promote `VernedVnFileMatchesNeeded` to a field of `IsValidELF` (requires macro update across every Op's `_preserves_validity`) and discharge the bridge theorem.
- Priority: **HIGH** (Issue #115)

**Gap 62: Version-def `vd_next` linked-list correctness**
- Source: `research/02-gnu-extensions.md` §.gnu.version_d (linked list of Elf_Verdef structures)
- Current Lean status: **ABSENT**
- Suggested Lean predicate: `def VerdefListWellFormed (verdef) : Prop := each vd_next is either 0 (terminator) or the correct offset to the next entry`
- Priority: **MED**

**Gap 63: Version-need `vn_next` / `vna_next` linked-list correctness**
- Source: `research/02-gnu-extensions.md` §.gnu.version_r
- Current Lean status: **ABSENT**
- Suggested Lean predicate: `def VerneedListWellFormed`
- Priority: **MED**

**Gap 64: `VER_NDX_LOCAL = 0` and `VER_NDX_GLOBAL = 1` reserved**
- Source: `research/02-gnu-extensions.md` §How It Works
- Current Lean status: **ABSENT**
- Suggested Lean predicate: `def VerndxGlobalLocalNeverRedefined (elf) : Prop := ∀ vd ∈ verdef, vd.ndx ∉ {VER_NDX_LOCAL, VER_NDX_GLOBAL}`
- Priority: **LOW**

---

## F. String Tables

**Gap 65: `.dynstr` byte-0 is 0 (empty-string sentinel)**
- See Gap 40 above. `StrtabNullTerminated` verifies the *last* byte; the *first* byte is separately specified.

**Gap 66: Permitted empty string tables (`sh_size == 0`)**
- Source: `research/03-dynamic-linking.md` §Open Questions — "The gABI spec permits empty string tables and explicitly states that non-zero indexes are invalid for them"
- Current Lean status: **WEAKER** — `StrtabNullTerminated` handles empty tables via `bytes.size = 0`, but no predicate forbids non-zero string-offset references into an empty table
- Suggested Lean predicate: `def StringOffsetsIntoEmptyStrtabAreZero (elf) : Prop := da.strtab.bytes.size = 0 → ∀ d ∈ strtab-referencing dyn entries, d.value = 0`
- Priority: **LOW**

**Gap 67: `.dynstr` not explicitly validated null-terminated on load (documented gap)**
- Source: `research/04-patchelf-invariants.md` §String Table Null-Termination [^16] ("`.dynstr` is not explicitly validated for null-termination during loading")
- Current Lean status: **EQUIVALENT** — `dynstrNullTerminated` field in `IsValidELF` now covers this at the Lean level
- (no gap; included for accounting)

---

## G. Hash Tables

**Gap 68: SYSV hash chain size may differ from dynsym size (patchelf-specific)**
- Source: `research/03-dynamic-linking.md` §SYSV Hash (DT_HASH) [^17a] — "patchelf's `rebuildHashTable()` does not read `nchain` directly but infers the chain size from the remaining section data, handling the case where `nchain` does not equal the total .dynsym count"
- Current Lean status: **ABSENT** — no SYSV-hash structural invariant in the Spec
- Suggested Lean predicate: `def SysvHashChainMatchesDynsym (elf) : Prop := match da.hashSysv with | some h => h.chain.size = da.symtab.size | none => True` (strict form) or accept the permissive rule
- Priority: **MED**

**Gap 69: SYSV hash `nbucket > 0`**
- Source: gABI Ch. 5 Hash Table
- Current Lean status: **ABSENT**
- Suggested Lean predicate: `def SysvHashNbucketPositive : ∀ h, da.hashSysv = some h → h.bucket.size > 0`
- Priority: **LOW**

**Gap 70: GNU hash `maskwords` power of 2**
- Source: `research/02-gnu-extensions.md` §Section Layout (Bloom filter indexing `% maskwords` requires power-of-2 for masking)
- Current Lean status: **ABSENT**
- Suggested Lean predicate: `def GnuHashMaskwordsPowerOfTwo : ∀ h, da.hashGnu = some h → ∃ k, h.maskwords = 2^k`
- Priority: **MED**

**Gap 71: GNU hash bucket ordering (full semantic check, not just bound)**
- Source: `research/02-gnu-extensions.md` §Section Layout item 3 ("Buckets: Array of nbuckets uint32 values mapping hash % nbuckets to the first symbol index")
- Current Lean status: **WEAKER** — `ElfFileGnuHashOrdered` (`Invariants.lean:193-199`) only checks `hash.symndx ≤ da.symtab.size`; the actual bucket-sorting predicate is deferred (docstring explicitly says so)
- Suggested Lean predicate: `def GnuHashBucketSorted (elf) : Prop := -- for each symbol at index ≥ symndx, its hash value mod nbuckets is non-decreasing`
- Priority: **HIGH**

**Gap 72: GNU hash chain terminator bit (bit 0 set on last entry)**
- Source: `research/02-gnu-extensions.md` §Section Layout item 4
- Current Lean status: **ABSENT**
- Suggested Lean predicate: `def GnuHashChainTerminated (da) : Prop := for each bucket, the last chain entry has bit 0 set`
- Priority: **HIGH**

**Gap 73: GNU hash bloom-filter consistency (every symbol's 2-bit imprint is present)**
- Source: `research/02-gnu-extensions.md` §Section Layout item 2
- Current Lean status: **ABSENT**
- Suggested Lean predicate: `def GnuHashBloomFilterComplete (da) : Prop := ∀ s ≥ symndx, bit bits of bloom filter for djb2(s.name) are set`
- Priority: **MED** (false positives are tolerated; missing bits cause lookup failure)

**Gap 74: Symbols below `symndx` are excluded from `.gnu.hash`**
- Source: `research/02-gnu-extensions.md` §Comparison with SYSV Hash ("Excluded (below symndx)")
- Current Lean status: **ABSENT**
- Suggested Lean predicate: `def BelowSymndxAreUndefined (da) : Prop := ∀ i < symndx, da.symtab[i].shndx = SHN_UNDEF`
- Priority: **MED**

**Gap 75: DT_MIPS_XHASH / MIPS hash variant**
- Source: `research/04-patchelf-invariants.md` §.dynamic Section Address Coherence (DT_MIPS_XHASH row)
- Current Lean status: **EQUIVALENT** — `DynamicAddrCoherent` includes the DT_MIPS_XHASH clause
- (no gap; included for accounting)

---

## H. Version Tables

**Gap 76: `.gnu.version` hidden-bit (0x8000) preservation semantics**
- Source: `research/02-gnu-extensions.md` §How It Works — "Bit 15 (0x8000): Hidden bit — symbol not visible to static linker"
- Current Lean status: **ABSENT**
- Suggested Lean predicate: `theorem clearSymbolVersion_preserves_hidden_bit_off : result.versym[i].raw.hi = 0` (since clear sets to VER_NDX_GLOBAL which has hi=0)
- Priority: **LOW**

**Gap 77: `DT_VERDEF` address coherence tag**
- Source: `research/03-dynamic-linking.md` §GNU/OS-Specific Tags (DT_VERNEED is present; DT_VERDEF has value 0x6ffffffc but is missing from table — actually present as `DT_VERDEFNUM` / verdef pointer)
- Current Lean status: **PARTIAL** — `DynamicAddrCoherent` covers DT_VERNEED but not DT_VERDEF
- Suggested Lean predicate: extend `DynamicAddrCoherent` with `d.tag = DT_VERDEF → ∃ sh, sh.type = SHT_GNU_VERDEF ∧ sh.addr = d.value`
- Priority: **HIGH**

**Gap 78: Symbol versioning interaction with IRELATIVE and lazy binding**
- Source: `research/03-dynamic-linking.md` §The ELF Loading Process step 13 [^22a]
- Current Lean status: **ABSENT**
- Suggested Lean predicate: blocked on integrated semantics; for now, `opPreservesVersioningTables : ∀ op preserving .dynsym, op preserves .gnu.version/.version_d/.version_r cross-references`
- Priority: **MED**

---

## I. Relocations

**Gap 79: DT_RELR / SHT_RELR handling (research flags as CRITICAL)**
- Source: `research/05-edge-cases-and-gaps.md` §RELR Relocations — Critical Gap [^14-^20]
- Current Lean status: **PARTIAL** — `RelrAddressesInBounds` is defined (`Spec/Invariants.lean:518`) and a vacuous-case closure `RelrAddressesInBounds_of_not_hasRelr` exists (`Spec/Invariants.lean:731`); the predicate is deliberately *not* yet part of the `IsValidELF` structure (documented rationale at `Spec/Invariants.lean:532-545`). `OpError.relrPresent` gate exists in `Validity.lean:132` but no Op is yet conditioned on it. (The previously-cited `IsValidELF_relr_in_bounds_promise` was a projection-style theorem that has been removed under Round-4 T1.)
- Suggested Lean predicate: close the `sorry`, add `relrInBounds : RelrAddressesInBounds elf` to `IsValidELF`, and wire each section-moving Op to reject `elf.hasRelr = true`
- Priority: **HIGH**

**Gap 80: `sh_type = SHT_RELR` section `sh_entsize = sizeof(uintptr_t)`**
- Source: `research/05-edge-cases-and-gaps.md` §RELR Relocations — §What RELR Is
- Current Lean status: **ABSENT**
- Suggested Lean predicate: extend Gap 38's `ShEntsizeConsistent` to include SHT_RELR
- Priority: **MED**

**Gap 81: Relocation `r_offset` is addressable (in some PT_LOAD)**
- Source: `research/03-dynamic-linking.md` §The ELF Loading Process step 13 (relocations applied to loaded addresses)
- Current Lean status: **PARTIAL** — RELR has `RelrAddressesInBounds`; the analogous predicate for SHT_REL/SHT_RELA is absent
- Suggested Lean predicate: `def RelOffsetsInBounds (elf) : Prop := ∀ r ∈ allRelocations elf, ∃ ph ∈ elf.programHeaders, ph.type = PT_LOAD ∧ ph.vaddr ≤ r.offset ∧ r.offset < ph.vaddr + ph.memsz`
- Priority: **HIGH**

**Gap 82: Relocation `r_sym` (the symbol index) is in bounds of `.dynsym`**
- Source: gABI Ch. 5 Relocation
- Current Lean status: **ABSENT**
- Suggested Lean predicate: `def RelSymIndicesInBounds (elf) : Prop := ∀ r ∈ allDynRelocations elf, r.sym < da.symtab.size`
- Priority: **HIGH** (rebuildGnuHashTable reorders dynsym; a missed reloc-table update corrupts this)

**Gap 83: relocation `r_type` validity (per psABI)**
- Source: `research/01-elf-specification.md` §Processor-Specific ABI Supplements
- Current Lean status: **ABSENT**
- Suggested Lean predicate: blocked on psABI enumeration per-arch
- Priority: **LOW**

---

## J. Notes

**Gap 84: Note alignment 4 vs 8 (gABI-vs-GNU conflict)**
- Source: `research/02-gnu-extensions.md` §Note Alignment [^46a-^46c]; `research/05-edge-cases-and-gaps.md` §The 4-byte vs 8-byte Alignment Conflict
- Current Lean status: **ABSENT** — no predicate enforces either convention
- Suggested Lean predicate: `def NoteAlignmentConsistent (elf) : Prop := ∀ sh, sh.type = SHT_NOTE → sh.addralign ∈ {4, 8}` plus a per-section consistency with the enclosing PT_NOTE's `p_align`
- Priority: **HIGH** (Issue #400 "non-contiguous SHT_NOTE sections")

**Gap 85: Note header is always 12 bytes (32-bit fields even on ELF64)**
- Source: `research/05-edge-cases-and-gaps.md` §Binary Format ("both 32-bit and 64-bit note headers use 4-byte (uint32_t) words")
- Current Lean status: **ABSENT**
- Suggested Lean predicate: in `Elf.Notes`: `theorem noteHeader_is_12_bytes : ∀ nh, encodeNhdr nh |>.size = 12`
- Priority: **MED**

**Gap 86: PT_NOTE contains contiguous SHT_NOTE sections (Issue #400)**
- Source: `research/05-edge-cases-and-gaps.md` §PT_NOTE and SHT_NOTE Relationship; Issue #400 [^39]
- Current Lean status: **WEAKER** — `SectionSegmentCoherent` covers containment but not contiguity of multiple SHT_NOTE inside a single PT_NOTE
- Suggested Lean predicate: `def NoteSectionsContiguousInSegment (elf) : Prop := ∀ ph of type PT_NOTE, the SHT_NOTE sections inside it span [ph.offset, ph.offset+ph.filesz) with no gaps`
- Priority: **MED**

**Gap 87: Mixed-alignment notes within one PT_NOTE (LLD splits; Issue #217, #255, #400)**
- Source: `research/05-edge-cases-and-gaps.md` §PT_NOTE and SHT_NOTE Relationship ("mixing different alignments within one PT_NOTE is problematic")
- Current Lean status: **ABSENT**
- Suggested Lean predicate: `def NotesInSegmentShareAlignment (elf) : Prop := ∀ ph of type PT_NOTE, ∀ shA shB both SHT_NOTE inside ph, shA.addralign = shB.addralign` (or forbid by requiring `normalizeNoteSegments` post-condition)
- Priority: **HIGH** (3 separate GitHub issues)

**Gap 88: `.note.gnu.build-id` descriptor integrity**
- Source: `research/02-gnu-extensions.md` §.note.gnu.build-id (SHA-1 20 bytes; SHF_ALLOC)
- Current Lean status: **ABSENT** — no predicate preserves build-id under any Op
- Suggested Lean predicate: `theorem ops_preserve_build_id : ∀ op, op.doesNotClearSectionBytes → original-buildid-bytes = post-buildid-bytes`
- Priority: **MED** (build-id mismatch breaks separate-debuginfo lookup)

**Gap 89: `.note.ABI-tag` descriptor (4 words, OS id + kernel version)**
- Source: `research/02-gnu-extensions.md` §.note.ABI-tag
- Current Lean status: **ABSENT**
- Suggested Lean predicate: similar to Gap 88
- Priority: **LOW**

**Gap 90: `.note.dlopen` (UAPI.12) JSON descriptor preservation**
- Source: `research/05-edge-cases-and-gaps.md` §dlopen Metadata
- Current Lean status: **ABSENT**
- Suggested Lean predicate: `theorem ops_preserve_dlopen_notes : ∀ op, op.isPassthroughForNonKnownNotes → dlopenBytes preserved`
- Priority: **LOW** (preservation-by-default is the goal)

**Gap 91: `.note.gnu.property` ↔ PT_GNU_PROPERTY synchronisation (CET/BTI)**
- Source: `research/02-gnu-extensions.md` §PT_GNU_PROPERTY [^11]
- Current Lean status: **EQUIVALENT** — `SectionSegmentCoherent` includes `.note.gnu.property ↔ PT_GNU_PROPERTY`
- (no gap; included for accounting)

---

## K. Cross-Subsystem / File-Wide

**Gap 92: ET_DYN vs ET_EXEC strategy split (research doc §ET_EXEC vs ET_DYN)**
- Source: `research/04-patchelf-invariants.md` §ET_EXEC vs ET_DYN: Two Strategies (entire table lines 189-219)
- Current Lean status: **ABSENT** — `IsValidELF` does not distinguish; the differing strategies are implicit in Ops implementations but no anti-regression verifies the correctness of each
- Suggested Lean predicate: `theorem shiftFile_applies_only_to_ET_EXEC` and `theorem appendAtEnd_applies_only_to_ET_DYN`
- Priority: **MED**

**Gap 93: Virtual address space underrun for ET_EXEC (≥ VA 0)**
- Source: `research/04-patchelf-invariants.md` §Virtual Address Space Bounds [^19]
- Current Lean status: **ABSENT**
- Suggested Lean predicate: op-precondition for `shiftFile`: `minPtLoadVaddr elf ≥ extraPages * pageSize` (i.e., enough headroom)
- Priority: **HIGH** (already a visible error in C++; Lean should enforce structurally)

**Gap 94: For ET_DYN libraries, new PT_LOAD placed past highest vaddr, rounded up to `alignStartPage`**
- Source: `research/04-patchelf-invariants.md` §Virtual Address Space Bounds (line 131-133) and [^20]
- Current Lean status: **ABSENT**
- Suggested Lean predicate: `theorem library_new_ptload_above_max : ∀ phnew ∈ result.programHeaders - elf.programHeaders, phnew.type = PT_LOAD → phnew.vaddr > max(oldVaddrs + oldMemsz)`
- Priority: **MED**

**Gap 95: `sortShdrs` preserves `sh_link` / `sh_info` translation-by-name / e_shstrndx recovery**
- Source: `research/04-patchelf-invariants.md` §Section Header Cross-References [^14]
- Current Lean status: **ABSENT** as an anti-regression; structurally `DynsymShLinkPointsToDynstr`, `HashShLinkPointsToDynsym` suffice for those two cases but `sortShdrs` itself has no soundness theorem
- Suggested Lean predicate: `theorem sortShdrs_preserves_named_references : ∀ before after, shdrAtName "X" before = shdrAtName "X" after`
- Priority: **HIGH**

**Gap 96: "I'm lazy" assertion (last-non-replaced-section exists after last-replaced)**
- Source: `research/04-patchelf-invariants.md` §Hardcoded Assumptions [^25]
- Current Lean status: **ABSENT**
- Suggested Lean predicate: precondition for executable-path rewriter: `lastReplacedIdx + 1 < sectionHeaders.size`
- Priority: **MED**

**Gap 97: `rewriteSectionsExecutable` stops after `.dynstr` (research author can't recall why)**
- Source: `research/04-patchelf-invariants.md` §Lost Rationale [^21]; §Open Questions (line 336-337)
- Current Lean status: **ABSENT**
- Suggested Lean predicate: blocked on understanding the rationale; until then record as a documented op-precondition comment
- Priority: **MED** (Lean semantics should either replicate or eliminate)

**Gap 98: Binutils 1-byte padding compatibility (for old readelf)**
- Source: `research/04-patchelf-invariants.md` §ET_EXEC vs ET_DYN table last row [^44]
- Current Lean status: **ABSENT**
- Suggested Lean predicate: post-condition on ET_DYN write: `result.fileSize > ptDynamicSegment.offset + ptDynamicSegment.filesz` (strictly)
- Priority: **LOW**

**Gap 99: PHT-at-end-of-file compat with pre-March-2022 Linux kernels**
- Source: `research/04-patchelf-invariants.md` §PHT Relocation for Libraries [^31] (kernel commit 0da1d5002745…)
- Current Lean status: **ABSENT**
- Suggested Lean predicate: optional op-flag with a warning predicate; not structurally enforceable
- Priority: **LOW**

**Gap 100: PIE detection via PT_INTERP (not DF_1_PIE)**
- Source: `research/05-edge-cases-and-gaps.md` §PIE Detection [^31]; Issue #115 [^32]
- Current Lean status: **ABSENT** — no predicate distinguishes PIE executables
- Suggested Lean predicate: `def IsExecutable (elf) : Bool := elf.header.fileType = ET_EXEC ∨ (elf.header.fileType = ET_DYN ∧ hasPhdrOfType elf PT_INTERP)`
- Priority: **MED**

**Gap 101: `DF_1_PIE` consistency with PT_INTERP-based PIE detection**
- Source: `research/02-gnu-extensions.md` §DT_FLAGS_1 (`DF_1_PIE` row); `research/05-edge-cases-and-gaps.md` §PIE Detection
- Current Lean status: **ABSENT**
- Suggested Lean predicate: `def Df1PieConsistent (elf) : Prop := hasDf1 DF_1_PIE ↔ IsExecutable elf ∧ elf.header.fileType = ET_DYN`
- Priority: **LOW**

**Gap 102: `rewriteHeaders()` covers all address-bearing DT_* tags (research §Open Question)**
- Source: `research/03-dynamic-linking.md` §Open Questions ("Are there DT_* tags with embedded addresses that patchelf's rewriteHeaders() does not update?"); `research/05-edge-cases-and-gaps.md` §Open Questions ("Is there a formal specification for which DT_* tags contain addresses vs values?")
- Current Lean status: **ABSENT** — `DynamicAddrCoherent` enumerates a whitelist; no theorem says "no *other* DT tag carries an address"
- Suggested Lean predicate: `def AllAddressTagsCoherent (elf) : Prop := ∀ d ∈ entries, DynamicTag.carriesAddress d.tag → ∃ sh ∈ sectionHeaders, sh.addr = d.value` plus a decidable enumeration of address-carrying tags
- Priority: **HIGH**

**Gap 103: `writeReplacedSections` clobbering stale bytes with `'Z'`**
- Source: `research/04-patchelf-invariants.md` §Old Section Clobbering [^53]
- Current Lean status: **ABSENT** as an explicit invariant
- Suggested Lean predicate: post-condition on any section-moving op: `stale bytes are non-semantic` (either `'Z'`-filled or otherwise unreferenced)
- Priority: **LOW**

**Gap 104: RPATH string sharing detection (forAllStringReferences)**
- Source: `research/04-patchelf-invariants.md` §RPATH String Sharing Detection [^38][^38a]
- Current Lean status: **ABSENT**
- Suggested Lean predicate: `theorem setRpath_preserves_all_other_dt_string_values : ∀ d, d.tag ≠ DT_RPATH ∧ d.tag ≠ DT_RUNPATH → stringAt d.value elf = stringAt d.value (setRpath elf r)`
- Priority: **HIGH** (corruption of SONAME / NEEDED if sharing is missed)

**Gap 105: `isChanged` / `alwaysWrite` gating (write side-effect correctness)**
- Source: `research/04-patchelf-invariants.md` §Write Gating [^60]
- Current Lean status: **ABSENT** as a theorem
- Suggested Lean predicate: `theorem write_is_noop_when_unchanged : elf.isChanged = false → Ops.Write.write elf = parseOutputOf elf` (byte-identical)
- Priority: **LOW** (partially handled by `write_idempotent_on_unmodified`)

**Gap 106: Load base / lowest-PT_LOAD-vaddr for PIE**
- Source: `research/03-dynamic-linking.md` §Base Address (line 88-91)
- Current Lean status: **ABSENT**
- Suggested Lean predicate: `def loadBase (elf) : UInt64 := (minVaddr-of-PT_LOAD elf) & ~pageMask`; invariant: for ET_DYN, minVaddr = 0 after link (positioning is load-time)
- Priority: **MED**

**Gap 107: `DT_STRTAB == .dynstr` assumption (research flags as fragile)**
- Source: `research/04-patchelf-invariants.md` §Hardcoded Assumptions [^26]; `research/03-dynamic-linking.md` §Open Questions ("What happens when DT_STRTAB points to a virtual address that doesn't correspond to .dynstr's section header?")
- Current Lean status: **PARTIAL** — `DynamicAddrCoherent.DT_STRTAB → some SHT_STRTAB sh.addr = d.value` requires *some* STRTAB section to match but does not pin it to the section named `.dynstr`
- Suggested Lean predicate: `def DT_STRTAB_pinsToDynstr (elf) : Prop := findSection ".dynstr" = some idx → ∀ d, d.tag = DT_STRTAB → sectionHeaders[idx].addr = d.value`
- Priority: **HIGH**

**Gap 108: DT_JMPREL section name is one of the expected set (`.rel.plt`, `.rela.plt`, `.rela.IA_64.pltoff`)**
- Source: `research/04-patchelf-invariants.md` §.dynamic Section Address Coherence (row for DT_JMPREL)
- Current Lean status: **WEAKER** — `DynamicAddrCoherent` matches any SHT_REL/SHT_RELA section; the name-specific constraint is unchecked
- Suggested Lean predicate: augment with named section match
- Priority: **MED**

**Gap 109: DT_REL fallback `.rel.dyn` / `.rel.got` (C++ hedge)**
- Source: `research/04-patchelf-invariants.md` §Lost Rationale [^22] ("no idea if this makes sense, but it was needed for some program")
- Current Lean status: **ABSENT** as a documented preference
- Suggested Lean predicate: preference order in section-name resolution
- Priority: **LOW**

---

## L. Bug-Class Anti-Regressions

**Gap 110: Issue #152 — `--set-rpath` places `.dynamic` in read-only PT_LOAD**
- Source: `research/05-edge-cases-and-gaps.md` §Pattern 1 [^33]
- Current Lean status: **EQUIVALENT** — `AntiRegressions.setRpath_dynamic_remains_writable` proves it by functional shape (`programHeaders` untouched)
- (no gap)

**Gap 111: PR #202 — re-running patchelf corrupts top of `.dynamic`**
- Source: `research/05-edge-cases-and-gaps.md` §Pattern 1 [^34]
- Current Lean status: **ABSENT** — no anti-regression theorem
- Suggested Lean predicate: `theorem op_idempotent : ∀ op, op (op elf) = op elf` for the idempotent ops (e.g., setRpath with same path)
- Priority: **HIGH** (highly visible Nix-use regression)

**Gap 112: Issue #446 — patchelf 0.17.0 segfault after RPATH modification**
- Source: `research/05-edge-cases-and-gaps.md` §Pattern 1 [^35]
- Current Lean status: **ABSENT**
- Suggested Lean predicate: implied by broader correctness of `setRpath`; a specific regression theorem would take the form `setRpath elf r preserves PT_LOAD validity`
- Priority: **HIGH**

**Gap 113: Issue #507 — patchelf + llvm-strip sequence corrupts binaries**
- Source: `research/05-edge-cases-and-gaps.md` §Pattern 2 [^36]
- Current Lean status: **PARTIAL** — `write_idempotent_on_unmodified` is a loose proxy; the real invariant is section-header order preservation under write
- Suggested Lean predicate: `theorem write_preserves_section_order : (Ops.Write.write elf).sectionHeaders.order = elf.sectionHeaders.order`
- Priority: **HIGH**

**Gap 114: Issue #520 — Firefox relrhack hardcodes `.dynamic` addresses**
- Source: `research/05-edge-cases-and-gaps.md` §Pattern 2 [^20]
- Current Lean status: **PARTIAL** — `setRpath` doesn't move `.dynamic` (see #152 anti-regression), but any op that *does* move `.dynamic` must update the RELR entries
- Suggested Lean predicate: `theorem ops_preserve_dynamic_address : ∀ op preserving `.dynamic` address, relrhack-compatible`; fully solved only when RELR is handled (Gap 79)
- Priority: **HIGH**

**Gap 115: Issue #217 — PT_NOTE not updated when relocating SHT_NOTE**
- Source: `research/05-edge-cases-and-gaps.md` §Pattern 3 [^37]
- Current Lean status (post-R4): **WEAKER** — T2 replaced the vacuous `True := trivial` with a real sorried statement: `ops_preserve_note_containment` in `Spec/AntiRegressions.lean` now quantifies over PT_NOTE / SHT_NOTE containment, but the proof is `sorry`. The underlying predicate is **not yet a field** of `IsValidELF`.
- Suggested Lean predicate: promote the containment clause to a field of `IsValidELF` or of `SectionSegmentCoherent`; discharge the sorry.
- Priority: **HIGH**

**Gap 116: Issue #255 — "unsupported overlap of SHT_NOTE and PT_NOTE" with Rust ELFs**
- Source: `research/05-edge-cases-and-gaps.md` §Pattern 3 [^38]
- Current Lean status: **ABSENT**
- Suggested Lean predicate: `def NoteSegmentOverlapsLegal (elf) : Prop := SHT_NOTE sections inside PT_NOTE ranges don't overlap with each other beyond segment boundaries`
- Priority: **MED**

**Gap 117: Issue #400 — non-contiguous SHT_NOTE sections error**
- Source: `research/05-edge-cases-and-gaps.md` §Pattern 3 [^39]
- Current Lean status: **ABSENT**
- Suggested Lean predicate: covered by Gap 86 `NoteSectionsContiguousInSegment`
- Priority: **MED**

**Gap 118: Issue #403 — normalizeNoteSegments causes `.dynstr` to not be fully contained**
- Source: `research/05-edge-cases-and-gaps.md` §Pattern 3 [^40]
- Current Lean status: **ABSENT**
- Suggested Lean predicate: `theorem normalizeNoteSegments_preserves_dynstr_containment : ∀ elf, ∃ ph of type PT_LOAD s.t. `.dynstr` fully contained before → still after`
- Priority: **HIGH**

**Gap 119: Issue #115 — `--add-needed`/`--remove-needed` breaks PIE executables (ld.so dl-version assert)**
- Source: `research/05-edge-cases-and-gaps.md` §Pattern 4 [^32]
- Current Lean status (post-R4): **PARTIAL** — T15 closed `AntiRegressions.addNeeded_verneed_coherent`. The symmetric `replaceNeeded_preserves_verneed_coherence` in `Ops/Needed.lean` remains sorried. `VernedVnFileMatchesNeeded` exists as a standalone predicate (T15) but is still not part of `IsValidELF`. (See also Gap 61.)
- Suggested Lean predicate: close `replaceNeeded_preserves_verneed_coherence`, promote `VernedVnFileMatchesNeeded` into `IsValidELF`, add `removeNeeded_verneed_coherent` companion.
- Priority: **HIGH**

**Gap 120: Issue #244 — `--set-rpath` outputs binary with broken `.dynsym`/`.dynstr`**
- Source: `research/05-edge-cases-and-gaps.md` §Pattern 4 [^41]
- Current Lean status: **ABSENT**
- Suggested Lean predicate: `theorem setRpath_preserves_dynsym_dynstr : preserving all of .dynsym offsets, .dynstr existing-string offsets, and the dynsym-to-dynstr sh_link`
- Priority: **HIGH**

**Gap 121: Issue #215 — ARM Android soname change → C++ exception stack corruption**
- Source: `research/05-edge-cases-and-gaps.md` §Pattern 5 [^42]
- Current Lean status: **ABSENT**
- Suggested Lean predicate: likely PT_TLS or eh_frame-related; blocked on per-architecture analysis
- Priority: **MED** (platform-specific)

**Gap 122: Issue #568 — segfault on Fedora 41 after `--set-rpath` (binutils layout change)**
- Source: `research/05-edge-cases-and-gaps.md` §Pattern 5 [^43]
- Current Lean status: **ABSENT**
- Suggested Lean predicate: implied by broader `setRpath` validity but no specific theorem
- Priority: **MED**

**Gap 123: `modifyExecstack` dead-code bug (research §modifyExecstack)**
- Source: `research/04-patchelf-invariants.md` §modifyExecstack Strategies [^49][^49a]; `research/05-edge-cases-and-gaps.md` (absent from that doc's explicit list but referenced)
- Current Lean status: **EQUIVALENT** — `AntiRegressions.execstack_strategies_exhaustive` re-exports the ops-level theorem
- (no gap)

**Gap 124: Pattern-6 (compile-time) GCC `rdi()` inlining bug workaround**
- Source: `research/04-patchelf-invariants.md` §Compiler Workaround [^28]
- Current Lean status: **N/A** — Lean doesn't have this compiler bug, but the fact that the C++ needed a workaround signals endianness handling is error-prone
- Suggested Lean predicate: `theorem all_U16_U32_U64_encode_round_trip : ∀ x enc, decodeU* (encodeU* x enc) = x` (foundational; likely already present in Elf.Encoding)
- Priority: **LOW**

---

## Additional Cross-Cutting Gaps Missed by Prior Reviews

**Gap 125: Auxiliary vector consistency (`AT_PHDR`, `AT_PHNUM`, `AT_ENTRY`) implicit requirements**
- Source: `research/03-dynamic-linking.md` §The ELF Loading Process step 8 [^22c]
- Current Lean status: **ABSENT** — these are derived from the header fields the Lean already tracks, but no explicit cross-check
- Suggested Lean predicate: `def AuxvDerivable (elf) : Prop := elf.phoff > 0 ∧ elf.phnum > 0 ∧ elf.entry > 0 ∨ elf.header.fileType ∉ {ET_EXEC, ET_DYN}`
- Priority: **LOW**

**Gap 126: `AT_RANDOM` / `AT_EXECFN` / `AT_SYSINFO_EHDR` do not leak into ELF structures**
- Source: `research/03-dynamic-linking.md` §The ELF Loading Process step 8
- Current Lean status: **N/A** — kernel-side; no Lean representation
- Priority: **LOW**

**Gap 127: `DT_SYMBOLIC` (superseded by DF_SYMBOLIC) handling**
- Source: `research/03-dynamic-linking.md` §Standard Tags (line 150)
- Current Lean status: **ABSENT**
- Suggested Lean predicate: analogous to Gap 49's `DT_TEXTREL`: `def DT_SYMBOLIC_matches_DF_SYMBOLIC : ...`
- Priority: **LOW**

**Gap 128: DT_FLAGS_1 flags enumeration completeness (30+ flags per glibc `elf.h`)**
- Source: `research/02-gnu-extensions.md` §DT_FLAGS_1 and DF_1_* Flags [^33]
- Current Lean status: **ABSENT** — `DynamicTag` enumeration likely covers only a subset
- Suggested Lean predicate: ensure `DF_1_*` flag enum matches glibc's full table; add `def Df1FlagsUnknownPreserved : all unknown high bits preserved`
- Priority: **LOW**

**Gap 129: `DF_1_GROUP`, `DF_1_LOADFLTR`, `DF_1_INITFIRST`, `DF_1_DIRECT`, `DF_1_NODUMP` behaviour preservation**
- Source: `research/03-dynamic-linking.md` §DT_FLAGS_1 table
- Current Lean status: **ABSENT** (any write that adds DF_1_NODEFLIB must preserve these bits)
- Suggested Lean predicate: `theorem noDefaultLib_preserves_other_df1_bits : ∀ b ≠ DF_1_NODEFLIB bit, (noDefaultLib elf).df1Bit b = elf.df1Bit b`
- Priority: **MED**

**Gap 130: `getElfType()` endianness FIXME (research §Open Questions line 340)**
- Source: `research/04-patchelf-invariants.md` §Open Questions ("`getElfType()` endianness FIXME — has this caused real bugs on big-endian hosts modifying little-endian binaries?")
- Current Lean status: **ABSENT** as explicit anti-regression
- Suggested Lean predicate: `theorem parse_get_elf_type_endianness_correct : ∀ bytes, parseElfType bytes = interpret bytes with bytes.ident.dataEncoding`
- Priority: **MED**

**Gap 131: LIEF segment-based alternative not a blocker, but a design open-question**
- Source: `research/05-edge-cases-and-gaps.md` §LIEF [^44]
- Current Lean status: **N/A** — architectural, not an invariant
- Priority: (not a gap)

**Gap 132: Notes' descriptor `n_descsz` consistency with descriptor bytes**
- Source: `research/05-edge-cases-and-gaps.md` §Binary Format
- Current Lean status: **ABSENT**
- Suggested Lean predicate: `def NoteDescSizeMatches (nh) : Prop := nh.descBytes.size = nh.n_descsz.toNat`
- Priority: **MED**

**Gap 133: Notes' `n_namesz` includes null terminator**
- Source: `research/05-edge-cases-and-gaps.md` §Binary Format ("name, null-terminated")
- Current Lean status: **ABSENT**
- Suggested Lean predicate: `def NoteNameNullTerminated (nh) : Prop := nh.name.size > 0 → nh.name[nh.name.size - 1] = 0 ∧ nh.n_namesz.toNat = nh.name.size`
- Priority: **LOW**

**Gap 134: `SHT_NOBITS` with `SHF_ALLOC` (typical `.bss` layout)**
- Source: gABI Ch. 4 Sections (`SHT_NOBITS` combined with `SHF_ALLOC`)
- Current Lean status: **ABSENT**
- Suggested Lean predicate: `def BssNobitsAlloc : ∀ sh with name = ".bss", sh.type = SHT_NOBITS ∧ sh.flags.alloc ∧ sh.flags.write`
- Priority: **LOW**

**Gap 135: `.bss` in-memory region within a PT_LOAD where `p_memsz > p_filesz`**
- Source: `research/03-dynamic-linking.md` §BSS Handling
- Current Lean status: **PARTIAL** — `PtLoadFileszMemsz` captures `filesz ≤ memsz` but not the `.bss` section's presence in the `(p_offset + p_filesz, p_offset + p_memsz)` gap
- Suggested Lean predicate: `def BssInBssRegion (elf) : Prop := ∀ sh .bss, ∃ ph PT_LOAD, ph.vaddr + ph.filesz ≤ sh.addr ∧ sh.addr + sh.size ≤ ph.vaddr + ph.memsz`
- Priority: **MED**

---

## Summary Statistics

Counts are computed by scanning this file:

- **Total gaps catalogued**: 135 (numbered 1-135).
- **Priority distribution**: HIGH=39, MED=51, LOW=36 — 9 gaps are untagged (no `Priority:` line).
- **Status distribution (tallied post-R5 by Python scan)**: ABSENT=94, PARTIAL=21, WEAKER=8, EQUIVALENT=8 — total 131 labelled; 4 gaps carry no status tag. The earlier catalog self-claim of "135 gaps, 131 labelled" is accurate in aggregate but was previously unbroken-down by label.

### Known staleness in this catalog

Round-4 work has shifted some of the situations below. The catalog entries still reflect the pre-Round-4 state unless explicitly updated:

- **Gap 61** (`vn_file` valid offset, `VernedVnFileMatchesNeeded`): Round-4 T15 defined the predicate standalone in `Spec/Invariants.lean` and added a sorried bridge theorem `vernedVnFileMatchesNeeded_on_valid`. The predicate is **still not a field** of `IsValidELF` (blocked on the positional-refine issue — T11 picked Option B which doesn't add fields). Status is now PARTIAL, up from ABSENT.
- **Gap 79** (RELR in `IsValidELF`): the predicate `RelrAddressesInBounds` exists standalone, with a vacuous-case closure `RelrAddressesInBounds_of_not_hasRelr`. The actual gap is "not a field of `IsValidELF`" and "no Op consults `OpError.relrPresent`". (Round-4 T1 removed a previously-cited projection theorem `IsValidELF_relr_in_bounds_promise`; any surviving citation of that name elsewhere in this catalog is stale.)
- **Gap 115** (`ops_preserve_note_containment := trivial`): unit T2 replaced the vacuous `True := trivial` with a real sorried statement in `Spec/AntiRegressions.lean`. The predicate is still not a field of `IsValidELF`, so the underlying gap remains; only the artifact cited in the "Current Lean status" line is stale.
- **Gap 119** (verneed coherence under `replaceNeeded`): Round-4 T15 closed `addNeeded_verneed_coherent` for the easy case; `replaceNeeded_preserves_verneed_coherence` remains sorried (and is in `Ops/Needed.lean`, not `Spec/AntiRegressions.lean` as the original citation stated).
- Line numbers for `Spec/Invariants.lean` cited below have shifted after T1's projection-theorem deletions (`Spec/Invariants.lean:639-745` removed) and T11's `refine_IsValidELF` macro additions.
- Several proposed Lean predicates use identifier names (`ELFOSABI_SYSV`, `STT_GNU_IFUNC`, `ET_LOOS`, `EM_NONE`, `VER_NDX_LORESERVE`, etc.) that may not exist in the project's enumerations; treat those signatures as schematic.

### Adversarial-review findings (partially integrated)

A later adversarial pass surfaced additional gaps. Status for each:

- **[Partially addressed R5-G+I3]** Missing `sh_size % sh_entsize = 0` (`ShEntsizeDivides`), `sh_name` offset validity (`ShNameInBounds`), `PT_INTERP`/`PT_PHDR` must-precede-PT_LOAD (`PtInterpPrecedesPtLoad`, `PtPhdrPrecedesPtLoad`), `PhtCoveredByPtLoad`, `EntryPointInExecLoad`, `StringOffsetsIntoStrtabValid`, `SysvNchainMatchesDynsymSize`, `GnuHashMaskwordsPow2` — all now defined as standalone predicates in `Spec/Invariants.lean`. Not yet fields of `IsValidELF` (blocked on positional refine).
- **Mis-tagged priority: Gap 6** (`e_entry` in executable PT_LOAD) is tagged HIGH with justification "corrupted e_entry → SIGSEGV", but `patchelf.cc` never modifies `e_entry`. This is a parse-time validation concern, not an Op-preservation concern. Priority should be LOW for Op-preservation purposes, perhaps MED for parse hardening.
- **Still missing: PT_TLS tracking.** `SegmentType.PT_TLS` is enumerated in Lean but no `IsValidELF` clause tracks it. Gap 21 lists PT_TLS risks but not a concrete predicate. Suggested: `ops_preserve_pttls_align` theorem (exists, sorried) should be backed by a validity clause; currently it dangles.
- **Still missing: `SHT_SYMTAB_SHNDX` / `SHN_XINDEX` handling.** Large-section-count ELFs use this escape hatch. Gap 59 mentions `st_shndx` in bounds but not the `SHN_XINDEX` sentinel path.
- **Duplication between K and L subsystems.** Section L (Bug-Class Anti-Regressions) and Section K (Cross-Subsystem / File-Wide) both cover Issue #115 from different angles; needs dedup.
- **Stub entries in the 135 list.** Gaps 65 (dup of 40), 117 (dup of 86), 131 (LIEF, marked "not a gap"), 126 (kernel auxv, N/A) inflate the count without contributing. 9 entries have no `Priority:` tag at all.

### R5 anti-regression additions

G7+A2 (R5) added these anti-regression theorem statements to `Spec/AntiRegressions.lean` (all sorried — statements only):

- Issue #244: `setRpath_preserves_dynsym_dynstr_coherence`.
- Issue #446: `setRpath_preserves_pt_load_containment`.
- PR #202: `setRpath_idempotent_runtime`, `setSoname_idempotent_runtime`.
- `runtime_unchanged_on_roundtrip` (identity theorem for parse∘write).

### Overlap with ROADMAP.md

ROADMAP's "Top-priority gaps" and "Highest-leverage structural expansions" sections duplicate the two lists below. Treat ROADMAP as the index and this catalog as the enumerated detail; the bullet lists in ROADMAP will be kept in sync with this file's sample selection.

### Top-priority gaps (sample)

Candidates for "work on these first" to unblock downstream proofs. This list is one reviewer's selection from the HIGH-tagged gaps; other HIGH gaps may be equally urgent.

1. **Gap 79** — RELR as a field of `IsValidELF`; Op-level `¬ elf.hasRelr` gate.
2. **Gap 102** — Completeness of the address-bearing DT_* tag whitelist in `DynamicAddrCoherent`.
3. **Gap 115** — PT_NOTE / SHT_NOTE containment predicate wired into `IsValidELF`.
4. **Gap 119** — `VernedVnFileMatchesNeeded` as a field of `IsValidELF`.
5. **Gaps 52 + 104** — DT_* string-offset validity and RPATH string-sharing preservation.

### Structural expansions that would unblock many downstream proofs

1. Add `VernedVnFileMatchesNeeded` to `IsValidELF` (unblocks Gap 119).
2. Add `RelrAddressesInBounds` to `IsValidELF` plus Op-level `¬ elf.hasRelr` gate (unblocks Gap 79 / 114).
3. Generalise `DynamicAddrCoherent` with a decidable `DynamicTag.carriesAddress` and a completeness theorem (unblocks Gap 102).
4. Add `LoadableSegmentVaddrNonOverlap` (unblocks Gap 25).
5. Add `StringOffsetsIntoStrtabValid` for DT_NEEDED / DT_SONAME / DT_RPATH / DT_RUNPATH (unblocks Gaps 52 / 61 / 120).

### Referenced but not enumerated

Research-doc Open Questions that cannot be resolved by a single Lean predicate:

- `research/01` §Open Questions: FreeBSD / Solaris conflicts with GNU extensions.
- `research/02` §Open Questions: Solaris-specific `DF_1_*` flag interactions with GNU `ld.so`.
- `research/03` §Open Questions: TLS, PLT-GOT, `DT_PREINIT_ARRAY` mechanics.
- `research/04` §Open Questions: `sh_addralign` unconditional overwrite (catalogued as Gap 32).
- `research/05` §Open Questions: whether to adopt LIEF's segment-based approach.

---

## Key Lean file:line citations at time of writing

These citations are approximate; Round-4 edits (T1 deletions) have
shifted some line numbers. Verify against the current tree before
use.

- `lean/Patchelf/Spec/Invariants.lean`, `IsValidHeader` (minimal header coverage) — referenced by Gap 1–10.
- `lean/Patchelf/Spec/Invariants.lean`, `DynamicAddrCoherent` (tag whitelist) — Gap 102.
- `lean/Patchelf/Spec/Invariants.lean`, `ElfFileGnuHashOrdered` (weaker than full bucket-sort) — Gap 71.
- `lean/Patchelf/Spec/Invariants.lean`, `RelrAddressesInBounds` (standalone, not a field) — Gap 79.
- `lean/Patchelf/Spec/Invariants.lean`, `IsValidELF` structure — Gaps 11 / 14 / 21 / 33 / 41 / 42 / 61 / 71 / 79 / 82 targets.
- `lean/Patchelf/Spec/AntiRegressions.lean`, `addNeeded_verneed_coherent` (sorry) — Gap 119.
- `lean/Patchelf/Spec/AntiRegressions.lean`, `ops_preserve_note_containment` (post-T2, sorried real statement) — Gap 115.
- `lean/Patchelf/Spec/Validity.lean`, `ParseError` (includes `pnXnumNotSupported`, `relrRequiresSupport`, `unimplemented`).

---

## Open Questions

- **Triage quality.** Priorities are one-reviewer judgments. Two gaps in particular seem mis-tagged: Gap 6 (`e_entry` in exec PT_LOAD) is tagged HIGH for reasons that apply to parser validation, not Op preservation; patchelf does not modify `e_entry`. Gap 14 (PT_PHDR must be covered by a PT_LOAD) should probably be HIGH but isn't listed in the top-5.
- **Completeness.** Section L "Bug-Class Anti-Regressions" and Section K "Cross-Subsystem / File-Wide" have topic overlap (e.g. Issue #115 is referenced in both). Untangling requires deciding whether the catalog is organized by "where the invariant lives" or "which bug it prevents".
- **Identifier grounding.** Many proposed Lean predicates reference enumeration values (`ELFOSABI_SYSV`, `STT_GNU_IFUNC`, `ET_LOOS`, `EM_NONE`, `VER_NDX_LORESERVE`, etc.) that may or may not exist in the current project. A follow-up pass should either ground each suggestion in existing identifiers or note where enumerations need expanding.
- **Footnote resolution.** Many entries cite research-doc footnotes by number (`[^8]`, `[^21]`, etc.) without resolving them inline. Readers have to look them up in the source doc. A follow-up pass could inline the resolved citation, or this catalog could adopt its own footnote-definition section.
- **"Missed by Prior Reviews" subsection.** This is an afterthought section that should either be merged into the relevant subsystems (A–L) or promoted to its own lettered subsystem.
- **Overlap with ROADMAP.md.** The "Structural expansions" list duplicates content now living in `ROADMAP.md`. A single source of truth should be chosen.
- `/Users/cbaker2/ext-sources/patchelf/lean/Patchelf/Spec/Validity.lean:129-136` — `OpError.relrPresent` gate (not yet wired to any Op)
