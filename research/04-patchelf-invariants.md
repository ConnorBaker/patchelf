# Patchelf Structural Invariants

Patchelf modifies ELF binaries in-place by rewriting sections and program
headers. This document catalogs the structural invariants it must maintain,
the fragile parts of the current implementation, and the differences between
how it handles executables vs shared libraries.

## Overview of Operations

Patchelf performs the following classes of modifications:

1. **String replacement**: changing the interpreter path, RPATH/RUNPATH, SONAME, or NEEDED library names by growing `.dynstr` and updating `.dynamic` entries
2. **Dynamic entry manipulation**: adding/removing DT_NEEDED, DT_RUNPATH, DT_RPATH, DT_SONAME, DT_FLAGS_1, DT_DEBUG entries in `.dynamic`
3. **Section rewriting**: replacing section contents and adjusting all headers to maintain consistency
4. **Symbol manipulation**: renaming dynamic symbols, clearing symbol versions, rebuilding hash tables
5. **Program header manipulation**: modifying PT_GNU_STACK flags, normalizing PT_NOTE segments

All of these ultimately flow through `rewriteSections()`, which dispatches
to either `rewriteSectionsExecutable()` or `rewriteSectionsLibrary()` based
on `e_type`.[^1]

## Invariants Maintained

### Page Alignment

ELF segments must satisfy a congruence requirement: the virtual address and
file offset must be congruent modulo the alignment.[^2] Patchelf enforces
this with explicit assertions: in the executable path, congruence is
checked modulo `getPageSize()`; in the library path, it is checked modulo
`alignStartPage` (which may be larger than the page size).[^3]

Page sizes are architecture-dependent. Patchelf uses the following defaults
(derived from GNU gold's `abi_pagesize`):[^4]

| Architecture | Page Size |
|---|---|
| Alpha, IA-64, MIPS, PPC, PPC64, AArch64, TileGX, LoongArch | 64 KB (0x10000) |
| SPARC, SPARC64 | 8 KB (0x2000) |
| All others (x86, x86-64, ARM, RISC-V, ...) | 4 KB (0x1000) |

These can be overridden with `--page-size`. New PT_LOAD segments in the executable path are created with `p_align`
set to `getPageSize()`.[^5] In the library path, `p_align` is set to
`alignStartPage`, which is the maximum of all existing segment alignments
and `getPageSize()` -- this may exceed the page size for binaries with
larger-aligned segments.[^5a]

When shifting file contents via `shiftFile()`, if the shift breaks a
segment's `p_vaddr - p_offset` alignment, patchelf corrects `p_align` to
the page size.[^6]

### Section/Segment Synchronization

Several section/segment pairs must stay synchronized. When a section's
offset or address changes, the corresponding segment must be updated:[^7]

| Section | Segment | Fields synchronized |
|---|---|---|
| `.interp` | `PT_INTERP` | `p_offset`, `p_vaddr`, `p_paddr`, `p_filesz`, `p_memsz` |
| `.dynamic` | `PT_DYNAMIC` | `p_offset`, `p_vaddr`, `p_paddr`, `p_filesz`, `p_memsz` |
| `SHT_NOTE` sections | `PT_NOTE` | `p_offset`, `p_vaddr`, `p_paddr`, `p_filesz`, `p_memsz` |
| `.MIPS.abiflags` | `PT_MIPS_ABIFLAGS` | `p_offset`, `p_vaddr`, `p_paddr`, `p_filesz`, `p_memsz` |
| `.note.gnu.property` | `PT_GNU_PROPERTY` | `p_offset`, `p_vaddr`, `p_paddr`, `p_filesz`, `p_memsz` |
| Program header table | `PT_PHDR` | `p_offset`, `p_vaddr`, `p_paddr`, `p_filesz`, `p_memsz`[^7a] |

The PT_PHDR segment is special: it describes the program header table
itself. The ELF spec states there can be at most one.[^8]

Additionally, the code ensures the program header table is covered by a
PT_LOAD segment so the kernel can mmap it.[^9]

### .dynamic Section Address Coherence

After sections are moved, entries in `.dynamic` that reference section
addresses or sizes must be updated. The following DT_* tags have their
`d_un.d_ptr` rewritten to the new `sh_addr` of the corresponding
section (except `DT_STRSZ`, which uses `d_un.d_val` set to
`sh_size`):[^10]

| DT tag | Section | Field |
|---|---|---|
| `DT_STRTAB` | `.dynstr` | `d_ptr` <- `sh_addr` |
| `DT_STRSZ` | `.dynstr` | `d_val` <- `sh_size` |
| `DT_SYMTAB` | `.dynsym` | `d_ptr` <- `sh_addr` |
| `DT_HASH` | `.hash` | `d_ptr` <- `sh_addr` |
| `DT_GNU_HASH` | `.gnu.hash` | `d_ptr` <- `sh_addr` |
| `DT_JMPREL` | `.rel.plt` or `.rela.plt` or `.rela.IA_64.pltoff` | `d_ptr` <- `sh_addr` |
| `DT_REL` | `.rel.dyn` or `.rel.got` | `d_ptr` <- `sh_addr` |
| `DT_RELA` | `.rela.dyn` | `d_ptr` <- `sh_addr` |
| `DT_VERNEED` | `.gnu.version_r` | `d_ptr` <- `sh_addr` |
| `DT_VERSYM` | `.gnu.version` | `d_ptr` <- `sh_addr` |
| `DT_MIPS_XHASH` | `.MIPS.xhash` | `d_ptr` <- `sh_addr` |
| `DT_MIPS_RLD_MAP_REL` | `.rld_map` | `d_ptr` <- relative offset |

### Symbol Table Section Index Remapping

When sections are reordered, the `st_shndx` field in `.dynsym` and
`.symtab` entries must be remapped from old section indices to new
ones.[^11] For `STT_SECTION` type symbols, `st_value` is also updated to
the new section address.[^12]

The old-to-new mapping is maintained via `sectionsByOldIndex`, populated
during ELF file construction.[^13]

### Section Header Cross-References

`sortShdrs()` preserves `sh_link` cross-references (translated to section
names before sorting, restored after) and `sh_info` for SHT_REL/SHT_RELA
sections. The `.shstrtab` index (`e_shstrndx`) is restored by matching on
`sh_offset`.[^14]

### String Table Null-Termination

The section header string table (`.shstrtab`) is validated for
null-termination on load.[^15] Note: `.dynstr` is *not* explicitly
validated for null-termination during loading, though patchelf maintains
it by always appending strings with explicit `'\0'` terminators when
growing `.dynstr`.[^16]

### Section Alignment

Replaced sections are aligned to `sectionAlignment`, which is
`sizeof(Elf_Off)` -- 4 bytes for ELF32, 8 bytes for ELF64.[^17] SHT_NOTE
sections preserve their original alignment if it's smaller than the default
section alignment.[^18]

### Virtual Address Space Bounds

For executables, inserting pages at the beginning shifts virtual addresses
backward. If the needed pages would push below virtual address 0, patchelf
raises "virtual address space underrun".[^19]

For libraries, new content is placed at a virtual address past the highest
existing segment, rounded up to the maximum segment alignment.[^20]

## Known Fragile Code

### Lost Rationale

The code contains several comments indicating the author no longer
remembers why certain logic exists:

- **"Why do we stop after a .dynstr section? I can't remember!"** -- In
  `rewriteSectionsExecutable()`, section replacement stops after
  encountering `.dynstr`. The rationale is lost.[^21]

- **"no idea if this makes sense, but it was needed for some program"** --
  DT_REL handling tries `.rel.dyn` then `.rel.got` as a fallback.[^22]

### Incomplete Fixes

- **Symbol st_value update**: Only `STT_SECTION` symbols get their
  `st_value` updated when sections move. The code has a FIXME noting this
  should be done for all types.[^23]

- **Endianness in getElfType()**: The `e_machine` field is read without
  endianness conversion, marked with `// FIXME: endianness`.[^24]

### Hardcoded Assumptions

- **"I'm lazy" assertion**: `assert(lastReplaced + 1 < shdrs.size())` in
  `rewriteSectionsExecutable()` assumes there's at least one non-replaced
  section after the last replaced one.[^25]

- **DT_STRTAB == .dynstr assumption**: The code assumes the virtual
  address in DT_STRTAB corresponds to the `.dynstr` section, which could
  be violated by unusual linker output.[^26]

- **Single split point in shiftFile()**: Only one PT_LOAD segment may
  straddle the insertion offset. This is asserted, not handled.[^27]

### Missing Endianness Conversion in noDefaultLib()

`noDefaultLib()` reads and writes `d_un.d_val` directly without `rdi()`/
`wri()` endianness conversion (lines 2000-2002, 2018).[^28b] Compare with
`addDebugTag()` (line 2017) which correctly uses `wri(newDyn.d_tag, ...)`.
This would produce incorrect results when cross-editing a big-endian
binary on a little-endian host (or vice versa). The same pattern of
missing endianness conversion appears in the new-entry path at line 2018:
`newDyn.d_un.d_val = DF_1_NODEFLIB` (should be
`wri(newDyn.d_un.d_val, DF_1_NODEFLIB)`).

### Compiler Workaround

The `rdi()` endianness conversion function is deliberately not inlined due
to a GCC code generation bug. The comment reads: "G++ creates broken code
if this function is inlined, don't know why".[^28]

## ET_EXEC vs ET_DYN: Two Strategies

Patchelf uses fundamentally different strategies for executables and shared
libraries:[^29]

| Aspect | ET_EXEC | ET_DYN |
|---|---|---|
| **Where new content goes** | Beginning of file (after ELF header + PHT) | End of file |
| **Growth mechanism** | `shiftFile()` inserts pages, pushing content forward | Appends to file, extends or adds PT_LOAD |
| **VA space management** | Shifts existing VAs backward; risks underrun near VA 0 | Adds new VA space past highest existing segment |
| **PHT location** | Always at `sizeof(Elf_Ehdr)`; hardcoded after shift | Prefers file start; relocates to end if immovable sections prevent growth |
| **Section replacement scope** | All replaceable sections before last replaced (stops at SHT_PROGBITS -- except `.interp` -- or after `.dynstr`)[^39] | Only sections whose offsets collide with the expanded PHT |
| **PT_LOAD manipulation** | Splits existing PT_LOAD via `shiftFile()` | Expands last PT_LOAD or creates new one |
| **SHT location** | May move to end of file if in the way | Always at end of file |
| **Binutils compat** | None needed | 1-byte padding for older `readelf`[^44] |

**Why the difference**: ET_EXEC uses fixed (absolute) virtual addresses, so
sections cannot be freely relocated -- their absolute addresses would
change, breaking hardcoded references. Patchelf works around this by
inserting space at the beginning and shifting existing content forward.
ET_DYN uses position-independent code with relative references, so
appending at the end with new VA mappings is safe.[^30]

### PHT Relocation for Libraries

For ET_DYN files, the program header table is preferably kept at the
beginning of the file. However, if the PHT has grown (e.g., from new
segments) and immovable SHT_PROGBITS sections block expansion, the PHT is
relocated to the end. This is noted as a compatibility concern: older Linux
kernels (pre-March 2022) had a bug preventing them from loading ELFs with
PHDRs not at the file start, fixed in commit
`0da1d5002745cdc721bc018b582a8a9704d56c42`.[^31]

## Operations That Risk Breaking Invariants

### shiftFile()

The most complex single operation. It:

1. Inserts `extraPages * pageSize` bytes at `startOffset` via `memmove`
2. Adjusts `e_shoff` and all section header offsets past the insertion point
3. **Splits** the PT_LOAD straddling `startOffset` -- the original
   segment's offset, vaddr, paddr, filesz, and memsz are adjusted to
   start at `startOffset` (keeping the post-split portion), and a new
   PT_LOAD is added for the pre-split portion[^32a]
4. Shifts virtual addresses backward for segments before the insertion
5. The new PT_LOAD gets hardcoded `PF_R | PF_W` flags regardless of the
   original segment's permissions[^32]

**Risk**: The hardcoded RW permissions on the new segment may change memory
protection semantics if the original was read-only.

### normalizeNoteSegments()

Breaks compound PT_NOTE segments (containing multiple SHT_NOTE sections)
into one PT_NOTE per section. This adds new program headers, increasing
`e_phnum`.[^33] The increased PHT size must be accommodated by the PT_LOAD
segment covering it.

Empty PT_NOTE segments (possibly from older patchelf versions) are silently
skipped for backward compatibility.[^34]

### Growing .dynstr and .dynamic Together

When adding a new RPATH or SONAME, both `.dynstr` (for the string) and
`.dynamic` (for the new DT entry) may need to grow in the same
operation.[^35] The `replaceSection` mechanism handles this via a map of
pending replacements, but the cascading size changes and the `setSubstr`
calls that shift `.dynamic` entries must stay within bounds.[^36]

### Hash Table Rebuilding

Two hash tables may be present and must be rebuilt when symbols are renamed:

- **`rebuildGnuHashTable()`** reorders symbols in `.dynsym` (to satisfy
  the GNU hash bucket-sorted ordering constraint), updates bloom filters,
  buckets, and chain tables, and remaps symbol indices in all relocation
  tables (SHT_REL and SHT_RELA).[^37] Because this reorders `.dynsym`,
  relocation table updates are mandatory -- if any section referencing
  symbol indices is missed, the binary will have corrupt relocations.

- **`rebuildHashTable()`** rebuilds the SYSV hash table (`.hash`) by
  recomputing bucket/chain entries from the current `.dynsym` names.[^37a]
  Unlike GNU hash, SYSV hash rebuilding does *not* reorder symbols and
  therefore does not require relocation table updates.

### RPATH String Sharing Detection

Before overwriting an old RPATH string, patchelf checks whether the string
is shared (referenced by multiple DT entries via `forAllStringReferences`).
If shared, the string is not overwritten and a new copy is appended
instead.[^38] When the string is not shared, it is tainted with `'X'`
characters (not zeroed).[^38a] If the sharing detection misses a
reference, overwriting the string could corrupt other dynamic entries.

### replaceNeeded() Cross-Table Updates

When replacing `DT_NEEDED` library names, patchelf also updates the
`vn_file` field in `.gnu.version_r` (version-needed) entries for the
replaced library.[^55] This cross-table update is significant: if the
version-needed table still references the old library name, the dynamic
linker may fail to find the required symbol versions.

### Old Section Clobbering

By default, `writeReplacedSections()` overwrites old section contents with
`'Z'` characters before writing new content.[^53] This prevents stale
data from being interpreted as valid. The `--no-clobber-old-sections` flag
disables this behavior, which is needed when the binary expects to find
section data at old locations.

### modifyExecstack() Strategies

`modifyExecstack()` uses three strategies in order of preference:[^49]

1. Modify the `PF_X` flag on an existing `PT_GNU_STACK` header
2. Repurpose a `PT_NULL` segment as `PT_GNU_STACK`
3. Add a new program header and call `rewriteSections(true)` to force
   a full section rewrite

**Bug**: Strategy 2 is effectively dead code. The variable `nullhdr` is
initialized to `(size_t)-1` (line 2305), and the detection condition at
line 2311 is `if (!nullhdr && type == PT_NULL)`. Since `(size_t)-1` is
nonzero (truthy), `!nullhdr` is always false, so a `PT_NULL` segment
will never be detected and repurposed.[^49a]

Strategy 3 is the most disruptive since it adds a program header and
triggers the full rewrite machinery even if no sections were otherwise
changed.

### Write Gating

The modified binary is only written to disk if the `changed` flag is true
or `--output` was specified (which sets `alwaysWrite`).[^60] Individual
operations set `changed = true` when they modify content.

Note: the `fileContents` parameter to `patchElf2` and
`elfFile.fileContents` are the same `shared_ptr<vector<unsigned char>>`
— in-place modifications to the buffer (e.g., `memset` for old section
clobbering) are reflected in both. The real distinction between the two
branches is that `isChanged()` is only true when `rewriteSections()` was
called, which triggers the full section rewriting machinery. The
`alwaysWrite` path writes the buffer regardless, which is useful for
`--output` when copying a file without modifications.[^60]

## Open Questions

- Why does `rewriteSectionsExecutable()` stop replacing sections after
  `.dynstr`? What would break if it continued?
- Is the `st_value` update for non-STT_SECTION symbols actually needed in
  practice? What binaries would break?
- Can `shiftFile()` ever need to split more than one PT_LOAD segment? The
  assertion says no, but is this guaranteed by all linkers?
- The `getElfType()` endianness FIXME -- has this caused real bugs on
  big-endian hosts modifying little-endian binaries?
- Are there DT_* tags not handled in `rewriteHeaders()` that contain
  section addresses and should be updated?
- `writeReplacedSections()` unconditionally sets `sh_addralign` to
  `sectionAlignment` for all replaced sections (line 709). Could this
  break sections that originally had larger alignment requirements?

## References

[^1]: `src/patchelf.cc`, lines 1184-1200, `rewriteSections()` dispatch.
[^2]: SCO, *System V Application Binary Interface*, Edition 4.1, 1997,
      Chapter 5, "Program Loading": "p_vaddr mod p_align = p_offset
      mod p_align."
      `https://refspecs.linuxbase.org/elf/gabi4+/ch5.pheader.html`
[^3]: `src/patchelf.cc`, line 1028:
      `assert(startAddr % getPageSize() == startOffset % getPageSize())`;
      line 931 in `rewriteSectionsLibrary`.
[^4]: `src/patchelf.cc`, lines 361-386, `getPageSize()`.
[^5]: `src/patchelf.cc`, line 568 (`getPageSize()` in executable path).
[^5a]: `src/patchelf.cc`, lines 814-821 (`alignStartPage` computation),
       line 930 (`alignStartPage` used for new PT_LOAD in library path).
[^6]: `src/patchelf.cc`, lines 541-546.
[^7]: `src/patchelf.cc`, lines 710-796 in `writeReplacedSections()`.
[^8]: SCO, *System V Application Binary Interface*, Edition 4.1, 1997,
      Chapter 5, "Program Header," PT_PHDR: "It may occur only if the
      program header table is itself part of the memory image. If it is
      present, it must precede any loadable segment entry."
      `https://refspecs.linuxbase.org/elf/gabi4+/ch5.pheader.html`
[^9]: `src/patchelf.cc`, lines 1086-1100.
[^10]: `src/patchelf.cc`, lines 1237-1318 in `rewriteHeaders()`.
[^11]: `src/patchelf.cc`, lines 1321-1347.
[^12]: `src/patchelf.cc`, lines 1341-1345, with FIXME comment.
[^13]: `src/patchelf.cc`, lines 354-356; `src/patchelf.h`, line 65.
[^14]: `src/patchelf.cc`, lines 399-445.
[^15]: `src/patchelf.cc`, lines 346-351.
[^16]: `src/patchelf.cc`, lines 1478 (`modifySoname`, `.dynstr`),
       1729 (`modifyRPath`, `.dynstr`), 1831 (`replaceNeeded`, `.dynstr`),
       1936 (`addNeeded`, `.dynstr`). Also line 1515 (`setInterpreter`,
       `.interp` — same pattern for a different section).
[^17]: `src/patchelf.h`, line 63.
[^18]: `src/patchelf.cc`, lines 744-746.
[^19]: `src/patchelf.cc`, lines 1075-1076.
[^20]: `src/patchelf.cc`, lines 812-823.
[^21]: `src/patchelf.cc`, lines 1008-1011.
[^22]: `src/patchelf.cc`, lines 1270-1278.
[^23]: `src/patchelf.cc`, lines 1341-1342.
[^24]: `src/patchelf.cc`, line 237.
[^25]: `src/patchelf.cc`, line 1000.
[^26]: `src/patchelf.cc`, lines 1608-1609.
[^27]: `src/patchelf.cc`, line 524.
[^28]: `src/patchelf.cc`, lines 111-112.
[^29]: `src/patchelf.cc`, lines 1193-1199.
[^30]: SCO, *System V Application Binary Interface*, Edition 4.1, 1997,
      Chapter 5, "Program Header": "Shared object segments [...] the
      difference between the virtual address of any segment in memory and
      the corresponding virtual address in the file is thus a single
      constant." ET_EXEC uses absolute virtual addresses assigned by the
      static linker; ET_DYN uses position-independent addressing.
      `https://refspecs.linuxbase.org/elf/gabi4+/ch5.pheader.html`
[^31]: `src/patchelf.cc`, lines 844-847. Linux kernel commit
      `0da1d5002745cdc721bc018b582a8a9704d56c42` (2022-03-02).
[^32]: `src/patchelf.cc`, line 567.
[^33]: `src/patchelf.cc`, lines 1116-1180.
[^34]: `src/patchelf.cc`, lines 1136-1140.
[^35]: E.g., `modifySoname()`, lines 1474-1499; `modifyRPath()`,
      lines 1724-1757.
[^36]: `src/patchelf.cc`, line 1354, `setSubstr()` assertion.
[^37]: `src/patchelf.cc`, lines 2076-2183
       (`rebuildGnuHashTable()`), 2144-2152 (relocation remapping).
[^37a]: `src/patchelf.cc`, lines 2208-2231
        (`rebuildHashTable()`). Both are called from
        `renameDynamicSymbols()` at lines 2265-2266.
[^38]: `src/patchelf.cc`, lines 1693-1713.
[^39]: `src/patchelf.cc`, line 1010: the condition is
       `(rdi(shdr.sh_type) == SHT_PROGBITS && sectionName != ".interp")`.
       `.interp` is SHT_PROGBITS but is explicitly exempted because it
       must be replaceable (for `--set-interpreter`).
[^32a]: `src/patchelf.cc`, lines 530-534 (original segment adjusted),
        lines 558-568 (new PT_LOAD for pre-split portion).
[^49]: `src/patchelf.cc`, lines 2302-2378, `modifyExecstack()`.
[^53]: `src/patchelf.cc`, lines 676-686 in `writeReplacedSections()`.
       Controlled by `clobberOldSections` flag (line 61), toggled by
       `--no-clobber-old-sections` (line 2722).
[^55]: `src/patchelf.cc`, lines 1852-1911 in `replaceNeeded()`.
       Iterates `.gnu.version_r` entries and updates `vn_file` for
       replaced libraries.
[^60]: `src/patchelf.cc`, lines 2501-2506 in `patchElf2()`.
       `elfFile.isChanged()` gates the write; `alwaysWrite` overrides.
       Both code paths write the same underlying buffer (same
       `shared_ptr`); the distinction is whether `rewriteSections()` was
       called (which modifies the buffer in-place via
       `writeReplacedSections()`).
[^7a]: PT_PHDR synchronization occurs in `rewriteHeaders()` at lines
       1210-1217, not in `writeReplacedSections()`. It is listed in this
       table for completeness but is handled in a different function than
       the other entries.
[^38a]: `src/patchelf.cc`, lines 1711-1713:
        `memset(rpath, 'X', rpathSize)`. The 'X' tainting prevents
        retained dependencies in Nix (per the comment at line 1709).
[^44]: `src/patchelf.cc`, line 894:
       `off_t binutilsQuirkPadding = 1;` with comment at lines 892-893
       explaining older binutils `readelf` (2.30) would check if the
       dynamic section segment is strictly smaller than the file.
[^28b]: `src/patchelf.cc`, lines 2000-2002: `dynFlags1->d_un.d_val`
        accessed without `rdi()`; line 2018: `newDyn.d_un.d_val =
        DF_1_NODEFLIB` without `wri()`. Compare with line 2017:
        `wri(newDyn.d_tag, DT_FLAGS_1)` which correctly uses `wri()`.
[^49a]: `src/patchelf.cc`, line 2305: `size_t nullhdr = (size_t)-1;`
        and line 2311: `if (!nullhdr && type == PT_NULL)`. Since
        `(size_t)-1` is the maximum value of `size_t` (nonzero),
        `!nullhdr` is always false. This appears to be a bug -- the
        intent was likely `if (nullhdr == (size_t)-1 && type == PT_NULL)`.
