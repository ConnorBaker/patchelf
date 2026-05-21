# ELF Dynamic Linking

This document describes the mechanics of dynamic linking in ELF: the
.dynamic section, program header types, string and symbol tables, hash
tables, and the end-to-end loading process. Understanding these mechanics
is essential for reasoning about what patchelf may safely modify.

## Sections vs. Segments: The Dual-View Architecture

An ELF file provides two parallel views of the same underlying data:[^1]

- **Section headers** (`Elf_Shdr`): The *linking view*. Located via
  `e_shoff` in the ELF header. Sections are logical divisions (`.text`,
  `.data`, `.dynstr`, `.dynamic`, etc.) used by linkers, debuggers, and
  tools like patchelf. Section headers are **optional at runtime** -- the
  ELF header's `e_shoff` field "holds zero if the file has no section
  header table,"[^1a] and a stripped executable can run without them.

- **Program headers** (`Elf_Phdr`): The *execution view*. Located via
  `e_phoff` in the ELF header. Segments are physical groupings for memory
  mapping, used by the kernel and dynamic linker. A single segment
  typically contains multiple sections.

One or more sections are grouped into a segment. For example, a single
PT_LOAD segment with read+execute permissions might contain `.text`,
`.plt`, and `.eh_frame`. (Note: with modern linker defaults like
`-z separate-code`, `.rodata` is typically placed in a separate read-only
PT_LOAD segment.)[^2] Only PT_LOAD segments cause the kernel to `mmap` file content into
memory. In practice, segments that carry data (PT_DYNAMIC, PT_INTERP,
PT_NOTE, etc.) reside within the address range of some PT_LOAD segment,
though this is implementation convention rather than a formal spec
requirement.[^2][^3] Note that metadata-only segments like PT_GNU_STACK
(which has `p_vaddr = 0`, `p_memsz = 0`) have no address range and do
not reside within any PT_LOAD.

**Implication for patchelf**: Patchelf operates primarily on the section
view but must keep the segment view consistent. When a section is moved,
any segment that references it (directly or by address range) must be
updated.

## PT_LOAD Segments

PT_LOAD segments describe how file content is mapped into process
memory.[^4]

### Program Header Fields

| Field | Meaning |
|---|---|
| `p_offset` | File offset of segment start |
| `p_vaddr` | Virtual address where segment is loaded |
| `p_paddr` | Physical address (reserved, unused for applications) |
| `p_filesz` | Bytes in the file image (may be 0) |
| `p_memsz` | Bytes in the memory image (may be 0) |
| `p_flags` | Permission flags: `PF_R` (read), `PF_W` (write), `PF_X` (execute) |
| `p_align` | Alignment for both file and memory |

### Alignment Congruence

The most critical invariant for PT_LOAD segments:[^5]

```
p_vaddr % p_align == p_offset % p_align
```

This ensures that when segments are `mmap`'d, the relative offset within a
page is consistent between file and memory. Typically `p_align` is the
system page size (4096) or a larger power of 2.

### BSS Handling

When `p_memsz > p_filesz`, the extra bytes are zero-initialized. This is
how `.bss` (uninitialized data) works. For PT_LOAD segments, the spec
requires that "the file size may not be larger than the memory size"
(`p_filesz <= p_memsz`).[^6] This constraint is specific to PT_LOAD
segments, not a universal invariant for all segment types.

### Ordering

The gABI spec states that "loadable segment entries in the program header
table appear in ascending order, sorted on the `p_vaddr` member."[^7]
(Note: the spec uses descriptive language rather than normative "must,"
but all conforming implementations treat this as a requirement.)

### Base Address

For position-independent executables and shared libraries, the base address
is calculated from the lowest `p_vaddr` among all PT_LOAD segments,
truncated to the nearest page boundary. This base is used for ASLR-adjusted
relocation.[^8]

## PT_INTERP

Specifies the path to the dynamic linker (interpreter).[^9]

The kernel's `load_elf_binary()` scans program headers for PT_INTERP. When
found, it reads the null-terminated path (typically
`/lib64/ld-linux-x86-64.so.2` on x86-64 Linux), opens the interpreter as
another ELF file, maps its PT_LOAD segments, and sets the execution entry
point to the **interpreter's** entry point, not the program's. The
program's actual entry point is communicated to the interpreter via the
`AT_ENTRY` auxiliary vector value.[^10]

Constraints: may occur at most once; the PT_INTERP program header entry
must precede any loadable segment entry in the program header table array
(this constrains header ordering, not the file offset of the interpreter
path string); only meaningful for executable files.[^9]

## PT_PHDR

A self-referential entry describing the location and size of the program
header table itself, both in the file and in memory.[^11]

This makes the program header table accessible to the dynamic linker at
runtime. The kernel also communicates the program header location via
auxiliary vector entries: `AT_PHDR` (address), `AT_PHENT` (entry size),
`AT_PHNUM` (count).[^12]

Constraints: may occur at most once; may only appear if the program header
table is part of the memory image; must precede any PT_LOAD segment.[^11]

## The .dynamic Section

The `.dynamic` section (type `SHT_DYNAMIC`) contains an array of `Elf_Dyn`
structures. Each has a `d_tag` (type) and a `d_un` union containing either
`d_val` (integer value) or `d_ptr` (virtual address). The array is
terminated by a `DT_NULL` entry. At runtime, the dynamic linker locates it
via the `PT_DYNAMIC` program header segment.[^13]

### Standard Tags (gABI)

| Tag | Value | d_un | Meaning |
|---|---|---|---|
| `DT_NULL` | 0 | ignored | End of `_DYNAMIC` array |
| `DT_NEEDED` | 1 | d_val | String table offset: name of a needed shared library |
| `DT_PLTRELSZ` | 2 | d_val | Total size in bytes of PLT relocation entries |
| `DT_PLTGOT` | 3 | d_ptr | Address of PLT and/or GOT |
| `DT_HASH` | 4 | d_ptr | Address of SYSV symbol hash table |
| `DT_STRTAB` | 5 | d_ptr | Address of `.dynstr` |
| `DT_SYMTAB` | 6 | d_ptr | Address of `.dynsym` |
| `DT_RELA` | 7 | d_ptr | Address of relocation table with explicit addends |
| `DT_RELASZ` | 8 | d_val | Size of `DT_RELA` table |
| `DT_RELAENT` | 9 | d_val | Size of one `DT_RELA` entry |
| `DT_STRSZ` | 10 | d_val | Size of string table |
| `DT_SYMENT` | 11 | d_val | Size of one symbol table entry |
| `DT_INIT` | 12 | d_ptr | Address of initialization function |
| `DT_FINI` | 13 | d_ptr | Address of termination function |
| `DT_SONAME` | 14 | d_val | String table offset: this object's name |
| `DT_RPATH` | 15 | d_val | String table offset: library search path (**superseded** by `DT_RUNPATH`; "level 2" in the gABI, meaning optional/obsolescent)[^13b] |
| `DT_SYMBOLIC` | 16 | ignored | Alters symbol resolution (superseded by `DF_SYMBOLIC`) |
| `DT_REL` | 17 | d_ptr | Address of relocation table with implicit addends |
| `DT_RELSZ` | 18 | d_val | Size of `DT_REL` table |
| `DT_RELENT` | 19 | d_val | Size of one `DT_REL` entry |
| `DT_PLTREL` | 20 | d_val | Type of PLT relocations (`DT_REL` or `DT_RELA`) |
| `DT_DEBUG` | 21 | d_ptr | Used for debugging; value unspecified by ABI |
| `DT_TEXTREL` | 22 | ignored | Indicates relocations in non-writable segments |
| `DT_JMPREL` | 23 | d_ptr | Address of PLT relocation entries |
| `DT_BIND_NOW` | 24 | ignored | Resolve all relocations before execution |
| `DT_INIT_ARRAY` | 25 | d_ptr | Array of initialization function pointers |
| `DT_FINI_ARRAY` | 26 | d_ptr | Array of termination function pointers |
| `DT_INIT_ARRAYSZ` | 27 | d_val | Size of `DT_INIT_ARRAY` |
| `DT_FINI_ARRAYSZ` | 28 | d_val | Size of `DT_FINI_ARRAY` |
| `DT_RUNPATH` | 29 | d_val | String table offset: library search path (replaces `DT_RPATH`) |
| `DT_FLAGS` | 30 | d_val | Object-specific flags |
| `DT_PREINIT_ARRAY` | 32 | d_ptr | Array of pre-initialization function pointers (executables only)[^13a] |
| `DT_PREINIT_ARRAYSZ` | 33 | d_val | Size of `DT_PREINIT_ARRAY` |

### GNU/OS-Specific Tags

| Tag | Value | Meaning |
|---|---|---|
| `DT_GNU_HASH` | 0x6ffffef5 | Address of GNU hash table |
| `DT_VERSYM` | 0x6ffffff0 | Address of symbol version table |
| `DT_RELACOUNT` | 0x6ffffff9 | Count of RELATIVE relocations |
| `DT_RELCOUNT` | 0x6ffffffa | Count of RELATIVE relocations |
| `DT_FLAGS_1` | 0x6ffffffb | Extended flags (see below) |
| `DT_VERNEED` | 0x6ffffffe | Address of version requirements table |
| `DT_VERNEEDNUM` | 0x6fffffff | Number of version need entries |

### DT_FLAGS (DF_*) Values

| Flag | Value | Meaning |
|---|---|---|
| `DF_ORIGIN` | 0x1 | Object may use `$ORIGIN` substitution |
| `DF_SYMBOLIC` | 0x2 | Symbol resolution starts with this object |
| `DF_TEXTREL` | 0x4 | Text relocations may exist |
| `DF_BIND_NOW` | 0x8 | All relocations processed at load time |
| `DF_STATIC_TLS` | 0x10 | Object uses static TLS model |

### DT_FLAGS_1 (DF_1_*) Values

| Flag | Value | Meaning |
|---|---|---|
| `DF_1_NOW` | 0x00000001 | Complete relocation at load |
| `DF_1_GLOBAL` | 0x00000002 | Set RTLD_GLOBAL |
| `DF_1_GROUP` | 0x00000004 | Member of a group |
| `DF_1_NODELETE` | 0x00000008 | Cannot be dlclose'd |
| `DF_1_LOADFLTR` | 0x00000010 | Trigger immediate filtee loading |
| `DF_1_INITFIRST` | 0x00000020 | Initialize before other objects |
| `DF_1_NOOPEN` | 0x00000040 | Cannot be dlopen'd |
| `DF_1_ORIGIN` | 0x00000080 | `$ORIGIN` processing required |
| `DF_1_DIRECT` | 0x00000100 | Direct binding enabled |
| `DF_1_INTERPOSE` | 0x00000400 | Object is an interposer |
| `DF_1_NODEFLIB` | 0x00000800 | Ignore default library search paths |
| `DF_1_NODUMP` | 0x00001000 | Object cannot be dumped |
| `DF_1_PIE` | 0x08000000 | Position-Independent Executable |

### Tags Patchelf Manipulates

From `src/patchelf.cc`:[^14]

- **Adds/removes/replaces**: `DT_NEEDED`, `DT_SONAME`, `DT_RPATH`,
  `DT_RUNPATH`, `DT_FLAGS_1`, `DT_DEBUG`
- **Updates addresses after section moves**: `DT_STRTAB`, `DT_STRSZ`,
  `DT_SYMTAB`, `DT_HASH`, `DT_GNU_HASH`, `DT_JMPREL`, `DT_REL`,
  `DT_RELA`, `DT_VERNEED`, `DT_VERSYM`, `DT_MIPS_XHASH`,
  `DT_MIPS_RLD_MAP_REL`

## String Tables

String tables (`.dynstr`, `.strtab`, `.shstrtab`) hold null-terminated
strings referenced by index (byte offset).[^15]

- Index 0 is always a null byte, representing the empty string
- The last byte must be null
- `.dynstr` serves dynamic linking: `DT_NEEDED` names, `DT_SONAME`,
  `DT_RPATH`/`DT_RUNPATH` values, and symbol names for `.dynsym`
- `.strtab` serves static linking and debugging
- `.shstrtab` holds section names
- Located at runtime via `DT_STRTAB` (address) and `DT_STRSZ` (size)

**Implication for patchelf**: When strings need to grow (new RPATH, new
SONAME, etc.), the entire `.dynstr` section must be replaced with a larger
copy and `DT_STRTAB`/`DT_STRSZ` updated.

## Symbol Tables

`.dynsym` (type `SHT_DYNSYM`) holds the minimal symbol set for dynamic
linking; `.symtab` (type `SHT_SYMTAB`) holds the complete symbol table
(often stripped). Located at runtime via `DT_SYMTAB`.[^16]

Each `Elf_Sym` entry contains:

| Field | Meaning |
|---|---|
| `st_name` | Index into associated string table |
| `st_info` | Binding (`STB_LOCAL`/`GLOBAL`/`WEAK`) and type (`STT_NOTYPE`/`OBJECT`/`FUNC`/`SECTION`/`FILE`) |
| `st_other` | Visibility (`STV_DEFAULT`/`HIDDEN`/`PROTECTED`) |
| `st_shndx` | Section index where symbol is defined |
| `st_value` | Symbol value (address) |
| `st_size` | Symbol size |

## Hash Tables

### SYSV Hash (DT_HASH)

Structure: `{ nbucket, nchain, bucket[nbucket], chain[nchain] }`.[^17]

Lookup: compute `hash(name) % nbucket` to get the first symbol index from
`bucket[]`, then follow `chain[]` entries until a match is found or
`STN_UNDEF` is reached. The gABI spec states "the number of symbol table
entries should equal `nchain`"[^17] (using "should," not "shall").
Note: patchelf's `rebuildHashTable()` does not read `nchain` directly
but infers the chain size from the remaining section data, handling the
case where `nchain` does not equal the total `.dynsym` count.[^17a]

### GNU Hash (DT_GNU_HASH)

Structure: header (`nbuckets`, `symndx`, `maskwords`, `shift2`), followed
by a Bloom filter, bucket array, and chain/value array.[^18]

The GNU hash uses the DJB2 hash function: `h = ((h << 5) + h) + c`,
starting with 5381.[^19] It imposes an ordering constraint on `.dynsym`:
symbols included in the hash table (those at index >= `symndx`) must be
grouped by bucket. A Bloom filter provides fast rejection of missing
symbols, making lookups significantly faster than SYSV hash.

The Bloom filter uses words of size `ElfClass` (32 or 64 bits). For each
symbol, two bits are set in the filter using the hash value and a shifted
version (`h >> shift2`).[^18]

**Implication for patchelf**: When symbols are renamed or reordered,
patchelf must rebuild both hash tables (if present) and reorder the
`.dynsym` entries to satisfy the GNU hash ordering constraint. This
also requires updating all relocation tables that reference symbol
indices.

## Library Search Order

When resolving a `DT_NEEDED` entry (without a `/` in the name), the
dynamic linker searches in this order:[^20]

1. Directories from `DT_RPATH` of the requesting object, **only if
   `DT_RUNPATH` is absent**. When `DT_RPATH` is present in the main
   executable, it is used when searching for any library in the
   dependency tree. (Note: the `ld.so(8)` man page describes this as
   searching "the DT_RPATH ... of the binary"; the common claim that
   DT_RPATH in *any* shared library applies to the entire tree is a
   simplification.)[^20]
2. `LD_LIBRARY_PATH` environment variable (ignored in secure-execution
   mode for setuid/setgid binaries).
3. Directories from `DT_RUNPATH` of the requesting object. Scoped: only
   applies to direct `DT_NEEDED` dependencies, not transitive ones.
4. `/etc/ld.so.cache` (precompiled cache from `ldconfig`).
5. Default paths: `/lib` and `/usr/lib` (or `/lib64`, `/usr/lib64` on
   64-bit), unless `DF_1_NODEFLIB` is set.

**DT_RPATH vs DT_RUNPATH**: `DT_RPATH` (tag 15) is superseded by
`DT_RUNPATH` (see [^13b] for the gABI's exact terminology). `DT_RUNPATH`
(tag 29) supersedes it with two key differences: (a) it can be overridden
by `LD_LIBRARY_PATH`, and (b) it is scoped to direct dependencies only.
If both are present, `DT_RPATH` is ignored. Patchelf converts `DT_RPATH`
to `DT_RUNPATH` by default unless `--force-rpath` is specified.[^21]

## The ELF Loading Process

The complete sequence from `execve()` to program execution:[^22]

1. **`execve()` syscall**: Kernel's `load_elf_binary()` reads the ELF
   header, validates magic bytes `\x7fELF`.
2. **Program headers**: Kernel reads the complete program header table.
3. **PT_INTERP check**: Kernel scans for PT_INTERP to determine if dynamic
   linking is needed.
4. **Process cleanup**: `flush_old_exec()` kills threads, releases old
   mappings; `setup_new_exec()` updates credentials and `/proc/pid/exe`.
5. **Stack setup**: Stack is randomized (ASLR), `setup_arg_pages()`
   configures memory tracking.[^22b]
6. **PT_LOAD mapping**: Kernel maps PT_LOAD segments into the new address
   space via `elf_map()` (a kernel-internal wrapper around `vm_mmap()`
   in `fs/binfmt_elf.c`). BSS regions are zeroed.
7. **Interpreter loading**: If PT_INTERP was found, kernel opens the
   interpreter ELF, maps its PT_LOAD segments via `load_elf_interp()`.
8. **Auxiliary vector**: `create_elf_tables()` builds the auxiliary vector
   on the stack with `AT_PHDR`, `AT_PHENT`, `AT_PHNUM`, `AT_ENTRY`,
   `AT_BASE`, `AT_RANDOM` (16 bytes of randomness[^22c]), `AT_EXECFN`,
   `AT_SYSINFO_EHDR`.
9. **Control transfer**: Execution begins at the **interpreter's** entry
   point.
10. **ld.so self-relocation**: Dynamic linker resolves its own relocations.
11. **ld.so processes program**: Uses `AT_PHDR` to find program headers,
    locates `PT_DYNAMIC`, reads all DT_* entries.
12. **Dependency resolution**: Recursively processes `DT_NEEDED`, searching
    via the library search order above.
13. **Symbol resolution and relocation**: Processes `DT_REL`/`DT_RELA`/
    `DT_JMPREL`, resolves symbols via hash tables + symbol tables + string
    tables. Symbol version checking (`DT_VERSYM`/`DT_VERNEED`) occurs
    during symbol resolution, not as a separate pass.[^22a]
14. **RELRO protection**: If a `PT_GNU_RELRO` segment is present, ld.so
    calls `mprotect()` on the RELRO region to make it read-only. With
    partial RELRO, this protects `.got` and `.dynamic` but not
    `.got.plt`. With full RELRO (`DF_BIND_NOW`/`DF_1_NOW` set),
    `.got.plt` is also in the RELRO region since lazy binding is
    disabled. See
    [02-gnu-extensions.md](02-gnu-extensions.md#relro-relocation-read-only)
    for details.
15. **Initialization**: Calls constructors (`DT_INIT`, `DT_INIT_ARRAY`) in
    dependency order, respecting `DF_1_INITFIRST`.
16. **Jump to program**: ld.so jumps to the address from `AT_ENTRY`;
    program's `_start` begins.

## Open Questions

- How does `DT_RELR` (relative relocations, added in gABI v4.3 draft)
  interact with patchelf's section rewriting? Patchelf does not currently
  handle `DT_RELR`. See
  [05-edge-cases-and-gaps.md](05-edge-cases-and-gaps.md#relr-relocations--critical-gap)
  for detailed analysis of this critical gap.
- What happens when `DT_STRTAB` points to a virtual address that doesn't
  correspond to `.dynstr`'s section header? Patchelf assumes they match.
- Are there `DT_*` tags with embedded addresses that patchelf's
  `rewriteHeaders()` does not update? If so, binaries using those tags
  would be silently corrupted.
- How do `DT_PREINIT_ARRAY` / `DT_PREINIT_ARRAYSZ` interact with
  patchelf? These are standard gABI tags (values 32/33) not currently
  handled.
- **TLS (Thread-Local Storage)**: This document does not cover TLS
  mechanics (`DT_TLSDESC`, `PT_TLS` (value 7, a standard gABI segment
  type), or the static/dynamic TLS models). TLS interacts with both the
  kernel loader and the dynamic linker and may affect patchelf
  correctness. See [05-edge-cases-and-gaps.md](05-edge-cases-and-gaps.md)
  for TLS risks.
- **PLT/GOT lazy binding mechanics** (PLT stub -> GOT entry -> resolver ->
  patch GOT) are referenced but not explained in detail. A future revision
  should describe how `DT_JMPREL`, `DT_PLTGOT`, and `DT_PLTREL` interact
  with lazy vs eager binding.
- The gABI spec permits **empty string tables** (`sh_size == 0`) and
  explicitly states that non-zero indexes are invalid for them. The spec
  also permits **substring sharing** within string tables (e.g.,
  "libfoo.so" contains "foo.so" at a higher offset). Neither property is
  currently exploited or validated by patchelf.
- **PT_GNU_RELRO**, **PT_GNU_STACK**, **PT_GNU_EH_FRAME**, and
  **PT_GNU_PROPERTY** are covered in
  [02-gnu-extensions.md](02-gnu-extensions.md) but not cross-referenced
  here. These segment types are relevant to the loading process
  description above.

## References

[^1]: TIS Committee, *TIS ELF Specification, Version 1.2*, May 1995,
      Book I, Chapter 1.
      `https://refspecs.linuxfoundation.org/elf/elf.pdf`

[^2]: Intezer, "ELF 101 Part 1: Sections and Segments."
      `https://intezer.com/blog/executable-and-linkable-format-101-part-1-sections-and-segments/`

[^3]: Oracle, *Linker and Libraries Guide*, "Program Header."
      `https://docs.oracle.com/cd/E19683-01/816-1386/chapter6-83432/index.html`

[^4]: gABI, Chapter 5, "Program Header," `PT_LOAD`.
      `https://refspecs.linuxbase.org/elf/gabi4+/ch5.pheader.html`

[^5]: Ibid. "As 'Loadable segment entries in the program header table
      appear in ascending order, sorted on the p_vaddr member' and
      'p_vaddr mod p_align = p_offset mod p_align'."

[^6]: Ibid. "If the segment's memory size (p_memsz) is larger than the
      file size (p_filesz), the 'extra' bytes are defined to hold the
      value 0."

[^7]: Ibid. "Loadable segment entries [...] appear in ascending order,
      sorted on the p_vaddr member."

[^8]: Oracle, *Linker and Libraries Guide*, "Program Header," base address
      calculation.

[^9]: gABI, Chapter 5, "Program Header," `PT_INTERP`.

[^10]: Linux kernel source, `fs/binfmt_elf.c`, `load_elf_binary()`.
       `https://github.com/torvalds/linux/blob/master/fs/binfmt_elf.c`;
       LWN.net, "How programs get run: ELF binaries."
       `https://lwn.net/Articles/631631/`

[^11]: gABI, Chapter 5, "Program Header," `PT_PHDR`.

[^12]: Manu Garg, "About ELF Auxiliary Vectors."
       `https://articles.manugarg.com/aboutelfauxiliaryvectors.html`

[^13]: gABI, Chapter 5, "Dynamic Section."
       `https://refspecs.linuxbase.org/elf/gabi4+/ch5.dynamic.html`

[^13b]: gABI, Chapter 5, "Dynamic Section": "This entry is at level 2.
        Its use has been superseded by DT_RUNPATH." Note: the gABI uses
        "superseded," not "deprecated" -- these terms have different
        connotations.

[^13a]: gABI, Chapter 5, "Dynamic Section": "The `DT_PREINIT_ARRAY`
        table is processed only in an executable file; it is ignored if
        contained in a shared object." Value 32 is shared with
        `DT_ENCODING`, a marker value for d_un interpretation rules.

[^14]: `src/patchelf.cc`, lines 1237-1318 (`rewriteHeaders`) and
       lines 2446-2499 (`patchElf2`).

[^15]: gABI, Chapter 4, "String Table."
       `https://www.sco.com/developers/gabi/latest/ch4.strtab.html`

[^16]: gABI, Chapter 4, "Symbol Table"; `elf(5)` man page.
       `https://man7.org/linux/man-pages/man5/elf.5.html`

[^17]: flapenguin, "About ELF DT_HASH."
       `https://flapenguin.me/elf-dt-hash`

[^17a]: `src/patchelf.cc`, lines 2198-2231, `rebuildHashTable()`.
        Line 2203 computes chain size from section data rather than
        reading the `nchain` header field; line 2220 computes
        `firstSymIdx = dynsyms.size() - ht.m_chain.size()`.

[^18]: flapenguin, "About ELF DT_GNU_HASH."
       `https://flapenguin.me/elf-dt-gnu-hash`

[^19]: The DJB2 hash function is widely attributed to Daniel J. Bernstein
       via a post to comp.lang.c in the early 1990s (commonly cited as
       1991, though the original post has not been independently
       located). See `http://www.cse.yorku.ca/~oz/hash.html` for the
       canonical secondary reference. The GNU hash table was implemented
       by Jakub Jelinek in a binutils patch posted June 28, 2006:
       `https://sourceware.org/legacy-ml/binutils/2006-06/msg00418.html`

[^20]: `ld.so(8)` man page.
       `https://man7.org/linux/man-pages/man8/ld.so.8.html`

[^21]: `src/patchelf.cc`, lines 1614-1686, `modifyRPath()`.

[^22]: Linux kernel `fs/binfmt_elf.c`; LWN.net, "How programs get run:
       ELF binaries," `https://lwn.net/Articles/631631/`;
       LWN.net, "A look at dynamic linking,"
       `https://lwn.net/Articles/961117/`.

[^1a]: gABI, Chapter 4, "ELF Header," `e_shoff` field definition.
       `https://www.sco.com/developers/gabi/latest/ch4.eheader.html`

[^22a]: In glibc's `ld.so`, version checking is performed during symbol
        lookup (in `_dl_lookup_symbol_x` via `check_match()`), not as a
        separate post-resolution pass. See glibc source `elf/dl-lookup.c`.

[^22b]: Per the LWN article cited in [^22], `setup_arg_pages()` occurs
        before the PT_LOAD mapping loop in `load_elf_binary()`. The
        kernel sets up the stack region before mapping the executable's
        segments.

[^22c]: `getauxval(3)` man page: "The address of sixteen bytes containing
        a random value."
        `https://man7.org/linux/man-pages/man3/getauxval.3.html`
