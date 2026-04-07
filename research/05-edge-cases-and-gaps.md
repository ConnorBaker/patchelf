# ELF Edge Cases and Patchelf Gaps

This document catalogs ELF features and edge cases that are relevant to
patchelf correctness but are not (or insufficiently) handled by the
current implementation. These represent risks for the Lean 4 rewrite and
potential sources of the historical correctness issues in Nixpkgs.

## ELF Note Sections

### Binary Format

Note entries have a 12-byte header followed by variable-length name and
descriptor fields:[^1]

```
+----------+----------+----------+
| n_namesz | n_descsz |  n_type  |   (each Elf32_Word = 4 bytes, even on 64-bit)
+----------+----------+----------+
|        name (n_namesz bytes, null-terminated)         |
|        padding to alignment boundary                  |
+-------------------------------------------------------+
|        descriptor (n_descsz bytes)                    |
|        padding to alignment boundary                  |
+-------------------------------------------------------+
```

Critically, **both 32-bit and 64-bit note headers use 4-byte (`uint32_t`)
words** for the header fields. The header is always 12 bytes regardless
of ELF class.[^1]

### The 4-byte vs 8-byte Alignment Conflict

There is a well-documented conflict between the gABI specification and
GNU/Linux practice:[^2]

- The **gABI spec** says 64-bit objects use 8-byte alignment for note
  entries; 32-bit use 4-byte.[^3]
- **GNU/Linux practice** (since the 1990s) uses 4-byte alignment
  unconditionally, even for 64-bit.[^4]

This was discussed on the generic-abi mailing list in Q4 2017 by H.J. Lu,
Ali Bahrami (Oracle/Solaris), and Mark Wielaard (Red Hat/elfutils).[^5] Key findings:

- HP-UX used true 8-byte note headers; Linux, Solaris, and NetBSD all
  used 4-byte words even in 64-bit note headers.[^5]
- Changing existing notes was deemed impossible due to the volume of
  deployed code.[^5]
- The practical resolution was a dual approach: existing GNU notes
  (ABI tag, build ID) remain 4-byte aligned forever; new note types
  (like `NT_GNU_PROPERTY_TYPE_0`) may use 8-byte alignment.[^5]
- Parsers should use `p_align` (of PT_NOTE) or `sh_addralign` (of
  SHT_NOTE) to determine alignment, not the ELF class.[^6]

The gABI spec text (as of the September 2025 Xinuos draft) still says
"8-byte words" for 64-bit, contradicting universal GNU/Linux practice.[^3]

**Patchelf interaction**: Patchelf preserves `sh_addralign` for note
sections when it differs from the default section alignment, which
correctly respects whichever convention the binary was produced with.[^7]
However, patchelf does not validate that note content padding matches
`sh_addralign`, which could matter if notes are corrupted.

### PT_NOTE and SHT_NOTE Relationship

One PT_NOTE segment can contain multiple contiguous SHT_NOTE sections.
The linker maps contiguous note sections into a single PT_NOTE. However,
**mixing different alignments within one PT_NOTE is problematic**: if a
segment contains 4-byte aligned notes followed by an 8-byte aligned note,
consumers may fail to parse the latter due to incorrect padding
assumptions.[^8]

Modern linkers address this: LLD groups SHT_NOTE sections by alignment
into separate PT_NOTE segments and sorts by decreasing alignment.[^8]

Patchelf's `normalizeNoteSegments()` breaks compound PT_NOTE segments
into one-per-section, eliminating the mixed-alignment problem within a
segment.[^9]

## dlopen Metadata (`.note.dlopen`)

### Motivation

Turning hard library dependencies (`DT_NEEDED`) into `dlopen()`
dependencies hides them from package managers. A binary may require
`libfoo.so` at runtime but have no `DT_NEEDED` entry for it, causing
packaging tools to miss the dependency. The XZ backdoor incident (2024)
catalyzed interest in making `dlopen()` dependencies discoverable.[^10]

### Specification

Proposed by Lennart Poettering (systemd project) in April 2024 via
systemd PR #32234, merged May 8, 2024.[^10] Now formally maintained as
**UAPI.12** by the UAPI Group.[^11]

| Property | Value |
|---|---|
| Section name | `.note.dlopen` |
| Note type | `0x407c0c0a` |
| Owner string | `FDO` (FreeDesktop.org) |
| Alignment | 4-byte |

The descriptor is a JSON array encoded as a zero-terminated UTF-8 string:

```json
[
    {
        "soname":      ["libfoo.so.1"],
        "feature":     "foo",
        "description": "Enables the foo feature",
        "priority":    "recommended"
    }
]
```

Fields:[^11]

| Key | Type | Mandatory | Description |
|---|---|---|---|
| `soname` | array of strings | yes | Library names loaded via `dlopen()`. Multiple = alternatives (OR). |
| `feature` | string | no | Feature keyword. Same feature across entries = all required (AND). |
| `description` | string | no | Human-readable description. |
| `priority` | string | no | `"required"`, `"recommended"` (default), or `"suggested"`. |

### Adoption

- **systemd**: Implemented tree-wide for all `dlopen()` calls (May 2024).[^10]
- **Debian**: debhelper plugin via `systemd/package-notes` for automatic
  dependency generation.[^12]
- **RPM**: Macros/helpers for parsing notes during package builds.[^12]
- **Yocto/OpenEmbedded**: Patches submitted for dependency extraction.[^13]
- **Other adopters**: mkinitcpio, htop, syft.[^12]

**Relevance to patchelf/Nix**: Nix's `autoPatchelfHook` currently
discovers runtime dependencies by scanning `DT_NEEDED` entries and RPATH
directories. It cannot discover `dlopen()` dependencies. Parsing
`.note.dlopen` could improve automatic dependency discovery in Nixpkgs.
Patchelf would need to preserve `.note.dlopen` sections during
modification (which it currently does, as it only modifies sections it
explicitly replaces).

## RELR Relocations — Critical Gap

### What RELR Is

RELR (SHT_RELR / DT_RELR) is a compact encoding for relative relocations
(`R_*_RELATIVE`), proposed by Cary Coutant and refined on the generic-abi
mailing list in 2017.[^14] It is now part of the gABI v4.3 draft.[^15]

Each entry is `uintptr_t` sized (4 or 8 bytes):[^16]

- **Even entry** (LSB = 0): An address (virtual address relative to a
  base of 0 for ET_DYN; absolute for ET_EXEC) needing relocation. Sets
  a cursor; that location gets `+= load_base`.
- **Odd entry** (LSB = 1): A bitmap. Shift right by 1; each set bit N
  means the cursor position + N words also needs `+= load_base`. The
  cursor advances by `(CHAR_BIT * sizeof(uintptr_t) - 1)` words.

This typically achieves >97% space savings vs RELA.[^16] For example,
65 contiguous relocations would require 1560 bytes in RELA (65 x 24
bytes) but only 24 bytes in RELR (1 address entry + 1 bitmap entry +
1 trailing address). (This example is illustrative; the actual savings
depend on address distribution.)

### Dynamic Tags

- `DT_RELR` (36): Address of `.relr.dyn` section[^17]
- `DT_RELRSZ` (35): Total size[^17]
- `DT_RELRENT` (37): Entry size[^17]

### Patchelf Gap — CRITICAL

**Patchelf has zero RELR handling code.** The constants are defined in
`src/elf.h` (lines 909-911) but `patchelf.cc` never references them.[^18]

If patchelf moves sections or changes load addresses, RELR entries (which
encode absolute `r_offset` addresses) become invalid. The patched binary
will crash at startup when the dynamic linker applies relocations to
wrong addresses.

This is an increasingly serious gap:[^19]

- Android and Fuchsia use RELR by default
- glibc 2.36+ supports RELR
- `-z pack-relative-relocs` is standard in modern GNU ld and lld
- Firefox's "relrhack" optimization has already caused patchelf failures
  (GitHub Issue #520)[^20]

Patchelf's `rewriteHeaders()` does not update `DT_RELR`/`DT_RELRSZ`
addresses when sections move, nor does it rewrite the RELR entries
themselves when `r_offset` values change.[^18]

## PN_XNUM — Extended Program Header Count

When the number of program headers exceeds 65534, `e_phnum` is set to
`PN_XNUM` (0xFFFF) and the actual count is stored in `sh_info` of section
header 0 (type SHT_NULL).[^21] Similarly, `e_shnum` overflow goes to
`sh_size` of section 0, and `e_shstrndx` overflow goes to `sh_link` of
section 0.[^21]

**Patchelf does not handle PN_XNUM.** It reads `e_phnum` directly without
checking for the sentinel value:[^22]

```cpp
auto ph_num = rdi(hdr()->e_phnum);  // line 286
```

While ELF files with >65534 program headers are rare (mostly core dumps),
patchelf would silently produce corrupt output if it encountered one.

## Compressed Sections (SHF_COMPRESSED)

Sections with the `SHF_COMPRESSED` flag have their content prefixed by a
compression header (`Elf_Chdr`) specifying the algorithm
(`ELFCOMPRESS_ZLIB` = 1, `ELFCOMPRESS_ZSTD` = 2), uncompressed size, and
alignment.[^23] `ELFCOMPRESS_ZSTD` was accepted into the gABI in July
2022.[^24]

The gABI states `SHF_COMPRESSED` "applies only to non-allocable sections"
and "cannot be used in conjunction with SHF_ALLOC."[^23] Since patchelf
primarily modifies allocable sections (`.dynamic`, `.interp`, `.dynstr`),
compressed sections are not currently a concern. However, if the
`SHF_ALLOC` restriction is relaxed (as has been proposed), this could
change.[^25]

Patchelf does not reference `SHF_COMPRESSED` in its source code.[^18]

## GNU Indirect Functions (STT_GNU_IFUNC)

`STT_GNU_IFUNC` (value 10) marks a symbol whose `st_value` points to a
resolver function, not the implementation itself. The dynamic linker
calls the resolver at relocation time to select an implementation (e.g.,
CPU-optimized `memcpy`).[^26]

**Patchelf risks**:[^27]

- If patchelf renames an IFUNC symbol, the symbol type (`st_info`) must
  remain `STT_GNU_IFUNC`. If inadvertently changed to `STT_FUNC`, the
  resolver address would be used as the function address, causing a crash.
- `IRELATIVE` relocations encode the resolver address directly (no symbol
  reference), so they survive symbol table modifications. However, they
  store the resolver's virtual address in the relocation addend — if
  patchelf moves the section containing the resolver (e.g., via
  `shiftFile()` which shifts virtual addresses), the addend becomes
  stale. Patchelf does not update `IRELATIVE` relocation addends.
- `ELFOSABI_GNU` (3) is expected by diagnostic tools like `readelf` to
  display IFUNC symbols correctly. However, the glibc dynamic linker
  does **not** check `ELFOSABI` before processing IFUNC relocations at
  runtime — IFUNC resolution works regardless of the OS/ABI byte.[^27a]
  Changing `ELFOSABI` via patchelf's `--set-os-abi` would affect tool
  output but not runtime behavior.

## Thread-Local Storage (TLS)

The linker combines `.tdata` (initialized) and `.tbss` (zero-initialized)
sections into a `PT_TLS` segment. The dynamic linker uses this to
allocate per-thread storage.[^28]

TLS uses four access models, listed from most to least efficient:[^29]

| Model | Use case | Address computation |
|---|---|---|
| Local Exec | Non-preemptible, in executable | Link-time constant offset from thread pointer |
| Initial Exec | Immediately-loaded objects | GOT entry with `R_*_TPOFF` dynamic relocation |
| Local Dynamic | Offset known, module unknown | Shared `__tls_get_addr` calls (optimization of GD for multiple variables in same module) |
| General Dynamic | Any object (most flexible) | Calls `__tls_get_addr` with both module ID and offset |

**Patchelf risks — HIGH**: If patchelf shifts sections that are part of a
`PT_TLS` segment:[^30]

- **Local Exec** offsets are hardcoded as immediate values in the text
  segment. These are not relocations and cannot be updated.
- **Initial Exec** GOT entries with `R_*_TPOFF` depend on the PT_TLS
  `p_vaddr` being correct.
- All TLS access relies on precise offset calculations from the thread
  pointer.

In practice, patchelf typically does not move `.tdata`/`.tbss` because
they reside in a data LOAD segment with other sections. But if patchelf's
segment splitting or page insertion shifts PT_TLS content, all thread-local
variable access in the binary would break.

## PIE Detection

PIE executables have `e_type = ET_DYN`, identical to shared libraries.
Patchelf distinguishes them using `PT_INTERP`: if present, the binary is
treated as an executable (`isExecutable = true`); otherwise, as a shared
library.[^31]

This approach is reasonable since patchelf's operations (setting
interpreter, modifying RPATH) depend on whether there is an interpreter.
However, `DF_1_PIE` (0x08000000 in `DT_FLAGS_1`) is not checked.[^31]

**Known issue**: `--add-needed` and `--remove-needed` can corrupt PIE
executables, causing ld.so assertion failures in `dl-version.c` (GitHub
Issue #115).[^32]

## Known Patchelf Bug Patterns

Analysis of patchelf's GitHub issues reveals recurring failure patterns:

### Pattern 1: Section Relocation Corrupts Metadata

When patchelf grows a section (e.g., longer RPATH), relocated program
headers or `.dynamic` entries may end up in wrong segments:

- **Issue #152**: `--set-rpath` places `.dynamic` in a read-only LOAD
  segment, causing ld.so to segfault.[^33]
- **PR #202**: Re-running patchelf on an already-patched binary corrupts
  the top of `.dynamic`.[^34]
- **Issue #446**: patchelf 0.17.0 regression causing segfaults after
  RPATH modification.[^35]

### Pattern 2: Tool Interaction Failures

Patchelf's section reorganization creates structures other tools
misinterpret:

- **Issue #507**: patchelf + llvm-strip sequence corrupts binaries.
  Patchelf's section reorganization creates structures that llvm-strip
  misinterprets, producing a corrupted binary that segfaults.[^36]
- **Issue #520**: Firefox's "relrhack" hardcodes `.dynamic` addresses.
  Patchelf moves `.dynamic` but cannot update those references.[^20]

### Pattern 3: PT_NOTE Handling

- **Issue #217**: patchelf doesn't update PT_NOTE when relocating
  SHT_NOTE sections.[^37]
- **Issue #255**: "unsupported overlap of SHT_NOTE and PT_NOTE" with
  Rust ELF files.[^38]
- **Issue #400**: "non-contiguous SHT_NOTE sections" error.[^39]
- **Issue #403**: `normalizeNoteSegments` causes `.dynstr` to not be
  fully contained in a segment.[^40]

### Pattern 4: Symbol Versioning Corruption

- **Issue #115**: `--add-needed`/`--remove-needed` breaks PIE
  executables, causing ld.so assertion failures in `dl-version.c`.[^32]
- **Issue #244**: `--set-rpath` outputs binary with broken
  `.dynsym`/`.dynstr`.[^41]

### Pattern 5: Platform-Specific Failures

- **Issue #215**: ARM Android library corruption when soname is changed;
  C++ exceptions cause stack corruption.[^42]
- **Issue #568**: Segfault on Fedora 41 after `--set-rpath` due to
  binutils layout changes.[^43]

## Alternative Approaches

### LIEF (lief-patchelf)

LIEF has developed a drop-in patchelf replacement using a
**segment-based approach** (matching how the OS loader works) rather than
patchelf's section-based approach.[^44] This makes LIEF more reliable for
binaries with non-standard section layouts, stripped section headers, or
unusual segment configurations. LIEF's patchelf passes 55 of 58 tests from patchelf's test suite (55
pass, 2 skipped, 1 failure).[^44]

The segment-based approach is noteworthy for the Lean 4 rewrite.
Whether operating primarily on the segment view (which is what the
kernel and dynamic linker actually use) would be more robust than
patchelf's section-based approach is an open design question — see
Open Questions below.

### Other Tools

- **elfutils** (`eu-readelf`, `eu-strip`, etc.): Comprehensive ELF
  reading/validation but not designed for post-link patching.[^45]
- **GNU binutils** (`objcopy`, `elfedit`): Can modify headers and
  sections but lack patchelf's high-level operations.[^45]
- **e9patch**: Static binary rewriting for x86_64 instrumentation, not
  linkage modification.[^46]

## Open Questions

- Should the Lean 4 rewrite adopt LIEF's segment-based approach instead
  of patchelf's section-based approach?
- How should RELR relocations be handled? Should patchelf rewrite RELR
  entries when sections move, or refuse to modify RELR-using binaries?
- Is there a formal specification for which DT_* tags contain addresses
  vs values? Patchelf's `rewriteHeaders()` hardcodes a list, but the
  gABI does not provide a systematic way to determine this.
- Should patchelf parse and preserve `.note.dlopen` sections, or is
  passive preservation (not touching them) sufficient?
- What is the correct behavior when patchelf encounters PN_XNUM? Should
  it error out or handle it?

## References

[^1]: `elf(5)` man page, "Notes (Nhdr)" section.
      `https://man7.org/linux/man-pages/man5/elf.5.html`

[^2]: MaskRay, "ELF: p_align = 8 for PT_NOTE," 2023.

[^3]: gABI, Chapter 5, "Note Section": "In 64-bit objects [...] each
      entry is an array of 8-byte words."
      `https://www.sco.com/developers/gabi/latest/ch5.pheader.html`

[^4]: `elf(5)` man page: note descriptors have "a 4 byte alignment."

[^5]: generic-abi mailing list, Q4 2017. H.J. Lu initial email:
      `https://sourceware.org/legacy-ml/gnu-gabi/2017-q4/msg00002.html`;
      Ali Bahrami response:
      `https://sourceware.org/legacy-ml/gnu-gabi/2017-q4/msg00011.html`;
      Mark Wielaard response:
      `https://sourceware.org/legacy-ml/gnu-gabi/2017-q4/msg00012.html`

[^6]: Ali Bahrami proposed alignment be "triggered by an sh_addralign,
      or p_align, of 8" rather than by ELF class. Ibid.

[^7]: `src/patchelf.cc`, lines 744-746, note alignment preservation in
      `writeReplacedSections()`.

[^8]: LLD patches: D61296 (group by alignment), D59531 (one PT_NOTE per
      section), D59120 (sort by decreasing alignment).
      `https://reviews.llvm.org/D61296`

[^9]: `src/patchelf.cc`, lines 1116-1180, `normalizeNoteSegments()`.

[^10]: Lennart Poettering, systemd PR #32234, April-May 2024.
       `https://github.com/systemd/systemd/pull/32234`;
       LWN.net coverage: `https://lwn.net/Articles/969908/`

[^11]: UAPI Group, "ELF dlopen metadata" specification (UAPI.12).
       `https://uapi-group.org/specifications/specs/elf_dlopen_metadata/`

[^12]: systemd/package-notes tooling for Debian/RPM integration.
       `https://github.com/systemd/package-notes`

[^13]: Yocto/OpenEmbedded patch for `.note.dlopen` extraction.
       `https://patchwork.yoctoproject.org/project/oe-core/patch/20241119125136.2507561-1-ross.burton@arm.com/`

[^14]: Proposal for SHT_RELR, generic-abi mailing list, 2017.
       `https://groups.google.com/g/generic-abi/c/bX460iggiKg`

[^15]: gABI v4.3 DRAFT, Xinuos.
       `https://gabi.xinuos.com/elf.pdf`

[^16]: MaskRay, "Relative relocations and RELR," October 2021.
       `https://maskray.me/blog/2021-10-31-relative-relocations-and-relr`;
       MaskRay, "A compact relocation format for ELF," March 2024.
       `https://maskray.me/blog/2024-03-09-a-compact-relocation-format-for-elf`

[^17]: `src/elf.h`, lines 909-911: `DT_RELRSZ` (35), `DT_RELR` (36),
       `DT_RELRENT` (37).

[^18]: Verified via grep: `patchelf.cc` contains zero references to
       "RELR", "SHF_COMPRESSED", or "PN_XNUM".

[^19]: glibc RELR support added in glibc 2.36 (BZ #27924).
       `https://patchwork.ozlabs.org/project/glibc/patch/20220310200329.1935466-2-hjl.tools@gmail.com/`

[^20]: NixOS/patchelf Issue #520: Firefox relrhack breaks patchelf.
       `https://github.com/NixOS/patchelf/issues/520`

[^21]: gABI, Chapter 4, "ELF Header": `e_phnum` may hold `PN_XNUM`
       (0xFFFF); actual count in section header 0's `sh_info`.
       `https://refspecs.linuxfoundation.org/elf/gabi4+/ch4.eheader.html`;
       `elf(5)` man page.

[^22]: `src/patchelf.cc`, line 286: `auto ph_num = rdi(hdr()->e_phnum);`
       with no PN_XNUM check.

[^23]: gABI, Chapter 4, "Sections," SHF_COMPRESSED description.

[^24]: ELFCOMPRESS_ZSTD proposal, generic-abi mailing list, July 2022.
       `https://groups.google.com/g/generic-abi/c/satyPkuMisk`

[^25]: MaskRay, "Compressed arbitrary sections," July 2023.
       `https://maskray.me/blog/2023-07-07-compressed-arbitrary-sections`

[^26]: MaskRay, "GNU indirect function," January 2021.
       `https://maskray.me/blog/2021-01-18-gnu-indirect-function`

[^27]: Ian Lance Taylor, "STT_GNU_IFUNC."
       `https://www.airs.com/blog/archives/403`

[^27a]: MaskRay, "GNU indirect function," January 2021: "Currently the
        only problem I know is the readelf -s display. Everything else
        works fine."
        `https://maskray.me/blog/2021-01-18-gnu-indirect-function`

[^28]: Ulrich Drepper, "ELF Handling for Thread-Local Storage."
       `https://www.uclibc.org/docs/tls.pdf`

[^29]: MaskRay, "All about thread-local storage," February 2021.
       `https://maskray.me/blog/2021-02-14-all-about-thread-local-storage`

[^30]: Android ELF TLS documentation.
       `https://android.googlesource.com/platform/bionic/+/HEAD/docs/elf-tls.md`

[^31]: `src/patchelf.cc`, line 322:
       `if (rdi(phdrs[i].p_type) == PT_INTERP) isExecutable = true;`

[^32]: NixOS/patchelf Issue #115.
       `https://github.com/NixOS/patchelf/issues/115`

[^33]: NixOS/patchelf Issue #152.
       `https://github.com/NixOS/patchelf/issues/152`

[^34]: NixOS/patchelf PR #202.
       `https://github.com/NixOS/patchelf/pull/202`

[^35]: NixOS/patchelf Issue #446.
       `https://github.com/NixOS/patchelf/issues/446`

[^36]: NixOS/patchelf Issue #507.
       `https://github.com/NixOS/patchelf/issues/507`

[^37]: NixOS/patchelf Issue #217.
       `https://github.com/NixOS/patchelf/issues/217`

[^38]: NixOS/patchelf Issue #255.
       `https://github.com/NixOS/patchelf/issues/255`

[^39]: NixOS/patchelf Issue #400.
       `https://github.com/NixOS/patchelf/issues/400`

[^40]: NixOS/patchelf Issue #403.
       `https://github.com/NixOS/patchelf/issues/403`

[^41]: NixOS/patchelf Issue #244.
       `https://github.com/NixOS/patchelf/issues/244`

[^42]: NixOS/patchelf Issue #215.
       `https://github.com/NixOS/patchelf/issues/215`

[^43]: NixOS/patchelf Issue #568.
       `https://github.com/NixOS/patchelf/issues/568`

[^44]: LIEF, "lief-patchelf: A drop-in patchelf replacement," July 2025.
       `https://lief.re/blog/2025-07-13-patchelf/`;
       lief-patchelf documentation:
       `https://lief.re/doc/latest/tools/lief-patchelf/index.html`

[^45]: elfutils project: `https://sourceware.org/elfutils/`;
       GNU Binutils overview:
       `https://interrupt.memfault.com/blog/gnu-binutils`

[^46]: e9patch: `https://github.com/GJDuck/e9patch`
