# The ELF Specification: History, Versions, and Structure

The Executable and Linkable Format (ELF) is the standard binary format for
executables, shared libraries, object files, and core dumps on Unix-like
systems. This document traces the specification's history, enumerates its
versions and extensions, and maps the landscape of primary source documents.

## Origins

ELF was developed by **Unix System Laboratories (USL)**, a subsidiary of
AT&T, as the native object file format for **System V Release 4 (SVR4)**,
which shipped circa 1989-1990.[^1] In the System V lineage, ELF replaced
**COFF** (Common Object File Format), which had been introduced in AT&T
System V for 32-bit platforms in 1983.[^1b] On BSD systems, ELF replaced
the older `a.out` format.

USL collaborated with Sun Microsystems, incorporating elements of Sun's
dynamic shared library system from SunOS 4.x.[^2]

The format was designed to be:

- **Extensible**: new section types, segment types, and machine
  architectures can be added without breaking existing tools
- **Cross-platform**: architecture-independent structure with
  processor-specific supplements
- **Suitable for both linking and execution**: the same format serves as
  relocatable object files, shared libraries, and executables

## Specification Documents

The ELF specification has never had a single clean linear revision history.
Instead, it exists across several families of documents.

### System V Application Binary Interface (gABI)

The **generic ABI (gABI)** is the authoritative, architecture-independent
specification. It defines the ELF file format, section and segment
structures, symbol tables, relocations, and dynamic linking in
architecture-neutral terms.

The original was published in print by Prentice Hall on behalf of
AT&T/USL:[^3]

- *System V Application Binary Interface*, Prentice Hall, January 1993.
  ISBN 0-13-100439-5.

Subsequent editions were maintained as the Unix intellectual property
changed hands:

| Edition | Date | Publisher | Notes |
|---|---|---|---|
| Original | ~1990-1993 | AT&T/USL via Prentice Hall | Print only |
| Fourth Edition | ~1996 | SCO | PDF available[^4] |
| **Edition 4.1** | March 18, 1997 | SCO | Last formal edition[^5] |

After Edition 4.1, updates to the ELF-specific chapters (4 and 5) were
published as a series of online drafts hosted on sco.com. The Xinuos
revision history lists 15 drafts, the last dated July 23, 2015.[^6]

The SCO site hosts 7 archived snapshots plus a "latest" snapshot. Note
that snapshot URL dates reflect when the snapshot was saved and may differ
from the revision dates within the content. Some snapshots predate the
draft they are commonly associated with:[^7]

| Snapshot URL date | Content header date | Nearest draft |
|---|---|---|
| `1998-04-29` | April 29, 1998 | Pre-1st Draft (1st Draft is May 14, 1998) |
| `2000-07-17` | June 22, 2000 | 10th Draft |
| `2001-04-24` | April 24, 2001 | 11th Draft |
| `2003-12-17` | December 17, 2003 | (between 11th and 12th; no new draft number) |
| `2007-03-26` | March 26, 2007 | 12th Draft |
| `2009-10-26` | October 26, 2009 | Pre-13th Draft (13th Draft is November 3, 2009) |
| `2012-12-31` | October 19, 2010 | (post-13th, pre-14th) |
| `latest` | June 10, 2013 | 14th Draft (adds `SHF_COMPRESSED`)[^6a] |

The 15th Draft (July 23, 2015) appears in the Xinuos revision history[^9]
but was not captured as a separate snapshot on `sco.com`; the "latest"
snapshot still shows the 14th Draft content. The "latest" snapshot is at
`https://www.sco.com/developers/gabi/latest/contents.html`.[^7]

In 2025, **Xinuos** (the current IP owner) published new official
versions:[^8]

- **Version 4.2** (2025): Reported to have converted documentation to
  ReStructuredText and separated the ELF spec from the broader gABI
  document. [UNVERIFIED: the Xinuos site at `gabi.xinuos.com` shows only
  v4.3 DRAFT; v4.2 as a distinct publication could not be independently
  verified.]
- **Version 4.3 DRAFT** (PDF dated September 4, 2025; no formal
  publication date announced): Adds RELR relocations,
  `ELFCOMPRESS_ZSTD`, makes `DT_HASH` optional.

The Xinuos versions are hosted at `https://gabi.xinuos.com/` with source
on GitHub at `https://github.com/xinuos/gabi`.[^9]

### Tool Interface Standard (TIS)

The **Tool Interface Standards (TIS) Committee** was an industry consortium
(members included Intel, IBM, Microsoft, SCO, Novell, Borland, and others)
that published portable binary format specifications.[^10]

Two versions of the ELF specification were published under TIS:

- **TIS Portable Formats Specification, Version 1.1** (October 1993):
  Contains an extract of the x86 ABI version 3.0 alongside DWARF 2.0
  draft and OMF specifications.[^11]

- **TIS Executable and Linking Format (ELF) Specification, Version 1.2**
  (May 1995): The standalone ELF spec, reorganized into three books:
  Book I (generic ELF), Book II (x86 psABI), Book III (SVR4
  OS-specific).[^12]

TIS v1.2 is generally considered the most widely cited standalone ELF
specification. The TIS Committee grants "a non-exclusive, worldwide,
royalty-free license to use the information disclosed in this
Specification to make your software TIS-compliant" (per the TIS v1.2
frontmatter).[^12] It remains the best starting point for understanding
ELF.

### Processor-Specific ABI Supplements (psABI)

A conforming implementation requires both the gABI and the appropriate
**processor-specific ABI supplement (psABI)**. The psABI defines calling
conventions, register usage, relocation types, data representation, and
machine-specific ELF details.[^13]

Key psABI documents:

| Architecture | Document | URL |
|---|---|---|
| i386 | *System V ABI Intel386 Processor Supplement*, 4th Ed | `https://www.sco.com/developers/devspecs/abi386-4.pdf`[^14] |
| x86-64 | *System V ABI AMD64 Architecture Processor Supplement* | `https://gitlab.com/x86-psABIs/x86-64-ABI`[^15] |
| MIPS | *System V ABI MIPS Processor Supplement*, 3rd Ed | `https://refspecs.linuxfoundation.org/elf/mipsabi.pdf`[^16] |
| PowerPC | *System V ABI PowerPC Processor Supplement* | `https://refspecs.linuxfoundation.org/elf/elfspec_ppc.pdf`[^17] |
| IA-64 | *System V ABI IA-64 Processor Supplement* | `https://refspecs.linuxfoundation.org/elf/IA64-SysV-psABI.pdf`[^18] |
| ARM (32-bit) | *ELF for the ARM Architecture* | `https://refspecs.linuxfoundation.org/elf/ARMELF.pdf`[^19] |
| AArch64 (ARM 64-bit) | *ELF for the Arm 64-bit Architecture (AArch64)* | `https://github.com/ARM-software/abi-aa`[^19a] |
| RISC-V | *RISC-V ELF psABI Specification* | `https://github.com/riscv-non-isa/riscv-elf-psabi-doc`[^19b] |

The **x86-64 psABI** is the most actively maintained, currently managed by
H.J. Lu (Intel) and collaborators on GitLab.[^15] Version 1.0 was
finalized in late 2018. The gABI explicitly delegates certain decisions to
the psABI (e.g., relocation encodings, dynamic linker invocation rules).

## Ownership History

The UnixWare product assets (and with them, the hosting and maintenance of
the ELF specification) have passed through several hands:[^20]

1. **AT&T / Unix System Laboratories (USL)** -- original creator (~1989-1993)
2. **Novell** -- acquired Unix assets from USL in 1993
3. **The Santa Cruz Operation (old SCO)** -- acquired UnixWare product/technology assets from Novell via the Asset Purchase Agreement (APA), signed September 19, 1995, completed December 1995.[^20b] Note: the 2010 jury verdict in *SCO Group v. Novell* found that Novell retained the UNIX copyrights; the APA excluded copyrights from the transferred assets.[^20a]
4. **Caldera Systems / The SCO Group (new SCO/SCOX)** -- acquired from old SCO in 2001
5. **UnXis / Xinuos** -- acquired SCO Group's UnixWare assets in 2011

For the purposes of ELF specification maintenance, what matters is that the
hosting and editorial authority over the gABI documents transferred along
this chain, regardless of the broader UNIX copyright dispute.

Key individuals:

- **Dave Prosser** maintained the gABI from the USL days through The SCO
  Group era.[^20]
- **John Wolfe** was the last maintainer at Xinuos; he departed in
  2015.[^20]
- **Cary Coutant** (Google, later retired) served as the de facto
  community maintainer via the generic-abi Google Group. He is also the
  last GNU gold maintainer and current DWARF committee chair. Coutant
  publicly announced the gABI v4.3 draft and is reported to have
  coordinated with Xinuos on the 2025 updates, though the exact timeline
  and nature of this arrangement are not documented in primary
  sources. [UNVERIFIED: the specific claim of a "preliminary agreement in
  April 2020" originates from a secondary source.][^20]

Community coordination now happens on the **generic-abi Google Group** at
`https://groups.google.com/g/generic-abi`.[^21]

## The gABI / psABI Architecture

The System V ABI for any given system is composed of two layers:[^22]

```
+------------------------------------------+
|  Processor-Specific ABI (psABI)          |
|  - Calling conventions                   |
|  - Register usage                        |
|  - Relocation types                      |
|  - Data representation                   |
+------------------------------------------+
|  Generic ABI (gABI)                      |
|  - ELF file format                       |
|  - Section/segment structure             |
|  - Symbol tables & relocations (generic) |
|  - Dynamic linking framework             |
+------------------------------------------+
```

The gABI defines reserved ranges for OS-specific and processor-specific
extensions in section types (`SHT_LOOS`-`SHT_HIOS`,
`SHT_LOPROC`-`SHT_HIPROC`), segment types (`PT_LOOS`-`PT_HIOS`,
`PT_LOPROC`-`PT_HIPROC`), and dynamic tags (`DT_LOOS`-`DT_HIOS`,
`DT_LOPROC`-`DT_HIPROC`).[^23] This extensibility mechanism allows GNU,
Linux, Solaris, and other systems to add features without modifying the
base specification.

## Linux Standard Base (LSB)

The **Linux Standard Base** is a family of specifications maintained by the
Linux Foundation that standardizes the binary interface for Linux
distributions. It builds on the System V ABI and extends ELF for
Linux-specific purposes:[^24]

- Defines additional ELF special sections beyond those in the gABI
- Specifies additional `sh_type` values for section headers
- Standardizes Linux-specific ELF extensions per supported architecture
- References the gABI and relevant psABI documents as normative

LSB version history:

| Version | Date | Notes |
|---|---|---|
| 1.0 | 2001 | |
| 1.2 | June 2002 | |
| 1.3 | December 2002 | |
| 2.0 | August 2004 | |
| 3.0 | July 2005 | |
| 3.1 | October 2005 | Registered as ISO/IEC 23360 |
| 4.0 | 2008-2009 | Date disputed: Wikipedia says November 2008; the Linux Foundation site says May 2009 |
| 5.0 | June 2015 | Updated ISO/IEC 23360 in 2021 |

LSB specifications are hosted at
`https://refspecs.linuxfoundation.org/lsb.shtml`.[^25]

The LSB has seen declining adoption; Debian dropped its `lsb-*`
compatibility packages in 2015 after the package maintainer found no
volunteers to maintain them during a three-month discussion on the
debian-devel and debian-lsb mailing lists.[^26] In practice, the GNU
toolchain (binutils, glibc, GCC) and the Linux kernel define the de facto
standard for ELF on Linux, with extensions documented in source code and
`man` pages rather than formal specifications.

## ELF File Structure Overview

An ELF file has two parallel views, both defined starting from the ELF
header:[^27]

```
+-------------------+
|    ELF Header     |  -- identifies file class, endianness, machine type
+-------------------+
| Program Header    |  -- array of Elf_Phdr, describes segments for loading
| Table             |     (required for executables and shared libraries)
+-------------------+
|                   |
|    Sections /     |  -- the actual code, data, symbols, strings, etc.
|    Segments       |
|                   |
+-------------------+
| Section Header    |  -- array of Elf_Shdr, describes sections for linking
| Table (optional)  |     (used at link time, optional at execution time)
+-------------------+
```

- **Sections** are the linking view: named regions like `.text`, `.data`,
  `.dynstr`, `.dynamic`, used by the linker and tools like patchelf.
- **Segments** are the execution view: typed regions (PT_LOAD, PT_INTERP,
  etc.) that describe how the kernel and dynamic linker should map the
  file into memory.

Multiple sections may be mapped by a single segment. The section header
table is technically optional for execution (the kernel only needs program
headers), but patchelf requires it.[^28]

## Key Specification URLs

| Document | URL |
|---|---|
| TIS ELF v1.1 | `https://refspecs.linuxfoundation.org/elf/TIS1.1.pdf` |
| TIS ELF v1.2 | `https://refspecs.linuxfoundation.org/elf/elf.pdf` |
| gABI Edition 4.1 (1997) | `https://www.sco.com/developers/devspecs/gabi41.pdf` |
| gABI Fourth Edition | `https://www.sco.com/developers/devspecs/gabi40.pdf` |
| gABI latest SCO draft | `https://www.sco.com/developers/gabi/latest/contents.html` |
| Xinuos gABI v4.2/4.3 | `https://gabi.xinuos.com/` |
| Xinuos gABI GitHub | `https://github.com/xinuos/gabi` |
| Linux Foundation ELF index | `https://refspecs.linuxfoundation.org/elf/index.html` |
| x86-64 psABI (GitLab) | `https://gitlab.com/x86-psABIs/x86-64-ABI` |
| generic-abi mailing list | `https://groups.google.com/g/generic-abi` |
| `man 5 elf` (Linux) | `https://man7.org/linux/man-pages/man5/elf.5.html` |

## Open Questions

- The gABI draft history between the 14th Draft (2013) and the Xinuos v4.2
  (2025) is a 12-year gap. What de facto extensions were coordinated on
  the generic-abi mailing list during this period but never formalized
  until v4.3?
- How do non-Linux systems (FreeBSD, illumos/Solaris) extend ELF, and are
  there conflicts with GNU extensions?
- The Xinuos v4.3 draft makes `DT_HASH` optional. What is the migration
  status across toolchains?

## References

[^1]: MaskRay, "Evolution of the ELF object file format," May 26, 2024.
      `https://maskray.me/blog/2024-05-26-evolution-of-elf-object-file-format`

[^2]: Ibid. Sun's dynamic shared library implementation influenced the
      SVR4 dynamic linking design.

[^3]: AT&T, *System V Application Binary Interface*, Prentice Hall,
      January 1993. ISBN 0-13-100439-5.

[^4]: SCO, *System V Application Binary Interface*, Fourth Edition, ~1996.
      `https://www.sco.com/developers/devspecs/gabi40.pdf`

[^5]: SCO, *System V Application Binary Interface*, Edition 4.1,
      March 18, 1997.
      `https://www.sco.com/developers/devspecs/gabi41.pdf`

[^6]: SCO, *System V ABI, Chapters 4 and 5* (draft updates), 1998-2015.
      `https://www.sco.com/developers/gabi/`

[^7]: Archived snapshots available at dated URLs, e.g.,
      `https://www.sco.com/developers/gabi/2001-04-24/contents.html`,
      `https://www.sco.com/developers/gabi/2012-12-31/contents.html`.

[^8]: Xinuos, *System V Application Binary Interface*, Versions 4.2 and
      4.3 DRAFT, 2025.
      `https://gabi.xinuos.com/`

[^9]: Xinuos, gABI GitHub repository.
      `https://github.com/xinuos/gabi`
      Revision history: `https://gabi.xinuos.com/elf/c-history.html`

[^10]: Tool Interface Standards Committee, membership listed in TIS v1.1
       frontmatter.

[^11]: TIS Committee, *Tool Interface Standard (TIS) Portable Formats
       Specification, Version 1.1*, October 1993.
       `https://refspecs.linuxfoundation.org/elf/TIS1.1.pdf`

[^12]: TIS Committee, *Tool Interface Standard (TIS) Executable and
       Linking Format (ELF) Specification, Version 1.2*, May 1995.
       `https://refspecs.linuxfoundation.org/elf/elf.pdf`

[^13]: gABI Edition 4.1, Chapter 1: "A processor supplement document for
       each processor architecture describes the ABI for that
       architecture."

[^14]: SCO, *System V ABI Intel386 Architecture Processor Supplement*,
       Fourth Edition.
       `https://www.sco.com/developers/devspecs/abi386-4.pdf`

[^15]: H.J. Lu et al., *System V ABI AMD64 Architecture Processor
       Supplement*, GitLab.
       `https://gitlab.com/x86-psABIs/x86-64-ABI`

[^16]: *System V ABI MIPS Processor Supplement*, Third Edition.
       `https://refspecs.linuxfoundation.org/elf/mipsabi.pdf`

[^17]: *System V ABI PowerPC Processor Supplement*.
       `https://refspecs.linuxfoundation.org/elf/elfspec_ppc.pdf`

[^18]: *System V ABI IA-64 Processor Supplement*.
       `https://refspecs.linuxfoundation.org/elf/IA64-SysV-psABI.pdf`

[^19]: *ELF for the ARM Architecture*.
       `https://refspecs.linuxfoundation.org/elf/ARMELF.pdf`

[^20]: MaskRay, "Evolution of the ELF object file format," 2024;
       Xinuos gABI revision history.

[^20a]: *SCO Group v. Novell*, 10th Circuit Court of Appeals, affirming
        2010 jury verdict. The APA's excluded assets list excluded
        copyrights from the transferred assets. See also the District
        Court ruling (Judge Kimball, August 2007) for analysis of the
        APA's asset transfer provisions.

[^21]: generic-abi Google Group.
       `https://groups.google.com/g/generic-abi`

[^22]: gABI Edition 4.1, Chapter 1, "Introduction."

[^23]: gABI Edition 4.1, Chapter 4, "Sections" (reserved ranges for
       `sh_type`, `sh_flags`); Chapter 5, "Program Header" (reserved
       ranges for `p_type`); Chapter 5, "Dynamic Section" (reserved
       ranges for `d_tag`).

[^24]: Linux Foundation, *Linux Standard Base*.
       `https://refspecs.linuxfoundation.org/lsb.shtml`

[^25]: Ibid.

[^26]: Debian Bug #804264; Didier Raboud (lsb package maintainer)
       uploaded src:lsb 9.20150826 to unstable, dropping all `lsb-*`
       compatibility packages after no volunteers stepped forward.
       Discussion on debian-devel mailing list, September 2015.

[^27]: TIS ELF v1.2, Book I, Chapter 1, "Object Files."

[^28]: `src/patchelf.cc`, lines 297-298: patchelf errors with "no section
       headers" if `e_shnum == 0`.

[^1b]: COFF was introduced in 1983 in AT&T Unix System V for non-VAX
       32-bit platforms such as the 3B20. See Wikipedia, "COFF";
       MaskRay, "Evolution of the ELF object file format," 2024.

[^19a]: ARM Ltd., *ELF for the Arm 64-bit Architecture (AArch64)*.
        `https://github.com/ARM-software/abi-aa`

[^19b]: RISC-V Foundation, *RISC-V ELF psABI Specification*.
        `https://github.com/riscv-non-isa/riscv-elf-psabi-doc`

[^6a]: The Xinuos revision history at `gabi.xinuos.com/elf/c-history.html`
       confirms the 14th Draft (June 10, 2013) added "SHF_COMPRESSED to
       the Section Attribute Flags."

[^20b]: The APA was signed September 19-20, 1995. The sale was completed
        in December 1995 per Novell press release.
