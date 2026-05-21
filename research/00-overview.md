# Research Overview

This directory contains research supporting the long-term goal of rewriting
patchelf in Lean 4 with formal proofs of correctness.

## Motivation

PatchELF is a critical tool in the Nix ecosystem: it is used throughout
Nixpkgs and stdenv to modify ELF binaries (setting interpreters, RPATHs,
and NEEDED entries). However, it has historically suffered from subtle
correctness bugs. Version bumps in Nixpkgs are rare because breakages are
insidious and difficult to root-cause -- a patched binary may appear to
work but fail under specific conditions (wrong library resolution order,
corrupted hash tables, misaligned segments, etc.).

A rewrite in Lean 4 with formal verification would allow us to:

1. **Define** the structural invariants of valid ELF files as types and
   propositions
2. **Prove** that each patchelf operation preserves these invariants
3. **Eliminate** classes of bugs by construction rather than testing

## Document Map

| Document | Contents |
|---|---|
| [CLAUDE.md](CLAUDE.md) | Conventions for this research directory |
| [01-elf-specification.md](01-elf-specification.md) | ELF standard history, versions, gABI/psABI architecture, ownership, key URLs |
| [02-gnu-extensions.md](02-gnu-extensions.md) | GNU program header types, hash tables, symbol versioning, RELRO, DT_RUNPATH vs DT_RPATH, notes |
| [03-dynamic-linking.md](03-dynamic-linking.md) | .dynamic section tags, sections vs segments, PT_LOAD mechanics, string/symbol/hash tables, loading process |
| [04-patchelf-invariants.md](04-patchelf-invariants.md) | Invariants the current C++ implementation maintains (and where it fails), ET_EXEC vs ET_DYN strategies, fragile code, a discovered bug (dead code in `modifyExecstack`) |
| [05-edge-cases-and-gaps.md](05-edge-cases-and-gaps.md) | ELF notes (format, alignment controversy, dlopen metadata), RELR relocations (critical gap), PN_XNUM, compressed sections, IFUNC, TLS, PIE detection, known patchelf bug patterns, alternative tools (LIEF) |

## Reading Order

For someone new to ELF:

1. Start with **01-elf-specification.md** for the big picture: what ELF
   is, where the specs live, the gABI/psABI split.
2. Read **03-dynamic-linking.md** to understand the dual-view architecture
   (sections vs segments), the loading process, and how the dynamic linker
   uses `.dynamic` entries.
3. Read **02-gnu-extensions.md** to understand the GNU-specific features
   that the base spec doesn't cover but that are ubiquitous on Linux.
4. Read **04-patchelf-invariants.md** to understand what the current
   patchelf does, what invariants it maintains, and where the known
   fragility lies.
5. Finally, read **05-edge-cases-and-gaps.md** for ELF features patchelf
   doesn't handle (RELR, PN_XNUM, TLS), the dlopen metadata proposal,
   historical bug patterns, and the LIEF alternative approach.

## Where the planned future content actually landed

The 06/07/08 docs originally planned in this overview were never created
as standalone documents.  Their content was absorbed elsewhere as the
Lean port matured:

| Originally planned | Where it landed |
|---|---|
| `06-correctness-properties.md` (formal properties) | [`REWRITE-ABI.md`](REWRITE-ABI.md) §"IsValid invariants" + [`lean/STATUS.md`](../lean/STATUS.md) §"Theorems and what they cover" |
| `07-lean4-elf-types.md` (Lean type drafts) | Realised directly in `lean/Patchelf/Elf/{Basic,ElfFile,ValidElfFile,Layout,...}.lean`; the typed-section algebra is documented in [`REWRITE-ABI.md`](REWRITE-ABI.md) |
| `08-test-strategy.md` (tests from spec edge cases) | Test fixtures under `lean/tests/cases/`; the fixture suite + planned Tier 2 real-binary harness are described in [`REWRITE-PHASE-3-DESIGN.md`](REWRITE-PHASE-3-DESIGN.md) §4d |

The known-bugs catalog originally planned as `06-known-bugs.md` was
incorporated into `05-edge-cases-and-gaps.md` (section "Known Patchelf
Bug Patterns"), which organizes bugs by failure pattern rather than
chronologically.

For active design work see [`REWRITE-PHASE-3-DESIGN.md`](REWRITE-PHASE-3-DESIGN.md).
For the deferred-work ledger see [`ROADMAP.md`](ROADMAP.md).
For landed-work state see [`lean/STATUS.md`](../lean/STATUS.md).

## Key Insight

The fundamental challenge is that ELF files have two parallel views
(sections and segments). At execution time, only the segment (program
header) view matters -- section headers are optional. However, patchelf
operates via the section view and must keep the segment view consistent
with its changes. When a section is moved, grown, or replaced:

- All program headers referencing that section must be updated
- All `.dynamic` entries containing virtual addresses of that section must
  be updated
- All symbol table entries referencing section indices must be remapped
- All hash tables must be rebuilt if symbols are reordered
- Alignment congruence (`p_vaddr % p_align == p_offset % p_align`) must
  be maintained for all PT_LOAD segments

The current C++ implementation handles these updates procedurally through
a series of ad-hoc fixups in `rewriteHeaders()`. A formal approach would
instead define these as invariants and prove that each operation preserves
them.
