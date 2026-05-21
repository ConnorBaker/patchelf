# patchelf Lean port — specification from first principles

> **ARCHIVED — design path not taken.** A spec-first framing
> written before the pure-IR + typed-section-algebra architecture
> landed.  The §4 proposed `ElfFile { bytes, header,
> dynamic : Option …, dynstr : Option …, … }` hybrid model was
> not pursued; the §3 6-clause `IsValid` is subsumed by the
> typed algebra's type-level invariants (`Fin ds.size` string-ref
> offsets make bounds vacuous).  Kept as historical record.
> For current state see `lean/STATUS.md`.

This document is NOT a revision of `REWRITE-DESIGN.md`. It specifies the verified port from scratch, without reference to what the current 55k-LOC codebase already contains. The goal is to anchor size estimates to *what is being specified*, not to what has accumulated.

## 1. What patchelf does (empirical)

The C++ tool is 2,764 LOC of `patchelf.cc` + 299 LOC of `patchelf.h` + 4,334 LOC of `elf.h` (hand-written ELF structure definitions) = 7,397 LOC total. The `elf.h` is a data-declaration file; the behavioral code is in `patchelf.cc`.

Fourteen primary mutator operations, each one C++ member function:

| Operation | C++ function | What it changes |
|---|---|---|
| setInterpreter | `setInterpreter` | `.interp` section contents + PT_INTERP |
| modifyOsAbi | `modifyOsAbi` | `e_ident[EI_OSABI]` byte |
| modifySoname | `modifySoname` | DT_SONAME value + `.dynstr` |
| modifyRPath | `modifyRPath` | DT_RPATH/DT_RUNPATH value + `.dynstr` |
| removeRPath | `removeRPath` | drop DT_RPATH/DT_RUNPATH |
| addNeeded | `addNeeded` | prepend DT_NEEDED + `.dynstr` |
| removeNeeded | `removeNeeded` | drop DT_NEEDED entries |
| replaceNeeded | `replaceNeeded` | rewrite DT_NEEDED strings |
| noDefaultLib | `noDefaultLib` | set DF_1_NODEFLIB in DT_FLAGS_1 |
| addDebugTag | `addDebugTag` | append DT_DEBUG |
| renameDynamicSymbols | `renameDynamicSymbols` | rewrite dynsym names + `.dynstr` |
| clearSymbolVersions | `clearSymbolVersions` | null out versym entries |
| modifyExecstack | `modifyExecstack` | PT_GNU_STACK flags |
| normalizeNoteSegments | `normalizeNoteSegments` | split PT_NOTE segments |

Every operation either (a) flips a single byte in the header, (b) rewrites a single dynamic-table entry's value and optionally appends to `.dynstr`, (c) rewrites a dynamic symbol's name, or (d) rewrites program-header flags. Plus `normalizeNoteSegments`, which is a structural PT_NOTE split.

All 14 operations delegate their byte-layout work to shared infrastructure (`rewriteSections`, `shiftFile`, `writeReplacedSections`). That infrastructure is ~800 LOC of the 2,764. Each op itself is small: 30-100 LOC of "which dynamic-table entry / which byte / which flag" plus a call into the shared layout engine.

## 2. What a verified Lean port must specify

Three things:

**(a) A type of ELF files.** Faithful enough that parsing a real binary yields a value of the type, and writing that value yields bytes that re-parse.

**(b) A validity predicate.** Just strong enough that "patchelf's operations preserve validity" is a meaningful claim. Nothing more.

**(c) The fourteen operations, each with a correctness theorem** stating the intended field changed and validity was preserved.

The size of the port is governed by (a) + (b) + (c) + the proofs they induce. Prior design-doc iterations conflated (b) with "every property anyone might ever want to state about ELFs", inflating 38 validity fields + 18 extra invariant modules. That is not intrinsic to the problem.

## 3. Minimal validity

Validity means: *the loader won't crash, and the patchelf operations can read back what they wrote.* Concretely, an ELF is valid iff:

1. **Header decodes**: `e_ident` magic/class/encoding are recognized; `e_phoff`, `e_shoff`, `e_shstrndx`, `e_phnum`, `e_shnum` are in-bounds.
2. **Program header table is well-formed**: `phnum * phentsize` bytes starting at `phoff` decode to a list of `ProgramHeader`s.
3. **Section header table is well-formed**: `shnum * shentsize` bytes starting at `shoff` decode to a list of `SectionHeader`s; `shstrndx < shnum`; `sectionHeaders[0]` is `SHT_NULL`.
4. **String tables are null-terminated**: both `.shstrtab` (found via `shstrndx`) and `.dynstr` (found via `findSection ".dynstr"` or DT_STRTAB).
5. **Dynamic table, if present, ends with DT_NULL**: and every DT_* tag that carries an address-offset into `.dynstr` has its offset in bounds of `.dynstr`.
6. **Dynamic symbols, if present, have in-bounds name offsets**: each `st_name < dynstr.size`.

Six clauses. That's validity. Everything else the old `IsValidELF` + 18 Gaps enumerated (PT_TLS uniqueness, PT_PHDR self-consistency, GNU hash bucket ordering, verneed file-offset matches needed, etc.) is either:

- **Derivable** from clauses 1-6 plus the well-formed structural decoding. No need to state separately.
- **Not load-preserving and therefore optional**. Example: PT_TLS alignment. The loader uses the value; it doesn't reject on inconsistency. patchelf doesn't need to preserve it symbolically; it preserves it because it doesn't touch the field.
- **Only interesting post-hoc**: "after addNeeded, the verneed still points at `.dynstr` and DT_VERNEEDNUM matches" is a property of *the op*, not of ELFs generally. It lives in the op's correctness theorem.

This is the load-bearing move. The old 38-field structure conflated "properties of a well-formed ELF" with "properties patchelf chose to track." They're different. The first has 6 clauses. The second is a superset the user specifies at theorem time.

## 4. Minimal state

```lean
structure ElfFile where
  bytes      : ByteArray
  header     : ElfHeader
  phdrs      : Array ProgramHeader
  shdrs      : Array SectionHeader
  dynamic    : Option (Array DynEntry)      -- DT_* entries, parsed from .dynamic
  dynstr     : Option StringTable            -- .dynstr parsed
  dynsym     : Option (Array Symbol)         -- .dynsym parsed
  versym     : Option (Array UInt16)         -- .gnu.version parsed

def IsValid (e : ElfFile) : Prop :=
  decodesHeader e.bytes e.header ∧
  decodesPhdrs  e.bytes e.header e.phdrs ∧
  decodesShdrs  e.bytes e.header e.shdrs ∧
  strtabsNullTerminated e ∧
  dynamicEndsWithNullAndOffsetsInBounds e ∧
  dynsymNamesInBounds e
```

No separate Gap modules. No `Plus` variants. No projection layer. No KernelLoad separate from validity. If someone wants "this ELF loads and the kernel reads OSABI = Linux", they write `e.header.ident.osAbi = .linux` — it's a field access, not a separate theorem about a separate projection.

## 5. Operations

Each op is a function `ElfFile → ... → ElfFile` plus one theorem:

```lean
-- Op definition
def setInterpreter (e : ElfFile) (path : String) (hValid : IsValid e) : ElfFile := ...

-- Correctness theorem
theorem setInterpreter_correct
    (e : ElfFile) (path : String) (hValid : IsValid e) :
    let e' := setInterpreter e path hValid
    IsValid e' ∧ getInterpreter e' = some path
```

One precondition: the input is valid. One postcondition: output is valid AND the targeted field changed. That's the whole contract.

Some ops need additional preconditions (e.g., `setInterpreter` requires that `.interp` fits in the reserved PT_LOAD slack, or the op fails). Those live in the op's signature.

The fourteen ops × ~100-200 LOC each (body + correctness proof) ≈ 1.4-2.8k LOC for the Ops layer.

## 6. Byte-layout engine

The op bodies don't do their own byte layout. They delegate to a shared layout engine (analog of C++'s `rewriteSections`). The engine:

- Takes a list of `SectionPatch { index : Nat, newBytes : ByteArray }`.
- Produces new ELF bytes with updated offsets, phdr/shdr tables flushed, etc.
- One correctness theorem: "the patched bytes re-parse to an ElfFile whose sections differ from the input exactly in the patched indices."

This engine is the hard part. C++'s is 800 LOC. A Lean version with proofs is plausibly 1-2k LOC.

## 7. The codec

`decodeHeader`, `encodeHeader`, `decodeProgramHeader`, ... plus the roundtrip theorem `decode_encode_id` for each.

C++'s `elf.h` is 4,334 LOC of data definitions. Lean structures defining the same data are much smaller (no conditional macros for 32/64-bit variants, no alignment pragmas). Realistic: 1-2k LOC. The roundtrip theorems for each codec are stock patterns (each ~20-30 LOC). Twelve structures × 25 LOC ≈ 300 LOC of roundtrip proofs. Total codec layer: 1.5-2.5k LOC.

## 8. CLI

Parse command-line arguments; dispatch to the op; serialize output; handle errors. Fewer than 300 LOC.

## 9. Total size estimate, from the specification outward

| Layer | Specified content | Realistic LOC |
|---|---|---|
| Codec (decode/encode + roundtrips) | 12-ish structures + their proofs | 1.5-2.5k |
| Validity (6-clause `IsValid`) | Definition + decidability + fixture non-vacuity | 400-600 |
| Byte-layout engine | `rewriteSections` + correctness theorem | 1-2k |
| Ops (14 functions + 14 theorems) | Function + preservation + observable | 1.4-2.8k |
| CLI + `Main.lean` | Dispatch + error handling + I/O | 200-300 |
| Tests (differential against C++) | Harness + fixtures | 300-500 |
| **Total** | | **4.8-8.7k** |

Comparison:
- C++ patchelf (implementation only): ~3k LOC.
- This port: **~5-9k LOC**, which is 1.7-3× the C++. For a verified port this is comparable to CompCert (~10×) and seL4 (~20×) against their respective implementations — actually *better*, because patchelf's domain is smaller and more regular than a compiler or microkernel.

This is the target the original REWRITE-DESIGN.md tried to reach (6-9k in v2) but lost track of through iterative cost-tuning against the existing bloated codebase.

## 10. What's deleted

Relative to what's in the current 55k-LOC port:

- **Spec/Gaps/** (8.8k LOC, 18 modules): deleted entirely. Their content either absorbs into `IsValid`'s 6 clauses (if load-relevant) or into an op's correctness theorem (if op-specific) or goes away (if merely decorative).
- **Spec/Stability/** (would have been 1.3-1.7k in v10): never created. With 6 validity clauses instead of 38+18, per-invariant stability lemmas are mostly 2-liners proved inline.
- **Spec/RuntimeBehavior.lean** (1,369 LOC): deleted. Runtime behavior is a projection on ElfFile fields; it's not a separate model layer.
- **Spec/KernelLoad.lean** (310 LOC): deleted. Byte-level loader semantics is a theorem about parse applied to output bytes; not a separate predicate.
- **Spec/AntiRegressions.lean** (1,100 LOC): deleted. Regression theorems live either in the op's own file (if op-specific) or in `test/` (if fixture-based).
- **IsValidELF 38-field structure**: replaced by 6-clause `IsValid` predicate.
- **Safe/Bounded variant ladders**: never created. One canonical op per operation.
- **`refine_IsValidELF` macro**: never needed.
- **`findSection_stable` as a named bridge**: `findSection` is a function on bytes + header + shdrs; its behavior under a byte patch is a theorem about the patch region, proved once for the layout engine.

## 11. What's kept

- **Elf/ codec directory**: most of its 8.9k LOC is encoder/decoder pairs with roundtrips. This work is mostly done. Estimated salvage: 1.5-2.5k LOC after pruning core-duplicating lemmas and simplifying.
- **Ops/Read.lean** (parser): the `ParsePass3`-style fail-fast structure is the RIGHT shape — it's the 6-clause `IsValid` expressed as a decidable bundle. Estimated salvage: 400-600 LOC.
- **`Util/IndexPermutation.lean`**: mostly replaced by Lean core's `Array.Perm`, with ~100-150 LOC of wrapping.

## 12. The load-bearing claim

If minimal validity is genuinely 6 clauses (not 38+18), then the port's size is governed by (a) codec complexity, (b) layout-engine complexity, (c) per-op preservation-for-6-clauses. None of these compound to 35k.

The way to falsify this document is to find a patchelf operation that cannot be specified correctly without additional invariants beyond the 6. I've looked; I don't see one.

- `setInterpreter`: modifies `.interp` bytes and PT_INTERP filesz/offset. Clauses 1-3 cover header/phdr/shdr well-formedness; clause 4 covers `.interp`'s implicit null-termination. No Gap module needed.
- `modifyRPath`: appends to `.dynstr` and rewrites a DT_RPATH/DT_RUNPATH value. Clauses 4 (dynstr null-terminated) and 5 (DT_* offsets in bounds) are exactly what preservation needs.
- `normalizeNoteSegments`: splits PT_NOTE phdrs. Preserves clauses 1-3. Doesn't touch dynamic or dynstr. No Gap-level invariant involved.
- `renameDynamicSymbols`: rewrites `.dynstr` and dynsym names. Clause 6 (dynsym name offsets in bounds) is exactly what preservation needs.

The old IsValidELF's 38 fields enumerated *additional* properties (PT_TLS alignment, GNU hash ordering, versym length) that are interesting but not *load-preserving* — the loader doesn't reject on their violation. A spec-first port distinguishes "invariants the loader enforces" from "invariants some RFC annex mentions." The first is 6. The rest is optional.

## 13. What validates or falsifies this

Before committing to implementation, one prototype validates the design:

1. Port **setOsAbi** (the simplest op — flips one byte). Implement + prove the correctness theorem against 6-clause validity. Target: ≤ 50 LOC total including the op definition, the preservation proof, and the observable `getOsAbi` theorem.

2. Port **modifyRPath** (a mid-difficulty op — dynstr append + DT_* rewrite). Target: ≤ 200 LOC total.

If (1) exceeds 50 LOC or (2) exceeds 200 LOC, the design is wrong — the 6 clauses are insufficient and we're smuggling invariants back in through op signatures. Stop and re-examine.

If both succeed, extrapolate: 14 ops × average 150 LOC ≈ 2.1k Ops. Combined with codec + engine + validity + CLI + tests, total lands in the 5-9k band.

## 14. Relationship to REWRITE-DESIGN.md

`REWRITE-DESIGN.md` is a ten-version cost-estimate document about preserving the existing 55k codebase's framework. This document proposes replacing that framework. The two documents don't agree and shouldn't be merged. If this specification is accepted, REWRITE-DESIGN.md is obsolete.

## 15. Open questions

1. **Is validity actually 6 clauses or 7-8?** I claim 6 based on what the loader enforces. If real-world ELFs rely on a seventh load-time check (e.g., DT_VERSYMIDX consistency), add it. Each addition adds ~50-100 LOC across the port.

2. **Is the byte-layout engine 1-2k LOC in Lean?** This is the biggest unknown. C++'s is 800 LOC of imperative code. A verified version might be 1.5-3× that. If it's 3k, the total creeps toward 10k but still well below 35k.

3. **Can the existing codec (8.9k) actually be pruned to 2.5k?** Much of its bulk is redundant lemmas that the rewrite can delete by leaning on core `ByteArray` lemmas. Requires audit before the rewrite.

4. **What's the cost of Differential testing against C++ patchelf?** If we run C++ patchelf and diff bytes on fixtures, that's <500 LOC of harness. If we re-derive the expected output by hand, more.

5. **Does the `normalizeNoteSegments` op fit in 200 LOC?** It's structurally more complex than the others. If it needs 500-1000 LOC, it's an outlier, not a framework failure.

## 16. Recommendation

Write the setOsAbi + modifyRPath prototypes against the 6-clause `IsValid`. Three-day scope. If the prototypes meet the LOC targets (50 / 200), commit to this spec and execute. If they don't, abandon the rewrite and return to closing the 31 sorries on the existing 55k codebase.
