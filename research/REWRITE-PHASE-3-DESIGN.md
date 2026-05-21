# Phase 3 Design: Verified Loader-Coherent ELF Patcher

This document captures the design and migration path for the next major
arc of the Lean 4 `patchelf` port: closing the PT_LOAD / DT_* coherence
gap (the central correctness bug, documented in
[`lean/STATUS.md`](../lean/STATUS.md) §"Known correctness gap").

It supersedes the deferred-work entries in
[`ROADMAP.md`](ROADMAP.md) §1.1, §1.2, §3.5, §3.6 and §5.1, which
described op-level preservation theorems and feature-parity items
that this design renders obsolete (§5.1's op-level Tier D becomes
trivial under the unified `Elf` model; §3.5/§3.6 become decidable
preconditions of `Layout.apply`).

The decisions in this document are LOAD-BEARING. They were reached
after multiple rounds of adversarial review; the salient findings
are captured in §"Why this design" below.

## 1. Verification target

**The port verifies against the Linux+glibc loader contract, not
behavioral equivalence to C++ patchelf.** The C++ implementation
has documented bugs[^1] that we explicitly do not want to inherit.

Concretely, "the loader contract" is the union of:

- **Linux kernel `load_elf_binary`**, version ≥4.14[^2] — what the
  kernel checks before transferring control. Page-aligned PT_LOAD
  congruence (`p_offset ≡ p_vaddr mod p_align`); PT_INTERP/PT_PHDR
  consistency; magic / class / data-encoding bytes; `e_machine` in
  the kernel's supported set (we maintain a smaller architecture
  whitelist; see §4b predicate #2).
- **glibc `dl-load.c`**, version ≥2.31[^3] — what the dynamic
  linker requires after the kernel hands off, **only when a
  PT_DYNAMIC segment is present**. Static binaries (no PT_DYNAMIC,
  common in the ET_EXEC corpus) skip these checks entirely. When
  PT_DYNAMIC IS present: DT_STRTAB / DT_SYMTAB / DT_HASH (or
  DT_GNU_HASH) / DT_VERNEED inside some PT_LOAD's vaddr range;
  DT_NEEDED string-table indices in bounds; DT_STRSZ matches
  `.dynstr` size.

**What this contract does NOT cover** (see §4b.1 for full list):
GNU-hash chain semantics; relocation entry validity; PT_GNU_PROPERTY
note correctness; symbol versioning index consistency. A binary that
passes `Loader.IsLoadable` is structurally well-formed and
loader-mappable; runtime semantic validity (`ld.so` actually
resolves a symbol) is a stricter contract that Phase 3 may
incrementally tighten.

musl, FreeBSD `rtld-elf`, Solaris ld.so.1, and bionic[^4] are
**out of scope.** The port may produce binaries those loaders
reject; we do not commit to the contrary. NixOS, Debian stable,
RHEL/Rocky, and Alpine-glibc workloads are in scope; Alpine-musl
is not.

The contract is encoded as `Loader.IsLoadable : Elf → Prop` with a
decidable instance. `--validate` reports against it. `Layout.apply`
produces it as a postcondition (subtype return).

### What "verifies" means here

Three top-level theorems, after Phase 3 lands:

```lean
-- T1: codec roundtrip on the unified type. Replaces today's
-- parse_encode_roundtrip; the EncodePreconditions bundle vanishes
-- because all 9 clauses become invariants of `Elf`.
theorem encode_decode (e : Elf) :
    Codec.decode (Codec.encode e) = .ok e

-- T2: every CLI run that produces output produces loader-valid bytes.
theorem patchelf_produces_loadable
    (input : ByteArray) (op : Op) (output : ByteArray)
    (hRun : runOp op input = .ok output) :
    ∃ (e : Elf), Codec.decode output = .ok e ∧ Loader.IsLoadable e

-- T3: each op preserves an op-specific observable.
theorem patchelf_op_correct
    (input : ByteArray) (op : Op) (output : ByteArray)
    (hRun : runOp op input = .ok output) :
    ∃ (e₀ e₁ : Elf),
      Codec.decode input  = .ok e₀ ∧
      Codec.decode output = .ok e₁ ∧
      Loader.IsLoadable e₁ ∧
      Op.spec op e₀ e₁
```

The current `parse_encode_roundtrip` (`lean/Patchelf/Elf/ByteRoundtrip.lean:2325`)
is the `Op.spec = identity, plan = identity` special case of T3.
The Phase 3 work renames it accordingly; it is not "preserved unchanged"
across the refactor.

## 1.5. What ships when (calendar honesty)

This design serves the user-stated goal "never produce broken output"
in stages, not all at once. Honesty about which stage ships what:

| Stage | User-visible safety improvement | Ship horizon |
|---|---|---|
| **Phase 0** | `--validate` runs **before** writeBinFile and refuses to write on failure (§4c). `--validate` is **on by default**; opt out with `--no-validate`. Atomic write replaces `IO.FS.writeBinFile` so partial writes don't corrupt the input. **Net: today's broken-output cases now become refuse-to-write-output cases.** | ~2-3 weeks |
| **Unification** | None user-visible. Refactor only. Tier 2 tests must continue to fail with the same diagnostics. | +6-10 weeks (cumulative ~3-4 months in) |
| **Phase 3** | Broken-output cases become correct-output cases. The 6 Tier 2 fail-on-master tests flip to PASS. | +4-8 months (cumulative ~7-12 months in) |

**Phase 0 is the user-facing safety mechanism for the interim period.**
Refuse-to-write is a meaningful improvement over silently-write-broken.
Phase 3 is when broken cases start succeeding instead of refusing.

**Velocity caveat.** The Phase 3 budget (1500–2400 LOC of code +
700–1000 LOC of `apply_isLoadable` proof) at the project's historical
~3 LOC/hour proof velocity is 500–1000 hours of focused work. At a
steady 20 hours/week cadence that is 6–12 calendar months. Estimates
carry the historical 1.5–2× understatement risk; treat the upper bound
as more likely than the lower.

## 2. What we are NOT building

These items appeared in earlier plan drafts and have been struck
after adversarial review:

- **Phase 2 ("refuse cleanly").** Realistic invocation coverage on
  production binaries is 5–15%, not the 70% claimed in earlier drafts.
  Every `--add-needed` / `--set-rpath` / `--set-interpreter (grow path)`
  on a real binary requires `.dynstr` to grow past PT_LOAD's
  `p_filesz`. A "refuse-on-grow" build would route 85–95% of real
  invocations to "use C++ patchelf instead." Phase 3 makes those
  invocations succeed correctly; an intermediate refusal phase
  delays correct behavior without shipping value.

- **`--allow-reflow`.** It opts users back into the bug
  `--validate` exposes. There is no scenario where `--allow-reflow`
  is preferable to "use the page-size-aware reflow that Phase 3
  ships."

- **In-place fast path optimization.** A `canEditInPlace` predicate
  can land later as a byte-stability optimization (avoid mutating
  bytes when the op fits in existing slack). It is not on the
  critical path. When it does land, it must be distinct from
  `LayoutEngine.layoutAlreadyValid`, which is a 2-clause
  optimization gate (`sectionsNonOverlapping ∧ shdrSectionDisjoint`),
  not a safety predicate.

- **Behavioral equivalence to a pinned C++ patchelf revision.**
  See §1.

## 3. Phase ordering

```
Phase 0  →  Unification refactor  →  Phase 3
(visible)    (shape)                  (correctness)
```

### Rationale

The unification refactor (collapse byte-layer `ElfFile` + typed
`ValidElfFile` + `Adapter` into a single `Elf`) lands BETWEEN
Phase 0 and Phase 3, not after. Two reasons:

1. **Phase 3's proof obligations are dominated by `apply_isLoadable`**
   (estimated 700–1000 LOC of the 1500–2400 LOC budget). Each
   clause of `IsLoadable` (PT_LOAD coverage, DT_* address coherence,
   etc.) currently has to be discharged twice — once at the byte
   layer, once at the typed layer — and bridged through `Adapter`
   (`lean/Patchelf/Elf/AdapterRoundtrip.lean`, 103 LOC plus the
   discontinuity it papers over). Phase 3 on the unified `Elf`
   discharges each clause once.

2. **Phase 0's `--validate` predicates port mechanically to `Elf`.**
   Most are decidable on either layer; the unification redirects
   them rather than rewriting them. The cost of porting Phase 0
   across the refactor is ~50 LOC of import-site changes, not a
   meaningful fraction of Phase 0's budget.

The cost is that the unification refactor is a substantial mid-arc
investment (~−4,800 LOC; 13,717 → 8,890 estimated). It is
sequenced as its own milestone with its own acceptance gate.

## 4. Phase 0 — `--validate` flag, Tier 2, CI

**Goal:** stop producing broken output when validation can detect it.
The 49 shell tests pass cleanly; ops that would produce broken bytes
on real binaries refuse to write instead. Atomic write replaces
direct overwrite so partial-write corruption is impossible.

**Budget:** ~470 LOC (~241 Lean + 150 shell + 35 yaml + 25 docs +
~20 LOC `Main.lean` flow refactor). Up from earlier ~380 LOC; the
delta is 70 LOC of atomic write (§4c.1) + 20 LOC of validate-before-
write plumbing in `Main.lean`.

### 4a. Generalizations to land first

Three small generalizations land in a single PR before the
validator code, because four downstream consumers (`--validate`
itself, `IsLoadable`, future `LayoutPlan.AppliesTo`, future
`canEditInPlace`) all consume them. Skipping these means each
consumer re-implements the same coverage / disjointness primitives
inline.

| Generalization | LOC | Replaces |
|---|---:|---|
| `Patchelf/Elf/IntervalRange.lean` (NEW): `Range` record, `Range.coversRange`, `Array.coversVal`, `Array.findCovering`, `ProgramHeader.fileRange` / `.memRange` | ~80 | hand-rolled quantifiers in `dynAddressCoherentForTag` (`ElfFile.lean:695-705`) and `segmentCongruence` (`ElfFile.lean:552-560`) |
| Unified `Diagnostic` inductive (Phase 0 minimal: parse + validity + layout slices) | ~50 | `ParseError` (29 ctors at `ParseHeader.lean:18-48`), `DynamicParseError`, `AdapterError`, ad-hoc `Repr`-based stringification at `Main.lean:117` |
| `Patchelf/Elf/LayoutMutation.lean` (NEW): per-op static classification of byte deltas (`dynstrDelta`, `dynamicEntryDelta`, `requiresPtLoadGrow`) | ~50 | future Phase 3 / future `canEditInPlace` re-deriving these per-op |

The `Diagnostic` migration absorbs the existing error types
incrementally — Phase 0 lands the inductive and the new validate
constructors; later phases collapse the existing error types into
slices of it.

### 4b. Validator predicates

`Patchelf/Elf/Validate.lean` (NEW, ~120 LOC) defines a
`ValidateFailure` inductive plus
`runValidate : ElfFile → Array ValidateFailure`. Each predicate
is decidable; most are already proved decidable in `ElfFile.lean`
and just need to be collected, named, and fitted with a per-failure
formatter.

The 16-predicate set (was 14 in earlier drafts; added `eMachineSupported`
and made all DT_* predicates conditional on `e.dynamic.isSome`):

1. `headerCountsConsistent` (existing, `ElfFile.lean:211-219`)
2. `eMachineSupported` (NEW) — `e.header.machine ∈ supportedMachines`.
   Whitelist: `EM_X86_64`, `EM_386`, `EM_AARCH64`, `EM_ARM`,
   `EM_RISCV`, `EM_PPC64`, `EM_LOONGARCH`. Other values produce a
   warning, not a hard fail (we don't reject e.g. `EM_S390`; we
   just don't promise correctness). STATUS.md:243-250 flags this gap.
3. `segmentCongruence` (existing, `ElfFile.lean:551-560`) — PT_LOAD
   `p_offset ≡ p_vaddr mod p_align`
4. `ptLoadFileBoundsFit` (NEW) — every PT_LOAD's
   `[offset, offset+filesz)` ≤ encoded file size
5. `ptLoadMemszGeFilesz` (NEW)
6. `sectionFileInSomePtLoad` (NEW) — **the central bug.** Every
   non-NULL non-NOBITS section's file range is inside some PT_LOAD's
   file range. Currently violated post-`layoutForEncoding`.
7. `sectionAddrInSomePtLoad` (NEW) — SHF_ALLOC sections: vaddr range
   inside some PT_LOAD's vaddr range
8. `dtStrtabInPtLoadVaddr` (NEW; **conditional on `e.dynamic.isSome`**)
9. `dtStrszEqDynstrSize` (existing as `dynStrszCoherent`,
   `ElfFile.lean:727-744`; conditional on `e.dynamic.isSome`)
10–14. `dt{Symtab,Hash,GnuHash,Verneed,Versym}InPtLoadVaddr` (NEW;
    each conditional on `e.dynamic.isSome`)
15. `dtNeededInBounds` (delegates to existing `dynamicStringRefsValid`;
    conditional on `e.dynamic.isSome`)
16. `ptPhdrConsistent` (NEW) — PT_PHDR offset/filesz match
    `e_phoff` / `e_phnum × phentsize`

**Conditioning on `e.dynamic.isSome` is load-bearing:** static
binaries (e.g., fully-static busybox, glibc-static-linked binaries,
common in the 30–40% ET_EXEC corpus) have no PT_DYNAMIC at all.
Predicates that quantify over DT_* tags must vacuously hold when
the dynamic section is absent.

**`e.IsValid`** as a fallback (catches anything not enumerated above).

#### 4b.1 What `--validate` does NOT catch

Important to be honest about the contract scope:

- **GNU-hash chain validity.** `dtGnuHashInPtLoadVaddr` checks the
  `.gnu.hash` section is in a PT_LOAD; it does NOT check the bloom
  filter / bucket count / chain semantics. A malformed hash chain
  passes `--validate` and SIGSEGVs glibc at first symbol resolution.
  Phase 3 may add `gnuHashChainValid` once we model GNU hash; for
  Phase 0 this is out of scope. Documented in `--help`.
- **Relocation correctness.** `.rela.dyn` / `.rela.plt` entries
  pointing to addresses outside any PT_LOAD are runtime crashes,
  not parse errors. Out of scope for Phase 0.
- **`.note.gnu.property` PT_GNU_PROPERTY.** Modern glibc rejects
  binaries claiming SHSTK / IBT support without proper note. Out
  of scope for Phase 0.
- **Symbol versioning consistency.** Versym indices into Verneed/
  Verdef must be in bounds; we check the section is loaded but not
  the per-entry indices. Out of scope for Phase 0.

These gaps mean a Phase-0 `--validate` PASS is necessary but not
sufficient for "kernel + glibc accept the binary." The Tier 2 CI
runs `eu-elflint --strict` and `readelf -a` parsing as oracles
that catch some of these.

### 4c. CLI surface

**Validation runs BEFORE the file is written.** The previous design
draft had `--validate` reparsing the post-write bytes — this is a
post-mortem, not a guard, and violates Bash convention that nonzero
exit means "nothing happened." The fixed flow:

```
parse(input bytes) → ops.foldl → encode → ByteArray
                                              ↓
                                      runValidate (in memory)
                                       ↓ failures   ↓ ok
                                  emit + exit 5    writeAtomic(target)
```

- **`--validate` is ON BY DEFAULT.** This is the load-bearing decision.
  A user running `patchelf --add-needed libfoo.so /usr/bin/ls` should
  not get corrupted output silently. To disable, pass `--no-validate`
  (escape hatch for users who know what they're doing or are
  reproducing a buggy state for debugging).
- **`--no-validate`:** bypass the safety check. Documented in `--help`
  as "DANGEROUS: may produce binaries the kernel rejects."
- **`--validate-only`:** read-only mode. No mutation, no write; just
  parse, run predicates, exit 0/5. Useful for CI checks against
  unmodified binaries.
- **Composability:** `patchelf --set-rpath /foo file` (no explicit
  flag) is equivalent to `patchelf --set-rpath /foo --validate file`.
  Validation sees the in-memory post-mutation `Elf` before any I/O.
- **Atomic write (Phase 0, NOT deferred):** when validation passes,
  bytes are written via `IO.FS.writeBinFileAtomic` (write to
  `target.tmp.{pid}.{nonce}`, fsync, rename). On the same filesystem
  this is atomic; cross-filesystem writes fall back to copy+rename
  with a warning. Mode bits, owner, and (on Linux) extended attributes
  are preserved by reading them from the input before the rename.
  See §4c.1 for atomic-write details.
- **Exit codes:** extend `CliError.exitCode` (`CLI.lean:137-141`):
  `5 = validationFailed` (validation refused to write),
  `6 = atomicWriteFailed` (rename or fsync failed; nothing written).
- **Output:** failures go to stderr, one per line, format
  `<filename>: validate: <message>` (matches `Main.lean:200`).
  Order: predicate index, then section/phdr index within predicate.

#### 4c.1 Atomic write (Phase 0, ~60-80 LOC realistic budget)

`IO.FS.writeBinFileAtomic` lives in a new
`Patchelf/IOAtomic.lean`. Approximate shape:

```lean
def writeBinFileAtomic (target : System.FilePath) (bytes : ByteArray)
    (preserveMode : Bool := true) : IO Unit := do
  let dir       := target.parent.getD "."
  let stem      := target.fileName.getD ""
  let nonce     ← randomNonce 8        -- avoid collisions with parallel patchelf
  let pid       ← getPid
  let tmpName   := s!".{stem}.tmp.{pid}.{nonce}"
  let tmpPath   := dir / tmpName
  let mode      ← if preserveMode then some <$> IO.FS.getMode target else pure none
  IO.FS.writeBinFile tmpPath bytes
  IO.FS.fsyncFile tmpPath              -- file contents on disk
  IO.FS.fsyncDir dir                   -- directory entry on disk (NFS-correct)
  IO.FS.rename tmpPath target          -- atomic on same FS
  match mode with
  | some m => IO.FS.setMode target m
  | none   => pure ()
```

Honest budget breakdown:
- Core write+fsync+rename: 25 LOC
- Cross-filesystem fallback (rename returns `EXDEV`): 15 LOC
- Mode preservation: 10 LOC
- Lean `IO.FS.fsyncFile` / `fsyncDir` bindings (likely missing
  upstream): 20 LOC of `@[extern]` bindings
- xattr/ACL preservation on Linux: deferred (most patchelf use cases
  don't carry SELinux contexts on the patched file; document the gap)
- Concurrent invocation: not handled. patchelf is per-invocation;
  two simultaneous invocations on the same target file will race.
  Document this as the user's problem.

**Total: ~70 LOC.** The earlier ~20 LOC estimate was optimistic.

### 4d. Tier 2 test harness

`lean/tests/run-real.sh` (NEW, ~30 LOC) — parallel to
`tests/run.sh`, exit-77-as-SKIP convention, oracle discovery
(`eu-elflint`, `readelf`).

`lean/tests/cases-real/` (NEW, 12 files × ~12 LOC):

The first action is to wire the upstream fixture
`/Users/cbaker2/ext-sources/patchelf/tests/no-rpath-prebuild/no-rpath-amd64`
into `lean/tests/fixtures/` (symlink). It is 9514 bytes, ELF64,
real glibc binary; PT_LOAD #2 covers `[0x0, 0x6a4)` and spans
`.dynstr` (`[0x308, 0x345)`) through `.eh_frame`. `.dynstr` ends
at 0x345 with `.gnu.version` starting at 0x346 — exactly 1 byte
of slack. Adding any DT_NEEDED triggers reflow, triggers the
PT_LOAD-stale-offset bug. This is the killer reproducer that the
synthetic `tests/cases/*.sh` fixtures (all PT_LOAD `[0, 64)`,
isolated from reflow effects) cannot expose.

Each test asserts (a) exit code, (b) input-file byte-equality to a
backup, (c) stderr content (if any). Predictions are tentative until
§4f.5 empirical verification.

| # | Test | On master (no flags) | After Phase 0 (default) | After Phase 3 |
|---|---|---|---|---|
| 1 | `--validate-only` on pristine fixture | n/a | exit 0; file unchanged | exit 0 |
| 2 | `--print-rpath` byte-roundtrip | exit 0; file unchanged | exit 0; file unchanged | exit 0 |
| 3 | `--set-rpath /foo file` | exit 0; **CORRUPTED FILE** | exit 5; stderr cites `sectionFileInSomePtLoad`; file unchanged | exit 0; file is loadable |
| 4 | `--set-rpath` then `eu-elflint --strict` (assumes Phase-3 success) | corrupted output → eu-elflint fails | refuse-to-write → eu-elflint runs against unchanged input → passes | mutated output passes eu-elflint |
| 5 | `--set-rpath` then PT_LOAD-coverage via `readelf -lW`+`-SW` | broken | refuse-to-write; PT_LOAD coverage of unchanged binary holds trivially | mutated binary's PT_LOAD covers the moved sections |
| 6 | `--add-needed libfoo.so file` | exit 0; **CORRUPTED FILE** | exit 5; refuse-to-write | exit 0; loadable |
| 7 | `--replace-needed libc.so.6 libnewname.so.6 file` | exit 0; CORRUPTED | exit 5; refuse-to-write | exit 0 |
| 8 | `--set-interpreter /foo/ld file` | exit 0; CORRUPTED | exit 5; refuse-to-write | exit 0 |
| 9 | `--set-soname libnew.so` then DT_STRSZ matches | passes (syncDtStrszInFile handles) | exit 0 (or exit 5 if DT_STRSZ-side bug surfaces; verify) | passes |
| 10 | i386 fixture: graceful exit | exit 2 (parseFailed; parser ELF64-only) | exit 2 | exit 2 |
| 11 | `--no-validate --set-rpath /foo file` (regression switch test) | n/a | exit 0; **CORRUPTED FILE** (intentional opt-out) | exit 0; file is loadable |
| 12 | `--set-rpath /foo file` mid-write SIGKILL (atomic-write test) | input corrupted (was a `writeBinFile` race) | input unchanged (atomic rename never happened) | input unchanged |

**The deliverable artifact of Phase 0 is no broken output by default.**
The 6 invocations that today silently corrupt binaries now refuse to
write. Phase 3's acceptance test is "those same 6 invocations succeed
without `--no-validate` and produce loadable bytes."

### 4e. CI

`.github/workflows/lean-test.yml` (NEW, ~35 LOC):

- macOS Tier 1 only (no `eu-elflint` by default; Tier 2 would mostly SKIP)
- Ubuntu Tier 1 + Tier 2 with `apt-get install binutils elfutils file`

Tier 1 hard-fails on both platforms. Tier 2 hard-fails on Ubuntu —
the point is to expose failures.

The macOS runner uses `actions/checkout@v5 + leanprover/lean-action@v1`;
the Lean toolchain caches via the action.

### 4f. Phase 0 acceptance gate

1. `lake build` clean, zero `sorry`, zero new axioms.
2. `tests/run.sh` 49/49 PASS. (Note: this requires the synthetic
   fixtures in `tests/cases/` to remain trivially valid under the
   on-by-default `--validate` — they are, because PT_LOAD `[0, 64)`
   covers every section in the synthetic fixtures.)
3. `tests/run-real.sh` 10/10 PASS, where:
    - 4 tests PASS via the happy path (validation passes, atomic
      write succeeds).
    - 6 tests PASS via the **refuse-to-write path** (validation
      fails on `.dynstr`-growing ops on `no-rpath-amd64`; exit 5;
      input file unchanged on disk; appropriate diagnostic on
      stderr). Each test asserts the input file is byte-identical
      to the pre-invocation backup, AND exit code 5, AND stderr
      mentions a specific predicate.
4. `--validate` wall time <100ms on the 9514 B fixture.
5. **Empirical confirmation of test predictions before locking CI:**
   for each of tests 3–8, run the op against the fixture, capture
   the stderr diagnostic, and assert it in the test. Predictions
   in §4d are not authoritative until empirically verified.
6. **Atomic-write smoke test:** simulate a crash mid-write (kill -9
   between rename-prep and rename-exec via a fault-injection wrapper),
   verify the input file is intact. ~20 LOC of test harness.
7. **`--no-validate` smoke test:** verify the previous broken
   behavior is still reachable for users who explicitly opt out.
   This is the regression switch test.
8. `lean/STATUS.md` and `research/ROADMAP.md` updated.
9. CI workflow runs to completion on PR; Tier 1 green, Tier 2 green
   (all PASS, but with 6 of them taking the refuse path — visible in
   per-test logs).
10. `Patchelf/AxiomCheck.lean` pinned set unchanged.

## 5. Unification refactor (between Phase 0 and Phase 3)

Collapses byte-layer `ElfFile` + typed `ValidElfFile` + `Adapter`
into a single `Elf` type. **Net −4,800 LOC** (estimated; the
estimate carries the historical 1.5–2× understatement risk and
should be treated as a ceiling, not a target).

### 5a. What disappears

| File / artifact | LOC | Reason |
|---|---:|---|
| `Patchelf/Elf/Adapter.lean` | 361 | No two layers to bridge |
| `Patchelf/Elf/AdapterRoundtrip.lean` | 103 | Obviated |
| `Patchelf/Elf/ElfFile.lean` (most) | ~600 of 778 | Replaced by single `Elf` (~450 LOC); structural fields move into the typed model |
| `EncodePreconditions` bundle (`ByteRoundtrip.lean:2206-2825`) | ~600 | Each clause becomes a type invariant of `Elf` |
| `DecodeRoundtripWitness` (`ByteRoundtrip.lean:2162`) | ~50 | Replaced by direct T1 |
| `IsValid` 8-clause structure + decidable | ~150 | Vacuous on `Elf` (clauses are type invariants) |
| Encoder pipeline / LayoutEngine foldl-induction proofs (`LayoutEngine.lean` proofs + `Encoder.lean:203-637`) | ~600 of ~947 | Replaced by `Layout.apply` returning a subtype with constructive `IsLoadable` witness |

### 5b. What stays / changes shape

- The 14 ops migrate to operate on `Elf` directly. Each gets
  shorter (no Adapter detour); `_observable` theorems carry over
  largely unchanged (they speak about typed-section state).
- The DSL (`SchemaDSL.lean`) gains the EverParse Injective+DSL
  pattern[^5] — `serializer_correct + injective ⟹
  serializer_complete`. This collapses ~600 LOC of per-struct
  hand-written `_decode_write` lemmas into uniform DSL emission.
  See [`RESEARCH-SCHEMA-DSL.md`](RESEARCH-SCHEMA-DSL.md) §"DSL v3"
  for the design sketch.
- An `OpaqueSection` variant carries currently-unmodeled byte
  regions (text, data, rela.* sections, notes) verbatim. It is
  the verification escape hatch — theorems about `Elf` that don't
  need to inspect opaque content are unaffected; theorems that do
  must propagate through byte-equality (~100 LOC of plumbing).

### 5c. Migration strategy

The `OpaqueSection` carrier is the safety valve: any byte region
the typed model doesn't understand becomes an opaque blob,
encoded back verbatim at the same offset. This lets the migration
proceed without expanding the typed-section coverage; expansion
becomes a follow-up.

Acceptance gate for the unification:

1. All 49 shell tests still pass.
2. All 6 Tier 2 fail-on-master tests still fail (this is
   correctness preservation across the refactor — the bug must
   continue to be exposed; if a Tier 2 test silently flips to
   PASS during unification, something has changed semantically).
3. Top-level theorems T1 / T2 / T3 are stated (proofs on the
   unified type can be partial pending Phase 3, marked `sorry`
   only on the Phase-3-specific goals).
4. Zero new axioms; `Patchelf/AxiomCheck.lean` pinned set
   unchanged.

## 6. Phase 3 — `LayoutPlan` / `apply` / growEOF

**Goal:** produce loader-coherent bytes for every successful run.
The 6 Tier 2 fail-on-master tests flip to PASS without test
changes.

**Budget:** 1500–2400 LOC. The dominant cost is `apply_isLoadable`
(700–1000 LOC of per-strategy proof obligations).

### 6a. `LayoutPlan` and strategies

```lean
inductive LayoutMode where
  | inPlace      -- never grow file; fail if can't fit
  | growEOF      -- ET_DYN + ET_PIE: append new region after EOF, rewrite PT_LOAD
  | extend       -- ET_EXEC: C++ patchelf's rewriteSectionsExecutable analog

inductive LayoutError where
  | sectionTooLargeForSlot (idx : Nat) (need have : Nat)
  | ptLoadCoverageLost     (segIdx : Nat)
  | inPlaceRefused          (reason : String)
  | extendRequiresPhdrSlack (need : Nat)

structure LayoutPlan (e : Elf) where
  mode           : LayoutMode
  newOffsets     : Array (Fin e.sections.size × FileOffset)  -- only changed sections
  newShoff       : FileOffset
  phdrRewrites   : Array (Fin e.phdrs.size × ProgramHeader)
  newPhdrs       : Array ProgramHeader  -- extend mode only
  -- Decidable correctness witness, embedded.
  disjoint       : SpliceDisjointAfter e mode newOffsets newShoff phdrRewrites newPhdrs
  ptLoadCovers   : PtLoadCoverageHolds e mode newOffsets phdrRewrites newPhdrs

def planFor (e : Elf) (mode : LayoutMode) :
    Except LayoutError (LayoutPlan e)

def apply (e : Elf) (p : LayoutPlan e) :
    { e' : Elf // Loader.IsLoadable e' }
```

`apply` returns a subtype: there is no path from `ops.foldl` to
`encode` that produces an `Elf` without a `IsLoadable` witness.

Three strategies are needed:

- **`growEOFStrategy`** (primary, ET_DYN/ET_PIE). Appends a new
  region at file end; rewrites the matching PT_LOAD's `p_offset`,
  `p_filesz`, `p_memsz` (and adds a new PT_LOAD if the existing
  one has no slack). The C++ analog is
  `patchelf.cc:806 rewriteSectionsLibrary`[^6]. Most modern
  binaries (gcc-built, glibc-2.6+) are ET_DYN.
- **`extendStrategy`** (mandatory for ET_EXEC). The C++ analog
  is `patchelf.cc:974 rewriteSectionsExecutable`[^7]. Extends the
  last PT_LOAD or carves space; PT_PHDR-specific gymnastics. The
  earlier "ET_DYN-only" framing was wrong — empirically ET_EXEC
  is 30–40% of real binaries (pre-2016 Debian, RHEL 6/7, embedded
  MIPS/ARM, glibc-static-linked, anything older than gcc-6's
  PIE-by-default).
- **`inPlaceStrategy`** (optional, byte-stability optimization).
  Only fires when `canEditInPlace` holds — a stronger predicate
  than today's `LayoutEngine.layoutAlreadyValid` (see §6c).

`chooseStrategy : Elf → LayoutMode` dispatches based on `e_type`,
defaulting to `growEOF` for ET_DYN/ET_PIE and `extend` for ET_EXEC.

### 6b. `syncDtAddressesInFile` — the missing rewrite

C++ patchelf's `rewriteHeaders` (`patchelf.cc:1244-1318`[^8])
rewrites 10 DT_* entries to point at the new section addresses
after reflow:

```
DT_STRTAB  → .dynstr           DT_VERSYM  → .gnu.version
DT_SYMTAB  → .dynsym           DT_JMPREL  → .rel.plt / .rela.plt / .rela.IA_64.pltoff
DT_HASH    → .hash             DT_REL     → .rel.dyn / .rel.got
DT_GNU_HASH→ .gnu.hash         DT_RELA    → .rela.dyn
DT_VERNEED → .gnu.version_r    DT_MIPS_RLD_MAP_REL → (computed)
```

The Lean port currently rewrites **zero** of these. `syncDtStrszInFile`
handles only DT_STRSZ. This is a correctness gap independent of
PT_LOAD coverage: even if PT_LOAD covers the new section locations,
DT_STRTAB still points at the old vaddr.

A new `syncDtAddressesInFile : Elf → LayoutPlan e → Elf` is part
of `apply`. Driven by a static rewrite table:

```lean
structure DynTagRewriteRule where
  tag           : DynTag
  sectionName   : ByteArray
  fallbackNames : List ByteArray := []   -- DT_JMPREL: [".rel.plt", ".rela.plt", ...]
  required      : Bool                    -- DT_JMPREL=true; DT_GNU_HASH=false
  transform     : SectionAddr → DynEntryContext → UInt64 := fun a _ => a.val
                                          -- MIPS_RLD_MAP_REL has nontrivial transform
```

`patchDynamicEntries` (`Adapter.lean:193-287`) is NOT deleted in
Phase 3 — it remains the bridge for typed-modeled DT_* entries
(DT_NEEDED, DT_RPATH, etc.). `syncDtAddressesInFile` operates
only on the byte-layer DT_* address tags above. This split was
unclear in Phase 2 drafts.

### 6c. Page sizes from `e_machine`

`--page-size` is currently dead code (`grep -rn pageSize` returns
only 2 sites in `CLI.lean`). Phase 3 introduces:

```lean
def pageSizeFor : Elf.Machine → Nat
  | .x86_64       => 0x1000   -- 4 KiB
  | .i386         => 0x1000
  | .aarch64      => 0x10000  -- 64 KiB — non-negotiable
  | .arm          => 0x1000
  | .riscv        => 0x1000
  | .powerpc64    => 0x10000
  | .loongarch    => 0x10000
  | _             => 0x1000   -- conservative default
```

Resolution policy:
- If `--page-size N` provided, use N.
- Else use `pageSizeFor e.header.machine`.
- Reject if user-supplied N is inconsistent with `e_machine`'s
  well-known minimum (e.g., `--page-size 4096` on AArch64 → error,
  not silent CVE).

This must land in Phase 3, not be deferred. Hardcoding 4096
silently corrupts AArch64 binaries; AArch64 is ~30% of new Linux
deployments.

### 6d. `canEditInPlace` ≠ `layoutAlreadyValid`

`LayoutEngine.layoutAlreadyValid` (`LayoutEngine.lean:46-47`) is
`decide (e.sectionsNonOverlapping ∧ e.shdrSectionDisjoint)` — 2
of the 7 `spliceRegionsDisjoint` clauses. It is an **optimization
gate** ("should I run the layout pass?"), not a **safety
predicate** ("is editing in place safe?").

The optional in-place strategy needs a stronger predicate:

```lean
def canEditInPlace (e : Elf) (op : Op) : Bool :=
  let m := op.mutation e   -- LayoutMutation from Phase 0
  e.layoutAlreadyValid (op.apply e) ∧
  ¬m.requiresPtLoadGrow ∧
  m.dynstrDelta ≤ slack(e, .dynstr) ∧
  m.dynamicEntryDelta ≤ slack(e, .dynamic)
```

Empirically, on the upstream `no-rpath-amd64` fixture, every
`.dynstr`-growing op has `slack(e, .dynstr) = 1`, so
`canEditInPlace` returns false for ~95% of real invocations.
This is the right answer.

### 6e. Atomic write — moved to Phase 0

Originally in Phase 3, moved to Phase 0 §4c.1 after adversarial
review. Atomic write is independent of the layout work and addresses
a separate corruption class (partial-write-on-crash). No reason to
defer.

### 6f. Phase 2 test ledger

The 49 shell tests are structurally coupled to today's
"always reflow" semantics. Phase 3 replaces reflow with strategy
dispatch. Expected impact:

- **Pass unchanged (~41):** all `--print-*` ops, all read-only
  ops, ops on synthetic fixtures small enough that growEOF is
  trivially correct.
- **Behavioral change, no test change needed (~6–8):** ops that
  trigger reflow on synthetic fixtures. The bytes change (new
  PT_LOAD or extended PT_LOAD), but the existing post-condition
  checks (DT_NEEDED present, RPATH set, etc.) still pass.
- **Refused / requires fixture update (0 expected):** the synthetic
  fixtures' PT_LOAD `[0, 64)` shape doesn't trigger growEOF in
  problematic ways.

Tier 2 tests 3–8 flip from FAIL to PASS — that is Phase 3's
acceptance test.

### 6g. Phase 3 acceptance gate

1. `lake build` clean, zero `sorry`, zero new axioms.
2. `tests/run.sh` 49/49 PASS.
3. `tests/run-real.sh` 12/12 PASS via the **happy path** (the 6
   refuse-to-write tests from Phase 0 flip to mutate-and-succeed).
4. T1 / T2 / T3 proven (no `sorry` in `Roundtrip.lean`).
5. **Real-binary corpus differential.** Specification:
   - **Corpus source:** captured statically from a single Nixpkgs
     evaluation hash (committed to repo as a manifest of
     SHA-256+path), 30 binaries: 10 ET_DYN from
     `nixpkgs.coreutils.outPath/bin`, 10 ET_EXEC from a CentOS-7
     glibc-static rootfs tarball (committed as a manifest), 5
     AArch64 from `nixpkgs.coreutils.aarch64Out`, 5 PowerPC64 from
     a Debian-bookworm ppc64el chroot. Manifest format: TSV with
     hash + URL + arch + e_type.
   - **Capture mechanism:** `tests/corpus/fetch.sh` downloads via
     SHA-256 verification; cached in `tests/corpus/.cache/`; CI
     restores from artifact cache.
   - **CI scope:** runs in a separate workflow job
     `tier3-corpus-differential` that triggers on PR labels
     `corpus-test` or on `master` push. Default PR runs do NOT
     hit this job (it takes 5-15 min).
   - **Pass criterion:** for each binary in the corpus, run a
     mutation op (varies per binary), then run `eu-elflint
     --strict` and `readelf -a` on the output. Both must succeed.
6. `Patchelf/AxiomCheck.lean` pinned set unchanged.

## 7. Why this design

Salient findings from adversarial review:

- **Phase 2 alone is near-vacuous on real binaries.** Every
  `.dynstr`-growing op on `no-rpath-amd64` overflows the 1-byte
  slack. Realistic Phase-2-only invocation coverage is 5–15%, not
  the 70% earlier drafts claimed.
- **`canEditInPlace ≠ layoutAlreadyValid`.** The latter is an
  optimization gate; the former is a safety predicate. Conflating
  them was a BLOCKER finding.
- **The "loader contract" is plural.** Linux kernel, glibc, musl,
  and FreeBSD diverge on DT_NEEDED resolution, GNU-hash chain
  validity, RUNPATH-vs-RPATH, PT_GNU_PROPERTY enforcement. Pin
  explicitly to Linux+glibc.
- **Page sizes can't be hardcoded 4096.** AArch64 is non-negotiable.
  `--page-size` is dead code today.
- **10 DT_* address tags are unrewritten.** `patchDynamicEntries`
  preserves them verbatim; the C++ analog at `cc:1244-1318`
  rewrites all 10. The Lean port's "DT_NEEDED works fine" anecdote
  is misleading because typed-modeled tags do work — it's the
  byte-layer-only address tags that don't.
- **ET_EXEC is not <10%.** Pre-2016 Debian, RHEL 6/7, embedded
  MIPS/ARM, glibc-static, gcc <6 — empirically 30–40%. Phase 3
  must include `extendStrategy`, not only `growEOFStrategy`.
- **`apply_isLoadable` LOC dominates Phase 3.** Estimated 700–1000
  of the 1500–2400 budget. Earlier "Phase 3 is ~600-800 LOC"
  estimates were off by 2–3×.

## 8. Open questions and risk register

### 8a. LOC budget honesty

Estimates carry the project's historical 1.5–2× understatement risk
(per memories `uint64_to_nat_migration` and
`layoutForEncoding_spliceRegionsDisjoint`: prior major refactors
were 354 actual vs ~150-300 claim, and 561 actual vs ~150-300 claim).
Realistic budgets:

| Component | Optimistic (doc text) | Realistic (1.5-2× adjusted) |
|---|---:|---:|
| Phase 0 total | ~470 LOC | ~600-800 LOC |
| Atomic write (§4c.1) | ~70 LOC | ~100 LOC |
| Unification refactor | −4,800 LOC | −2,500 to −3,500 LOC |
| Phase 3 total | 1,500-2,400 LOC | 2,500-4,000 LOC |
| `apply_isLoadable` proof | 700-1,000 LOC | 1,000-1,500 LOC |

The Phase 3 timeline (§1.5) uses the realistic upper bound: ~12
calendar months at 20 hours/week steady cadence. If the unification
LOC saving lands closer to −2,500 than −4,800, the case for Phase 3
on the unified `Elf` weakens but does not break — the proof
discharge halving still applies.

### 8b. OpaqueSection coverage

The `OpaqueSection` carrier (§5b) was framed as an "escape hatch
for currently-unmodeled byte regions." Empirical reality: text /
data / rela.* / debug.* / note.* sections are the **bulk** of any
binary. On `no-rpath-amd64` (9514 bytes), typed sections total
~1100 bytes; opaque content is ~8400 bytes (88%). Theorems about
the unified `Elf` that touch any opaque region must propagate
byte-equality. Earlier estimate of "~100 LOC of plumbing" was
off; realistic budget is **300-500 LOC**, included in the
unification refactor's net total above.

### 8c. ROADMAP item dispositions

The original [`ROADMAP.md`](ROADMAP.md) had 8 deferred items in §3
(feature parity with C++ patchelf). This design supersedes some
and not others; explicit:

| ROADMAP item | Disposition |
|---|---|
| §1.1 Parser establishes `IsLoadable` | **Subsumed** by Phase 3 §6b (Loader.IsLoadable lifted from decorative to enforced; parser is `Codec.decode` returning typed `Elf`, no separate IsLoadable establishment) |
| §1.2 Pre-encode passes preserve_valid | **Subsumed** by unification (preconditions become type invariants) |
| §3.1 Multi-op canonical ordering | **Out of scope** for this design. Cosmetic; ~30 LOC at the CLI layer; can land as a separate Phase 4 item |
| §3.2 shrinkRPath filesystem probing | **Out of scope.** Belongs at Main.lean layer; no proof obligations |
| §3.3 .gnu.hash rebuild in --rename-dynamic-symbols | **Deferred to Phase 4.** ~150 LOC; not on the path to "never produce broken output" because the op currently rejects binaries with .gnu.hash (precondition prevents broken output) |
| §3.4 .gnu.version_r update in --replace-needed | **Deferred to Phase 4.** Real-world impact minor (loaders resolve via Verdef, not vn_file) |
| §3.5 PT_GNU_STACK append when missing | **Subsumed** by Phase 3's `extendStrategy` infrastructure; falls out as a one-liner once layout dispatch handles phdr table growth |
| §3.6 --page-size actually used | **Subsumed** by Phase 3 §6c (page sizes derived from e_machine, --page-size respected) |
| §3.7 --debug verbose trace output | **Out of scope.** Tooling; no correctness implication |
| §3.8 Per-clause ParseError classification | **Subsumed** by Phase 0 §4a (unified Diagnostic catalogue) |
| §5.1 Op-level byte roundtrip lemmas | **Subsumed** by Phase 3 T3 (op-level Tier D becomes trivial under the unified Elf model) |
| §5.2 Op-level _observable completeness | **Out of scope** for this design but tracked separately. Three ops (renameDynamicSymbols, addDebugTag, removeNeeded) have weak observables. ~150 LOC |

### 8d. GNU-hash chain validity

`Loader.IsLoadable` checks `.gnu.hash` is in a PT_LOAD but not chain
semantics (§4b.1). A malformed chain SIGSEGVs glibc. **Phase 3 may
add `gnuHashChainValid` as a 17th predicate** if the proof scope
fits; otherwise it is a Phase 4 item. Currently no Lean port op
manipulates `.gnu.hash` directly (—rename-dynamic-symbols rejects
binaries with `.gnu.hash`), so the gap is latent rather than
exploitable.

### 8e. ET_REL / ET_CORE handling

Phase 3's strategy dispatch handles ET_DYN and ET_EXEC. Other
`e_type` values:
- **ET_REL** (relocatable .o files): patchelf semantically doesn't
  apply (no PT_LOAD; no dynamic linking). `chooseStrategy` returns
  `LayoutError.unsupportedEType`; CLI emits a clear diagnostic.
  Captured in Phase 3 §6a; explicit predicate at parse-time.
- **ET_CORE** (core dumps): same disposition as ET_REL.
- **ET_NONE / ET_LOPROC..ET_HIPROC**: rejected at parse-time as
  "unrecognized e_type."

This is a Phase 0 add: parser-level rejection is a one-line guard
on `e.header.type`. Land it with the validator predicates.

### 8f. Interim-period user safety

Between Phase 0 ship and Phase 3 ship (~4-12 calendar months), the
tool refuses-to-write on cases that today silently corrupt. Users
of `patchelf --add-needed libfoo.so /usr/bin/ls` get exit 5 instead
of broken bytes. **Communication plan:**
- `--help` text documents `--validate` is on by default and lists
  the predicates checked.
- Refuse-to-write diagnostics include a one-line pointer:
  `(Phase 3 will land actual support; until then, use the C++
  reference patchelf or report this case if it is novel.)`
- `STATUS.md` "What works end-to-end" table flips columns to
  distinguish "works" from "refuses" from "broken silently."

### 8g. Phase 0 empirical verification gates

§4f.5 requires running the predicted ops against the fixture
before locking the test suite. Specifically:
- Predicted FAIL tests (3-8): confirm each op actually triggers
  the predicate that the test asserts. If `--set-rpath /foo` does
  not actually grow `.dynstr` on the fixture (e.g., `/foo` already
  appears as a substring), the prediction is wrong and the test
  needs a different op or a different fixture.
- Predicted PASS tests (1, 2, 9, 10): confirm via a dry run.
- Predicted refuse-to-write atomic-write test (12): build the
  fault-injection harness and exercise it.

### 8h. Worktree isolation for the unification refactor

The refactor touches ~40 files; we may want to land it as a long-
running branch with periodic merges from master, rather than a
single mega-PR. Decide before starting. (Argues for a long-running
branch given the ~6-10 week timeline.)

### 8i. DSL Injective+DSL pattern spike

The EverParse pattern is estimated to save ~600 LOC, but DSL
extension has historically been bumpy.  If the saving lands at
+0 LOC, the unification budget tightens by ~7%.  **Recommend a
1-week spike before committing,** porting one struct end-to-end
as a feasibility check.

### 8j. `Op.spec` dispatcher size

~22 ops × 1-3 spec clauses each = ~50 cases. Term-mode case-splits
on inductives are heavyweight in Lean. May need to be a typeclass
or a pattern-match table. Decide before §6 implementation.

### 8k. `pageSizeFor` table for less-common architectures

Need to verify SPARC, IA-64, m68k, s390x default page sizes.
Out-of-scope architectures fall through to 4096 with a runtime
warning ("page size 4096 assumed for unknown e_machine 0x{N};
binary may not load on the target system"); Phase 0 documents
this.

### 8l. musl / FreeBSD / Solaris support

Out of scope per §1. Alpine-musl is ~5-10% of NixOS users and
most Docker base images. Disposition:
- `--help` text: "musl libc is not supported. Output binaries
  may pass --validate but fail on Alpine / muslc Docker images."
- STATUS.md "Out of scope" section lists musl, FreeBSD rtld,
  Solaris, bionic with explicit e_machine implications.
- Phase 4 may extend the loader contract to musl if there is
  user demand. ~300-500 LOC additional predicates (musl rejects
  some PT_LOAD layouts glibc accepts).

### 8m. `encodedFileSize` exposure

`encodedFileSize` is a top-level `def` at
`Patchelf/Elf/Encoder.lean:66`; no refactor is needed.  Predicate
#4 (`ptLoadFileBoundsFit`) imports Encoder for this single name.

### 8n. Concurrent CI corpus runs

Phase 3 §6g acceptance gate now specifies the corpus mechanism
explicitly. Open question: should the corpus be re-fetched on
every CI run or pinned via SHA-256 to a manifest? (Recommend
pinned, with quarterly manual refresh.)

## 9. Glossary

- **byte layer / typed layer.** The current architecture has two
  representations: `ElfFile` (raw bytes + section offsets) and
  `ValidElfFile` (typed sections with cross-section invariants).
  Bridged by `Adapter`. The unification refactor (§5) collapses
  them.
- **Tier 2.** Real-binary test harness using upstream fixtures
  and external oracles (`eu-elflint`, `readelf`). Distinguished
  from Tier 1 (synthetic-fixture suite) and Tier D
  (`parse_encode_roundtrip`-style proof obligations).
- **growEOF.** Layout strategy that appends new file content past
  the original EOF and rewrites PT_LOAD to cover it. Works on
  ET_DYN / ET_PIE because the loader can place the segment
  anywhere.
- **extend.** Layout strategy that grows the last PT_LOAD in
  place. Required for ET_EXEC because PT_LOAD vaddrs are
  fixed.

## References

[^1]: `tests/cases/` in this repository documents several known
    issues in C++ patchelf via fixtures and shell tests. STATUS.md
    §"Bug audit" has additional notes.

[^2]: Linux kernel source, `fs/binfmt_elf.c:load_elf_binary`,
    upstream HEAD ≥4.14 stabilizes the PT_LOAD page-alignment
    check semantics relevant here.

[^3]: glibc source, `elf/dl-load.c:_dl_map_object_from_fd` and
    `elf/dl-deps.c:_dl_map_object_deps`. Versions ≥2.31 (released
    Feb 2020) are the union target; older glibcs may accept
    binaries this port produces but we don't commit to it.

[^4]: bionic = Android's libc. Out of scope; Android uses
    additional `.note.android.ident` checks and a different
    DT_VERSYM resolution path.

[^5]: EverParse "Injective + DSL" pattern: `serializer_correct +
    injective ⟹ serializer_complete`. Memory entry
    `everparse_injective_pattern.md` has pointers to the upstream
    F* sources.

[^6]: `/Users/cbaker2/ext-sources/patchelf/src/patchelf.cc:806`,
    function `rewriteSectionsLibrary`. Comments at the top
    document the ET_DYN strategy.

[^7]: `src/patchelf.cc:974`, function `rewriteSectionsExecutable`.
    Roughly 150 LOC; PT_PHDR-specific handling at lines 990–1020.

[^8]: `src/patchelf.cc:1244-1318`, function `rewriteHeaders`.
    The 14-arm `if-else` ladder over `d_tag` values.
