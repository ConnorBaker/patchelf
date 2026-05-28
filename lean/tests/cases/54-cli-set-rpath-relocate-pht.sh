#!/bin/sh -e
# CLI: --set-rpath on a binary that needs the `relocatePht` sub-case
# (ROADMAP §3.5a follow-up).  Covers the full BSS-heavy class:
#
# Coreutils `ls`:
#   * Last PT_LOAD has filesz=0xcbbc / memsz=0xa3de8 (~600 KB BSS).
#     `canExtendLastPtLoad` rejects.
#   * Phdr table is packed tight against `.note.gnu.build-id`
#     (phdrs at [0x40, 0x350), section 1 at 0x350).
#     `canAddFreshPtLoad` rejects (no in-place room for one more phdr).
#   * `growEOFWith` therefore takes the `relocatePht` branch:
#     `growEOFWithFreshPtLoadReloc` moves the phdr table itself to
#     the appended region, allocates a brand-new PT_LOAD covering
#     both the relocated phdrs and the moved sections, retargets
#     the PT_PHDR program header to the new location.
#
# Pre-§3.5a-relocatePht: `set-rpath` on `ls` exits 5 (validator
# rejects the `layoutForEncoding` fallback's non-loadable bytes).
# Post: `set-rpath` exits 0; modified binary runs.

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

FIXTURE="/tmp/lean-pe-fixtures/ls"
if [ ! -f "$FIXTURE" ]; then
  echo "SKIP: fixture $FIXTURE not present" >&2
  exit 77
fi

SCRATCH="scratch/54-cli-set-rpath-relocate-pht"
mkdir -p "$SCRATCH"
# Coreutils dispatches by argv[0]; copy as `ls` so basename is right.
cp "$FIXTURE" "$SCRATCH/ls"
chmod u+w "$SCRATCH/ls"

# Set a new rpath.  Must exit 0 (validator-accepted output).
if ! "$PATCHELF_BIN" set-rpath /new/rpath "$SCRATCH/ls" >"$SCRATCH/setrpath.out" 2>&1; then
  echo "FAIL: set-rpath on relocatePht-class binary did not exit 0" >&2
  cat "$SCRATCH/setrpath.out" >&2
  exit 1
fi

# Output's phnum should be 15 (original 14 + 1 fresh PT_LOAD).
after_phnum=$(LANG=C.UTF-8 od -An -j 56 -N 2 -tu2 --endian=little "$SCRATCH/ls" | tr -d ' ')
if [ "$after_phnum" != "15" ]; then
  echo "FAIL: post-op phnum was '$after_phnum', expected 15 (fresh PT_LOAD)" >&2
  exit 1
fi

# Output's phoff should be much larger than 64 (relocated to appended
# region — that's the relocatePht signature).
after_phoff=$(LANG=C.UTF-8 od -An -j 32 -N 8 -tu8 --endian=little "$SCRATCH/ls" | tr -d ' ')
if [ "$after_phoff" -lt 1000000 ]; then
  echo "FAIL: post-op phoff was '$after_phoff', expected >= 1000000 (relocated to appended region)" >&2
  exit 1
fi

# Reparse must succeed.
if ! "$PATCHELF_BIN" parse "$SCRATCH/ls" >"$SCRATCH/parse.out" 2>&1; then
  echo "FAIL: post-op reparse failed" >&2
  cat "$SCRATCH/parse.out" >&2
  exit 1
fi

# rpath should resolve to the new value.
after=$("$PATCHELF_BIN" print-rpath "$SCRATCH/ls")
if [ "$after" != "/new/rpath" ]; then
  echo "FAIL: post-op rpath was '$after', expected '/new/rpath'" >&2
  exit 1
fi

# Sanity: the modified binary should be loadable by the kernel + dynamic
# linker.  ld-linux may not find libgmp/libacl/libattr at /new/rpath
# (the rpath we set is bogus), but we can detect that vs. a SIGSEGV from
# corrupted ELF: a missing-library failure is cleanly handled, a
# SIGSEGV is signal 139.
chmod u+x "$SCRATCH/ls"
"$SCRATCH/ls" / >/dev/null 2>"$SCRATCH/run.err" || rc=$?
rc=${rc:-0}
if [ "$rc" -ge 128 ]; then
  echo "FAIL: modified binary crashed with signal (rc=$rc)" >&2
  cat "$SCRATCH/run.err" >&2
  exit 1
fi

echo "PASS: --set-rpath on relocatePht-class binary used the relocate sub-case"
