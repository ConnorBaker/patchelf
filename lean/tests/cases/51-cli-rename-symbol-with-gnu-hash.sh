#!/bin/sh -e
# CLI: --rename-dynamic-symbol now accepts binaries with .gnu.hash
# (previously rejected with "no .gnu.hash" precondition).
# The op rebuilds .gnu.hash to track the renamed symbols.
#
# This test uses /tmp/lean-pe-fixtures/hello (a glibc-linked binary
# with .gnu.hash).  Renames a weak symbol (__gmon_start__) to a
# new name; the binary must still run because:
#   1. .gnu.hash is rebuilt to point at the renamed symbol's new
#      bucket position.
#   2. The renamed symbol is weak — undefined-at-load is fine.

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

if ! command -v readelf >/dev/null 2>&1; then
  echo "SKIP: readelf not available" >&2
  exit 77
fi

FIXTURE="/tmp/lean-pe-fixtures/hello"
if [ ! -f "$FIXTURE" ]; then
  echo "SKIP: fixture $FIXTURE not present" >&2
  exit 77
fi

# Confirm the fixture has .gnu.hash (otherwise the test is vacuous).
if ! readelf -S "$FIXTURE" | grep -q '\.gnu\.hash'; then
  echo "SKIP: fixture has no .gnu.hash; test is vacuous" >&2
  exit 77
fi

SCRATCH="scratch/51-cli-rename-symbol-with-gnu-hash"
mkdir -p "$SCRATCH"
cp "$FIXTURE" "$SCRATCH/input.elf"
chmod u+w "$SCRATCH/input.elf"

# Rename the weak __gmon_start__ symbol.
"$PATCHELF_BIN" rename-dynamic-symbol __gmon_start__ __zzzz_replaced "$SCRATCH/input.elf"

# Reparse must succeed.
if ! "$PATCHELF_BIN" parse "$SCRATCH/input.elf" >"$SCRATCH/parse.out" 2>&1; then
  echo "FAIL: post-rename reparse failed" >&2
  cat "$SCRATCH/parse.out" >&2
  exit 1
fi

# The renamed symbol must show up in dynsym.
if ! readelf -W --dyn-syms "$SCRATCH/input.elf" | grep -q "__zzzz_replaced"; then
  echo "FAIL: renamed symbol not present in dynsym" >&2
  readelf -W --dyn-syms "$SCRATCH/input.elf" >&2
  exit 1
fi

# The original name must NOT show up.
if readelf -W --dyn-syms "$SCRATCH/input.elf" | grep -q "__gmon_start__"; then
  echo "FAIL: original name __gmon_start__ still in dynsym" >&2
  exit 1
fi

# Critical: the binary must still run (loader must find the .gnu.hash
# entries for the surviving symbols and resolve them).
chmod +x "$SCRATCH/input.elf"
if ! "$SCRATCH/input.elf" >"$SCRATCH/run.out" 2>&1; then
  echo "FAIL: post-rename binary doesn't run (loader rejected .gnu.hash?)" >&2
  cat "$SCRATCH/run.out" >&2
  exit 1
fi

if ! grep -q "hello argv0=" "$SCRATCH/run.out"; then
  echo "FAIL: binary ran but produced unexpected output" >&2
  cat "$SCRATCH/run.out" >&2
  exit 1
fi

echo "PASS: --rename-dynamic-symbol works on .gnu.hash binaries"
