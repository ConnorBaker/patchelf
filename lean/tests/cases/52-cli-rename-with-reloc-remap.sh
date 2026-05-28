#!/bin/sh -e
# CLI: --rename-dynamic-symbol on a binary with .gnu.hash AND
# relocations referencing the renamed symbol.  Tests that:
#   1. The .gnu.hash rebuild reorders dynsym (potentially).
#   2. The relocation remap rewrites every r_info that pointed at
#      a moved symbol.
#   3. The resulting binary still runs and the loader resolves
#      symbols via the rebuilt hash table.
#
# Uses /tmp/lean-pe-fixtures/hello (a glibc-linked binary with
# .gnu.hash and .rela.dyn).  Rename a symbol with a very different
# hash from the original (forcing bucket movement), then verify
# the binary runs.

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

# Confirm fixture has both .gnu.hash and .rela.* sections.
if ! readelf -S "$FIXTURE" | grep -q '\.gnu\.hash'; then
  echo "SKIP: fixture has no .gnu.hash; test is vacuous" >&2
  exit 77
fi
if ! readelf -SW "$FIXTURE" | grep -qE 'RELA|REL '; then
  echo "SKIP: fixture has no relocation sections; test is vacuous" >&2
  exit 77
fi

SCRATCH="scratch/52-cli-rename-with-reloc-remap"
mkdir -p "$SCRATCH"
cp "$FIXTURE" "$SCRATCH/input.elf"
chmod u+w "$SCRATCH/input.elf"
chmod +x "$SCRATCH/input.elf"

# Rename a symbol that has a relocation referencing it.
# _ITM_deregisterTMCloneTable is a weak symbol that's referenced by
# .rela.dyn.  Renaming to a very short name forces a different hash
# bucket.
"$PATCHELF_BIN" rename-dynamic-symbol _ITM_deregisterTMCloneTable A "$SCRATCH/input.elf"

# Reparse must succeed.
"$PATCHELF_BIN" parse "$SCRATCH/input.elf" >/dev/null

# The relocation that previously named "_ITM_deregisterTMCloneTable"
# must now name "A".  We verify by parsing readelf -r output.
if ! readelf -W -r "$SCRATCH/input.elf" | grep -q "GLOB_DAT.*A "; then
  echo "FAIL: relocation did not get remapped to renamed symbol 'A'" >&2
  readelf -W -r "$SCRATCH/input.elf" >&2
  exit 1
fi

# The original symbol name must NOT appear in any relocation.
if readelf -W -r "$SCRATCH/input.elf" | grep -q "_ITM_deregisterTMCloneTable"; then
  echo "FAIL: original symbol name still in relocations (remap incomplete)" >&2
  readelf -W -r "$SCRATCH/input.elf" >&2
  exit 1
fi

# The binary must still run.
if ! "$SCRATCH/input.elf" >"$SCRATCH/run.out" 2>&1; then
  echo "FAIL: post-rename binary doesn't run" >&2
  cat "$SCRATCH/run.out" >&2
  exit 1
fi

if ! grep -q "hello argv0=" "$SCRATCH/run.out"; then
  echo "FAIL: binary ran but produced unexpected output" >&2
  cat "$SCRATCH/run.out" >&2
  exit 1
fi

echo "PASS: rename + reloc remap on .gnu.hash binary"
