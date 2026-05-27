#!/bin/sh -e
# CLI: --help and -h both print usage and exit 0.  The Lean port uses
# subcommands (e.g. `patchelf set-rpath /a foo`) instead of flag-stacks,
# so help lists subcommand names rather than --flag-name.

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/21-cli-help"
mkdir -p "$SCRATCH"

"$PATCHELF_BIN" --help > "$SCRATCH/help" 2>&1
"$PATCHELF_BIN" -h     > "$SCRATCH/h"    2>&1

for f in "$SCRATCH/help" "$SCRATCH/h"; do
  if ! grep -qi "usage" "$f"; then
    echo "FAIL: $f didn't print usage" >&2
    cat "$f" >&2
    exit 1
  fi
done

# Subcommands expected in the help text.
for sub in set-rpath add-rpath shrink-rpath print-execstack \
            print-os-abi set-soname add-needed validate; do
  if ! grep -q -- "$sub" "$SCRATCH/help"; then
    echo "FAIL: help missing $sub" >&2
    exit 1
  fi
done

echo "PASS: --help/-h print usage listing subcommands"
