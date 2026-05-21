#!/bin/sh -e
# CLI: --help and -h both print usage and exit 0.

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/21-cli-help"
mkdir -p "$SCRATCH"

"$PATCHELF_BIN" --help > "$SCRATCH/help" 2>&1
"$PATCHELF_BIN" -h     > "$SCRATCH/h"    2>&1

for f in "$SCRATCH/help" "$SCRATCH/h"; do
  if ! grep -q "usage:" "$f"; then
    echo "FAIL: $f didn't print usage" >&2
    cat "$f" >&2
    exit 1
  fi
done

# Flags expected in the help text.
for flag in --set-rpath --add-rpath --shrink-rpath --force-rpath \
            --print-execstack --output --page-size; do
  if ! grep -q -- "$flag" "$SCRATCH/help"; then
    echo "FAIL: help missing $flag" >&2
    exit 1
  fi
done

echo "PASS: --help/-h print usage listing new flags"
