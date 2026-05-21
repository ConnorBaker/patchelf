#!/bin/sh -e
# CLI: --version prints a version string and exits 0.

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/20-cli-version"
mkdir -p "$SCRATCH"

"$PATCHELF_BIN" --version > "$SCRATCH/out" 2>&1

if ! grep -q "patchelf" "$SCRATCH/out"; then
  echo "FAIL: --version output didn't mention patchelf" >&2
  cat "$SCRATCH/out" >&2
  exit 1
fi

echo "PASS: --version prints a version string"
