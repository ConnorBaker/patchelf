#!/bin/sh -e
# CLI: --replace-needed rewrites matching .gnu.version_r vn_file entries
# to point at the new dynstr offset. Without this, the post-replace
# binary's .gnu.version_r still names the old library, which is at best
# cosmetic drift (loaders use Verdef, not vn_file) but at worst confuses
# tools like readelf -V.
#
# This test uses /tmp/lean-pe-fixtures/hello, which has a .gnu.version_r
# entry naming "libc.so.6". Renaming "libc.so.6" → "libreplaced.so.999"
# (a string of identical length to keep things simple, but that doesn't
# actually exist on disk so the binary won't load — we just verify the
# bytes round-trip via readelf).

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

SCRATCH="scratch/50-cli-replace-needed-rewrites-vn-file"
mkdir -p "$SCRATCH"
cp "$FIXTURE" "$SCRATCH/input.elf"
chmod u+w "$SCRATCH/input.elf"

# Pre-condition: vn_file resolves to "libc.so.6".
extract_vn_file() {
  readelf -V "$1" | sed -n 's/.*File: \([^ ]*\).*/\1/p' | head -1
}
pre=$(extract_vn_file "$SCRATCH/input.elf")
if [ "$pre" != "libc.so.6" ]; then
  echo "SKIP: fixture's vn_file isn't libc.so.6 (got '$pre')" >&2
  exit 77
fi

# Replace libc.so.6 with libxxxxxx.so.6 (same length so we don't trigger
# layout repack) — but the typed-algebra grow path appends regardless.
"$PATCHELF_BIN" replace-needed --no-validate libc.so.6 libxxxxxx.so.6 "$SCRATCH/input.elf"

# The renamed binary must reparse.
if ! "$PATCHELF_BIN" parse "$SCRATCH/input.elf" >"$SCRATCH/parse.out" 2>&1; then
  echo "FAIL: post-replace reparse failed" >&2
  cat "$SCRATCH/parse.out" >&2
  exit 1
fi

# DT_NEEDED should resolve to the new name.
needed=$("$PATCHELF_BIN" print-needed "$SCRATCH/input.elf" | head -1)
if [ "$needed" != "libxxxxxx.so.6" ]; then
  echo "FAIL: post-replace DT_NEEDED resolved to '$needed', expected 'libxxxxxx.so.6'" >&2
  exit 1
fi

# The .gnu.version_r vn_file should ALSO point at the new name.
post=$(extract_vn_file "$SCRATCH/input.elf")
if [ "$post" != "libxxxxxx.so.6" ]; then
  echo "FAIL: post-replace .gnu.version_r vn_file is '$post', expected 'libxxxxxx.so.6'" >&2
  exit 1
fi

echo "PASS: --replace-needed rewrites .gnu.version_r vn_file"
