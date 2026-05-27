#!/bin/sh -e
# CLI: --no-default-lib rejects missing-dynamic input.
#
# The insert path (DT_FLAGS_1 absent) is exercised by
# 18-cli-no-default-lib-insert.sh now that the layout engine handles
# `.dynamic` grow. The set-bit case (DT_FLAGS_1 already present) is
# exercised by 09-cli-no-default-lib-set.sh.

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/07-cli-no-default-lib"
mkdir -p "$SCRATCH"

# --- No dynamic section --------------------------------------
python3 - "$SCRATCH/minimal.elf" <<'PY'
import sys, struct
def u8(v): return bytes([v])
def u16(v): return struct.pack("<H", v)
def u32(v): return struct.pack("<I", v)
def u64(v): return struct.pack("<Q", v)
ident = b"\x7fELF" + u8(2) + u8(1) + u8(1) + u8(0) + (b"\x00" * 8)
hdr = ident + u16(2) + u16(62) + u32(1) + u64(0) + u64(0) + u64(64) \
    + u32(0) + u16(64) + u16(56) + u16(0) + u16(64) + u16(2) + u16(1)
null_shdr = b"\x00" * 64
shstr_shdr = u32(0) + u32(3) + u64(0) + u64(0) + u64(192) + u64(1) \
           + u32(0) + u32(0) + u64(1) + u64(0)
with open(sys.argv[1], "wb") as f:
    f.write(hdr + null_shdr + shstr_shdr + b"\x00")
PY

rc=0
output=$("$PATCHELF_BIN" no-default-lib "$SCRATCH/minimal.elf" 2>&1) || rc=$?
if [ "$rc" != "3" ]; then
  echo "FAIL: expected exit 3, got $rc" >&2
  echo "output: $output" >&2
  exit 1
fi

echo "PASS: --no-default-lib correctly rejects missing-dynamic input"
