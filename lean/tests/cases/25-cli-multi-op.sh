#!/bin/sh -e
# CLI: multiple op flags in one invocation are applied in order.
# --set-os-abi Linux followed by --print-os-abi should print 3 / Linux.

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/25-cli-multi-op"
mkdir -p "$SCRATCH"

python3 - "$SCRATCH/input.elf" <<'PY'
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
shstr = b"\x00"
with open(sys.argv[1], "wb") as f:
    f.write(hdr + null_shdr + shstr_shdr + shstr)
PY

# Before: should print whatever the original abi is (SysV / 0).
out=$("$PATCHELF_BIN" --set-os-abi Linux --print-os-abi "$SCRATCH/input.elf")

# The print-os-abi should have run AFTER set-os-abi, so we expect 'Linux'.
case "$out" in
  *Linux*) ;;
  *) echo "FAIL: multi-op didn't apply --set-os-abi before --print-os-abi. Got: $out" >&2; exit 1 ;;
esac

# Byte 7 should now be 3 on disk (set really happened).
after=$(od -An -tx1 -N1 -j7 "$SCRATCH/input.elf" | tr -d ' \n')
if [ "$after" != "03" ]; then
  echo "FAIL: post-multi-op byte 7 = $after, expected 03" >&2
  exit 1
fi

echo "PASS: multi-op --set-os-abi Linux --print-os-abi applied in order"
