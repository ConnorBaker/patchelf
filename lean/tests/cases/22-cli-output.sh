#!/bin/sh -e
# CLI: --output <FILE> writes the result to FILE instead of overwriting
# the input. Input must remain untouched.

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/22-cli-output"
mkdir -p "$SCRATCH"

# Use the same minimal fixture as case 02.
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

cp "$SCRATCH/input.elf" "$SCRATCH/pristine.elf"

"$PATCHELF_BIN" --set-os-abi Linux --output "$SCRATCH/output.elf" "$SCRATCH/input.elf"

# Input must be unchanged.
if ! cmp -s "$SCRATCH/input.elf" "$SCRATCH/pristine.elf"; then
  echo "FAIL: input file was modified despite --output" >&2
  exit 1
fi

# Output must exist and have byte 7 = 0x03.
if [ ! -f "$SCRATCH/output.elf" ]; then
  echo "FAIL: output file not created" >&2
  exit 1
fi

after=$(od -An -tx1 -N1 -j7 "$SCRATCH/output.elf" | tr -d ' \n')
if [ "$after" != "03" ]; then
  echo "FAIL: output byte 7 = $after, expected 03" >&2
  exit 1
fi

echo "PASS: --output writes to the target and leaves input pristine"
