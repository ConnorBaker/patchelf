#!/bin/sh -e
# CLI: argument values prefixed with '@' are read from the named file
# (C++ resolveArgument compatibility).

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/29-cli-at-file"
mkdir -p "$SCRATCH"

# Fixture from case 02.
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

# Write the abi name to a sidecar file.
echo "Linux" > "$SCRATCH/abi.txt"

# Use @sidecar for the --set-os-abi value.
"$PATCHELF_BIN" --set-os-abi "@$SCRATCH/abi.txt" "$SCRATCH/input.elf"

after=$(od -An -tx1 -N1 -j7 "$SCRATCH/input.elf" | tr -d ' \n')
if [ "$after" != "03" ]; then
  echo "FAIL: @file resolution didn't work; byte 7 = $after, expected 03" >&2
  exit 1
fi

echo "PASS: @file arg resolution reads argument from file"
