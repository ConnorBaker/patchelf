#!/bin/sh -e
# CLI: --print-os-abi emits the ABI name and exits 0.

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/03-cli-print-os-abi"
mkdir -p "$SCRATCH"

# Minimal ELF with EI_OSABI = 3 (Linux).
python3 - "$SCRATCH/input.elf" <<'PY'
import sys, struct
def u8(v): return bytes([v])
def u16(v): return struct.pack("<H", v)
def u32(v): return struct.pack("<I", v)
def u64(v): return struct.pack("<Q", v)

ident = b"\x7fELF" + u8(2) + u8(1) + u8(1) + u8(3) + (b"\x00" * 8)
hdr = ident + u16(2) + u16(62) + u32(1) + u64(0) + u64(0) + u64(64) \
    + u32(0) + u16(64) + u16(56) + u16(0) + u16(64) + u16(2) + u16(1)
null_shdr = b"\x00" * 64
shstr_shdr = u32(0) + u32(3) + u64(0) + u64(0) + u64(192) + u64(1) \
           + u32(0) + u32(0) + u64(1) + u64(0)
shstr = b"\x00"
out = hdr + null_shdr + shstr_shdr + shstr
with open(sys.argv[1], "wb") as f:
    f.write(out)
PY

out=$("$PATCHELF_BIN" print-os-abi "$SCRATCH/input.elf")
if [ "$out" != "Linux" ]; then
  echo "FAIL: expected 'Linux', got '$out'" >&2
  exit 1
fi
echo "PASS: print-os-abi output = '$out'"
