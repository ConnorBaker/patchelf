#!/bin/sh -e
# Multi-entry --replace-needed grow path: rename libold.so →
# libbrand.so (not in dynstr), on a binary with multiple DT_NEEDED.
# Verifies the adapter's positional remap correctly renames the
# target entry while leaving the others in their original positions.

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/46-cli-replace-needed-grow-multi"
mkdir -p "$SCRATCH"

python3 - "$SCRATCH/input.elf" <<'PY'
import sys, struct
def u8(v): return bytes([v])
def u16(v): return struct.pack("<H", v)
def u32(v): return struct.pack("<I", v)
def u64(v): return struct.pack("<Q", v)

ident = b"\x7fELF" + u8(2) + u8(1) + u8(1) + u8(0) + (b"\x00" * 8)
hdr = ident + u16(2) + u16(62) + u32(1) + u64(0) + u64(64) + u64(120) \
    + u32(0) + u16(64) + u16(56) + u16(1) + u16(64) + u16(4) + u16(1)

pt_load = u32(1) + u32(5) + u64(0) + u64(0) + u64(0) + u64(64) + u64(64) + u64(4096)
null_shdr = b"\x00" * 64
shstr_shdr = u32(1) + u32(3) + u64(0) + u64(0) + u64(376) + u64(28) \
           + u32(0) + u32(0) + u64(1) + u64(0)
# dynstr = "\0libold.so\0libbar.so\0" — 21 bytes (libbrand.so is NOT there, so grow)
dynstr_shdr = u32(11) + u32(3) + u64(0) + u64(0) + u64(404) + u64(21) \
            + u32(0) + u32(0) + u64(1) + u64(0)
# dynamic at 425, size 48 = 3 entries × 16
dynamic_shdr = u32(19) + u32(6) + u64(0) + u64(0) + u64(425) + u64(48) \
             + u32(2) + u32(0) + u64(8) + u64(16)

shstrtab = b"\x00.shstrtab\x00.dynstr\x00.dynamic\x00"
dynstr = b"\x00libold.so\x00libbar.so\x00"
# DT_NEEDED=1 (libold), DT_NEEDED=11 (libbar), DT_NULL
dynamic = u64(1) + u64(1) + u64(1) + u64(11) + u64(0) + u64(0)

with open(sys.argv[1], "wb") as f:
    f.write(hdr + pt_load + null_shdr + shstr_shdr + dynstr_shdr + dynamic_shdr
            + shstrtab + dynstr + dynamic)
PY

# Replace libold → libbrand (grow path — libbrand not in dynstr).
"$PATCHELF_BIN" --replace-needed libold.so libbrand.so "$SCRATCH/input.elf"

# Expect: libbrand.so first (renamed), libbar.so second (unchanged).
actual=$("$PATCHELF_BIN" --print-needed "$SCRATCH/input.elf")
expected='libbrand.so
libbar.so'
if [ "$actual" != "$expected" ]; then
  echo "FAIL: expected '$expected', got '$actual'" >&2
  exit 1
fi

echo "PASS: --replace-needed (grow) preserves position across multi-entry .dynamic"
