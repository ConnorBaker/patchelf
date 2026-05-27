#!/bin/sh -e
# CLI: --remove-soname drops DT_SONAME from .dynamic.

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/43-cli-remove-soname"
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
# dynstr at 404, size 11 = "\0libc.so\0\0\0" (offset 1 = "libc.so")
dynstr_shdr = u32(11) + u32(3) + u64(0) + u64(0) + u64(404) + u64(11) \
            + u32(0) + u32(0) + u64(1) + u64(0)
# dynamic at 415, size 32 = DT_SONAME(14) + DT_NULL
dynamic_shdr = u32(19) + u32(6) + u64(0) + u64(0) + u64(415) + u64(32) \
             + u32(2) + u32(0) + u64(8) + u64(16)

shstrtab = b"\x00.shstrtab\x00.dynstr\x00.dynamic\x00"
dynstr   = b"\x00libc.so\x00\x00\x00"
# DT_SONAME = 14, value = 1, DT_NULL
dynamic  = u64(14) + u64(1) + u64(0) + u64(0)

with open(sys.argv[1], "wb") as f:
    f.write(hdr + pt_load + null_shdr + shstr_shdr + dynstr_shdr + dynamic_shdr
            + shstrtab + dynstr + dynamic)
PY

before=$("$PATCHELF_BIN" print-soname "$SCRATCH/input.elf")
case "$before" in
  *libc.so*) ;;
  *) echo "FAIL (setup): pre-op soname was: $before" >&2; exit 1 ;;
esac

"$PATCHELF_BIN" remove-soname "$SCRATCH/input.elf"

after=$("$PATCHELF_BIN" print-soname "$SCRATCH/input.elf")
case "$after" in
  *libc.so*) echo "FAIL: soname still present: $after" >&2; exit 1 ;;
esac

echo "PASS: --remove-soname dropped DT_SONAME"
