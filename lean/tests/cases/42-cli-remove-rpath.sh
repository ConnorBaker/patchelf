#!/bin/sh -e
# CLI: --remove-rpath drops DT_RPATH and DT_RUNPATH from .dynamic.

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/42-cli-remove-rpath"
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
# dynstr at 404, size 6 = "\0/usr\0" (offset 1 = "/usr")
dynstr_shdr = u32(11) + u32(3) + u64(0) + u64(0) + u64(404) + u64(6) \
            + u32(0) + u32(0) + u64(1) + u64(0)
# dynamic at 410, size 32 = DT_RUNPATH(29) + DT_NULL
dynamic_shdr = u32(19) + u32(6) + u64(0) + u64(0) + u64(410) + u64(32) \
             + u32(2) + u32(0) + u64(8) + u64(16)

shstrtab = b"\x00.shstrtab\x00.dynstr\x00.dynamic\x00"
dynstr   = b"\x00/usr\x00"
# DT_RUNPATH = 29, value = 1 ("/usr"), DT_NULL
dynamic  = u64(29) + u64(1) + u64(0) + u64(0)

with open(sys.argv[1], "wb") as f:
    f.write(hdr + pt_load + null_shdr + shstr_shdr + dynstr_shdr + dynamic_shdr
            + shstrtab + dynstr + dynamic)
PY

before=$("$PATCHELF_BIN" --print-rpath "$SCRATCH/input.elf")
case "$before" in
  *"/usr"*) ;;
  *) echo "FAIL (setup): pre-op rpath was: $before" >&2; exit 1 ;;
esac

"$PATCHELF_BIN" --remove-rpath "$SCRATCH/input.elf"

after=$("$PATCHELF_BIN" --print-rpath "$SCRATCH/input.elf")
if [ -n "$after" ] && [ "$after" != "" ]; then
  case "$after" in
    *"/usr"*) echo "FAIL: rpath still present: $after" >&2; exit 1 ;;
  esac
fi

echo "PASS: --remove-rpath removed DT_RUNPATH"
