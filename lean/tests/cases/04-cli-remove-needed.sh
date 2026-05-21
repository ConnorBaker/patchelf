#!/bin/sh -e
# CLI: --remove-needed drops matching DT_NEEDED entries from .dynamic.
#
# Same fixture shape as test 11 (add-needed) but with TWO pre-existing
# DT_NEEDED entries; we remove one.

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/04-cli-remove-needed"
mkdir -p "$SCRATCH"

python3 - "$SCRATCH/input.elf" <<'PY'
import sys, struct
def u8(v): return bytes([v])
def u16(v): return struct.pack("<H", v)
def u32(v): return struct.pack("<I", v)
def u64(v): return struct.pack("<Q", v)

ident = b"\x7fELF" + u8(2) + u8(1) + u8(1) + u8(0) + (b"\x00" * 8)
# phoff=64, shoff=120, phnum=1, shnum=4, shstrndx=1
hdr = ident + u16(2) + u16(62) + u32(1) + u64(0) + u64(64) + u64(120) \
    + u32(0) + u16(64) + u16(56) + u16(1) + u16(64) + u16(4) + u16(1)

pt_load = u32(1) + u32(5) + u64(0) + u64(0) + u64(0) + u64(64) + u64(64) + u64(4096)
null_shdr = b"\x00" * 64
# shstrtab at 376, size 28
shstr_shdr = u32(1) + u32(3) + u64(0) + u64(0) + u64(376) + u64(28) \
           + u32(0) + u32(0) + u64(1) + u64(0)
# dynstr at 404, size 21 = "\0libfoo.so\0libbar.so\0"
dynstr_shdr = u32(11) + u32(3) + u64(0) + u64(0) + u64(404) + u64(21) \
            + u32(0) + u32(0) + u64(1) + u64(0)
# dynamic at 425, size 48 (3 entries × 16 bytes)
dynamic_shdr = u32(19) + u32(6) + u64(0) + u64(0) + u64(425) + u64(48) \
             + u32(2) + u32(0) + u64(8) + u64(16)

shstrtab = b"\x00.shstrtab\x00.dynstr\x00.dynamic\x00"
# dynstr bytes: offset 1 = "libfoo.so", offset 11 = "libbar.so"
dynstr   = b"\x00libfoo.so\x00libbar.so\x00"
# DT_NEEDED(1)=1 ("libfoo.so"), DT_NEEDED(1)=11 ("libbar.so"), DT_NULL
dynamic  = u64(1) + u64(1) + u64(1) + u64(11) + u64(0) + u64(0)

with open(sys.argv[1], "wb") as f:
    f.write(hdr + pt_load + null_shdr + shstr_shdr + dynstr_shdr + dynamic_shdr
            + shstrtab + dynstr + dynamic)
PY

# Before: both libs listed.
before=$("$PATCHELF_BIN" --print-needed "$SCRATCH/input.elf")
case "$before" in
  *libfoo.so*) ;;
  *) echo "FAIL (setup): pre-op output missing libfoo.so: $before" >&2; exit 1 ;;
esac
case "$before" in
  *libbar.so*) ;;
  *) echo "FAIL (setup): pre-op output missing libbar.so: $before" >&2; exit 1 ;;
esac

# Remove libfoo.so.
"$PATCHELF_BIN" --remove-needed libfoo.so "$SCRATCH/input.elf"

after=$("$PATCHELF_BIN" --print-needed "$SCRATCH/input.elf")
case "$after" in
  *libfoo.so*) echo "FAIL: libfoo.so still listed: $after" >&2; exit 1 ;;
esac
case "$after" in
  *libbar.so*) ;;
  *) echo "FAIL: libbar.so missing after remove: $after" >&2; exit 1 ;;
esac

echo "PASS: --remove-needed dropped libfoo.so, kept libbar.so"
