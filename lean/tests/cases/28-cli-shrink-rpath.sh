#!/bin/sh -e
# CLI: --shrink-rpath --allowed-rpath-prefixes keeps only entries whose
# string starts with one of the allowed prefixes.

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/28-cli-shrink-rpath"
mkdir -p "$SCRATCH"

# Fixture: DT_RPATH pointing at "/a/b:/c/d:/e/f".
python3 - "$SCRATCH/base.elf" <<'PY'
import sys, struct
def u8(v): return bytes([v])
def u16(v): return struct.pack("<H", v)
def u32(v): return struct.pack("<I", v)
def u64(v): return struct.pack("<Q", v)

rpath_str = b"/a/b:/c/d:/e/f"   # 14 bytes
dynstr_bytes = b"\x00" + rpath_str + b"\x00"  # 16 bytes
dynstr_size = len(dynstr_bytes)

ident = b"\x7fELF" + u8(2) + u8(1) + u8(1) + u8(0) + (b"\x00" * 8)
phoff = 64
shoff = 120  # phoff + 56 phdr
hdr = ident + u16(2) + u16(62) + u32(1) + u64(0) + u64(phoff) + u64(shoff) \
    + u32(0) + u16(64) + u16(56) + u16(1) + u16(64) + u16(4) + u16(1)
pt_load = u32(1) + u32(5) + u64(0) + u64(0) + u64(0) + u64(64) + u64(64) + u64(4096)

shstrtab_off = 376  # shoff + 4*64
shstrtab = b"\x00.shstrtab\x00.dynstr\x00.dynamic\x00"
shstrtab_size = len(shstrtab)

dynstr_off = shstrtab_off + shstrtab_size   # 404
dynamic_off = dynstr_off + dynstr_size      # 420
dynamic = u64(0x0f) + u64(1) + u64(0) + u64(0)  # DT_RPATH -> offset 1 in dynstr
dynamic_size = len(dynamic)

null_shdr = b"\x00" * 64
shstr_shdr = u32(1) + u32(3) + u64(0) + u64(0) + u64(shstrtab_off) + u64(shstrtab_size) \
           + u32(0) + u32(0) + u64(1) + u64(0)
dynstr_shdr = u32(11) + u32(3) + u64(0) + u64(0) + u64(dynstr_off) + u64(dynstr_size) \
            + u32(0) + u32(0) + u64(1) + u64(0)
dynamic_shdr_bytes = u32(19) + u32(6) + u64(0) + u64(0) + u64(dynamic_off) + u64(dynamic_size) \
             + u32(2) + u32(0) + u64(8) + u64(16)

with open(sys.argv[1], "wb") as f:
    f.write(hdr + pt_load + null_shdr + shstr_shdr + dynstr_shdr + dynamic_shdr_bytes
            + shstrtab + dynstr_bytes + dynamic)
PY

initial=$("$PATCHELF_BIN" --print-rpath "$SCRATCH/base.elf")
if [ "$initial" != "/a/b:/c/d:/e/f" ]; then
  echo "FAIL: initial rpath = '$initial'" >&2; exit 1
fi

# Keep only entries starting with /c.
cp "$SCRATCH/base.elf" "$SCRATCH/shrunk.elf"
"$PATCHELF_BIN" --shrink-rpath --allowed-rpath-prefixes /c "$SCRATCH/shrunk.elf"
result=$("$PATCHELF_BIN" --print-rpath "$SCRATCH/shrunk.elf")
if [ "$result" != "/c/d" ]; then
  echo "FAIL: --shrink-rpath with /c prefix got '$result', expected /c/d" >&2; exit 1
fi

# Multi-prefix: keep entries starting with /a OR /e.
cp "$SCRATCH/base.elf" "$SCRATCH/multi.elf"
"$PATCHELF_BIN" --shrink-rpath --allowed-rpath-prefixes "/a:/e" "$SCRATCH/multi.elf"
result=$("$PATCHELF_BIN" --print-rpath "$SCRATCH/multi.elf")
if [ "$result" != "/a/b:/e/f" ]; then
  echo "FAIL: --shrink-rpath with /a:/e prefixes got '$result', expected /a/b:/e/f" >&2; exit 1
fi

echo "PASS: --shrink-rpath filters rpath by --allowed-rpath-prefixes"
