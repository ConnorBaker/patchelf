#!/bin/sh -e
# CLI: --add-rpath <path> prepends the existing rpath to <path> with
# ':' separator. When there's no existing rpath, it behaves as
# --set-rpath.

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/27-cli-add-rpath"
mkdir -p "$SCRATCH"

# Fixture with DT_RPATH pointing at "/existing".
python3 - "$SCRATCH/base.elf" <<'PY'
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
dynstr_shdr = u32(11) + u32(3) + u64(0) + u64(0) + u64(404) + u64(11) \
            + u32(0) + u32(0) + u64(1) + u64(0)
dynamic_shdr = u32(19) + u32(6) + u64(0) + u64(0) + u64(415) + u64(32) \
             + u32(2) + u32(0) + u64(8) + u64(16)
shstrtab = b"\x00.shstrtab\x00.dynstr\x00.dynamic\x00"
# "/existing" at offset 1 (9 chars + NUL + NUL = 11 bytes total).
dynstr   = b"\x00/existing\x00"
dynamic = u64(0x0f) + u64(1) + u64(0) + u64(0)
with open(sys.argv[1], "wb") as f:
    f.write(hdr + pt_load + null_shdr + shstr_shdr + dynstr_shdr + dynamic_shdr
            + shstrtab + dynstr + dynamic)
PY

# Sanity: initial rpath is "/existing".
initial=$("$PATCHELF_BIN" print-rpath "$SCRATCH/base.elf")
if [ "$initial" != "/existing" ]; then
  echo "FAIL: initial rpath = '$initial', expected /existing" >&2; exit 1
fi

# --add-rpath /new: expect "/existing:/new".
cp "$SCRATCH/base.elf" "$SCRATCH/appended.elf"
"$PATCHELF_BIN" add-rpath /new "$SCRATCH/appended.elf"
result=$("$PATCHELF_BIN" print-rpath "$SCRATCH/appended.elf")
if [ "$result" != "/existing:/new" ]; then
  echo "FAIL: --add-rpath result = '$result', expected /existing:/new" >&2; exit 1
fi

echo "PASS: --add-rpath prepends existing rpath with colon separator"
