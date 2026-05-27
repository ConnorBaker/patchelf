#!/bin/sh -e
# CLI: --add-rpath on a binary without an existing rpath entry should
# INSERT a new DT_RUNPATH (C++ patchelf behavior: appendRPath on empty
# old-rpath is equivalent to setRpath). Covers the addRpath branch of
# the CLI insertion dispatch.

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/39-cli-add-rpath-no-entry-inserts"
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
dynstr_shdr = u32(11) + u32(3) + u64(0) + u64(0) + u64(404) + u64(1) \
            + u32(0) + u32(0) + u64(1) + u64(0)
dynamic_shdr = u32(19) + u32(6) + u64(0) + u64(0) + u64(405) + u64(16) \
             + u32(2) + u32(0) + u64(8) + u64(16)

shstrtab = b"\x00.shstrtab\x00.dynstr\x00.dynamic\x00"
dynstr   = b"\x00"
dynamic = u64(0) + u64(0)

with open(sys.argv[1], "wb") as f:
    f.write(hdr + pt_load + null_shdr + shstr_shdr + dynstr_shdr + dynamic_shdr
            + shstrtab + dynstr + dynamic)
PY

"$PATCHELF_BIN" add-rpath /app/lib "$SCRATCH/input.elf"

got=$("$PATCHELF_BIN" print-rpath "$SCRATCH/input.elf")
if [ "$got" != "/app/lib" ]; then
  echo "FAIL: --print-rpath returned '$got', expected '/app/lib'" >&2
  exit 1
fi

echo "PASS: --add-rpath on fresh binary inserted new rpath entry (no existing rpath to compose with)"
