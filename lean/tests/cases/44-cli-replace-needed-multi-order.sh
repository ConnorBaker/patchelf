#!/bin/sh -e
# CLI: --replace-needed on a binary with multiple DT_NEEDED preserves
# positional order.  The adapter's `patchDynamicEntries` rewrites each
# DT_NEEDED in place rather than drop-and-reappend (which would swap
# order on rename).

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/44-cli-replace-needed-multi-order"
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
# dynstr = "\0libfoo.so\0libbar.so\0libbrand.so\0" — 33 bytes
dynstr_shdr = u32(11) + u32(3) + u64(0) + u64(0) + u64(404) + u64(33) \
            + u32(0) + u32(0) + u64(1) + u64(0)
# dynamic at 437, size 48
dynamic_shdr = u32(19) + u32(6) + u64(0) + u64(0) + u64(437) + u64(48) \
             + u32(2) + u32(0) + u64(8) + u64(16)

shstrtab = b"\x00.shstrtab\x00.dynstr\x00.dynamic\x00"
dynstr = b"\x00libfoo.so\x00libbar.so\x00libbrand.so\x00"
# DT_NEEDED=1 (libfoo), DT_NEEDED=11 (libbar), DT_NULL
dynamic = u64(1) + u64(1) + u64(1) + u64(11) + u64(0) + u64(0)

with open(sys.argv[1], "wb") as f:
    f.write(hdr + pt_load + null_shdr + shstr_shdr + dynstr_shdr + dynamic_shdr
            + shstrtab + dynstr + dynamic)
PY

# Replace libfoo.so → libbrand.so (reuse path).
"$PATCHELF_BIN" --replace-needed libfoo.so libbrand.so "$SCRATCH/input.elf"

# --print-needed emits entries in .dynamic order.  Expect libbrand first,
# libbar second (since libfoo was at position 1 and got renamed).
actual=$("$PATCHELF_BIN" --print-needed "$SCRATCH/input.elf")
expected='libbrand.so
libbar.so'
if [ "$actual" != "$expected" ]; then
  echo "FAIL: expected '$expected', got '$actual'" >&2
  exit 1
fi

echo "PASS: --replace-needed preserves positional order across multi-entry .dynamic"
