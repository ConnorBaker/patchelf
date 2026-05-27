#!/bin/sh -e
# Multi-entry removeNeeded: a binary with three DT_NEEDED where two
# share a name (libfoo appearing twice).  After --remove-needed
# libfoo, only libbar should remain.  This verifies the final output
# is the filtered set, not the prefix — the adapter's positional
# mapping must correctly handle a smaller post-filter `needed` array
# than the input had DT_NEEDED entries.

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/45-cli-remove-needed-multi"
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
# dynstr = "\0libfoo.so\0libbar.so\0" — 21 bytes
dynstr_shdr = u32(11) + u32(3) + u64(0) + u64(0) + u64(404) + u64(21) \
            + u32(0) + u32(0) + u64(1) + u64(0)
# dynamic at 425, size 64 = 4 entries × 16
dynamic_shdr = u32(19) + u32(6) + u64(0) + u64(0) + u64(425) + u64(64) \
             + u32(2) + u32(0) + u64(8) + u64(16)

shstrtab = b"\x00.shstrtab\x00.dynstr\x00.dynamic\x00"
dynstr = b"\x00libfoo.so\x00libbar.so\x00"
# DT_NEEDED=1 (libfoo), DT_NEEDED=11 (libbar), DT_NEEDED=1 (libfoo), DT_NULL
dynamic = u64(1) + u64(1) + u64(1) + u64(11) + u64(1) + u64(1) + u64(0) + u64(0)

with open(sys.argv[1], "wb") as f:
    f.write(hdr + pt_load + null_shdr + shstr_shdr + dynstr_shdr + dynamic_shdr
            + shstrtab + dynstr + dynamic)
PY

# Remove libfoo.so (appears twice).
"$PATCHELF_BIN" remove-needed libfoo.so "$SCRATCH/input.elf"

# After removal: only libbar.so should remain.
actual=$("$PATCHELF_BIN" print-needed "$SCRATCH/input.elf")
expected='libbar.so'
if [ "$actual" != "$expected" ]; then
  echo "FAIL: expected '$expected', got '$actual'" >&2
  exit 1
fi

echo "PASS: --remove-needed drops all matching entries (even duplicates)"
