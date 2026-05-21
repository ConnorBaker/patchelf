#!/bin/sh -e
# Edge case: --add-needed on a .dynamic with NO existing DT_NEEDED
# entries (only DT_NULL).  The adapter's `patchDynamicEntries` must
# correctly append the new DT_NEEDED when there's nothing to map
# positionally over.

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/47-cli-add-needed-empty-dynamic"
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
# Empty-ish dynstr: "\0" (1 byte; just the first null).
dynstr_shdr = u32(11) + u32(3) + u64(0) + u64(0) + u64(404) + u64(1) \
            + u32(0) + u32(0) + u64(1) + u64(0)
# dynamic at 405, size 16 = DT_NULL only
dynamic_shdr = u32(19) + u32(6) + u64(0) + u64(0) + u64(405) + u64(16) \
             + u32(2) + u32(0) + u64(8) + u64(16)

shstrtab = b"\x00.shstrtab\x00.dynstr\x00.dynamic\x00"
dynstr = b"\x00"
dynamic = u64(0) + u64(0)   # DT_NULL

with open(sys.argv[1], "wb") as f:
    f.write(hdr + pt_load + null_shdr + shstr_shdr + dynstr_shdr + dynamic_shdr
            + shstrtab + dynstr + dynamic)
PY

# Sanity: before should have no needed entries.
before=$("$PATCHELF_BIN" --print-needed "$SCRATCH/input.elf")
if [ -n "$before" ]; then
  echo "FAIL (setup): expected no needed entries, got '$before'" >&2
  exit 1
fi

"$PATCHELF_BIN" --add-needed libnew.so "$SCRATCH/input.elf"

after=$("$PATCHELF_BIN" --print-needed "$SCRATCH/input.elf")
expected='libnew.so'
if [ "$after" != "$expected" ]; then
  echo "FAIL: expected '$expected', got '$after'" >&2
  exit 1
fi

echo "PASS: --add-needed appends to an empty .dynamic"
