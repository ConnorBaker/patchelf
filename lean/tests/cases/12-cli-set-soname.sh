#!/bin/sh -e
# CLI: --set-soname rewrites the DT_SONAME value (appending the new
# name to .dynstr via the layout engine).

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/12-cli-set-soname"
mkdir -p "$SCRATCH"

# Fixture: named-sections + PT_LOAD header + DT_SONAME pointing at "libc.so".
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
dynstr_shdr = u32(11) + u32(3) + u64(0) + u64(0) + u64(404) + u64(11) \
            + u32(0) + u32(0) + u64(1) + u64(0)
dynamic_shdr = u32(19) + u32(6) + u64(0) + u64(0) + u64(415) + u64(32) \
             + u32(2) + u32(0) + u64(8) + u64(16)

shstrtab = b"\x00.shstrtab\x00.dynstr\x00.dynamic\x00"
dynstr   = b"\x00libc.so\x00\x00\x00"
# DT_SONAME(14) pointing at "libc.so" (offset 1), then DT_NULL.
dynamic = u64(14) + u64(1) + u64(0) + u64(0)

with open(sys.argv[1], "wb") as f:
    f.write(hdr + pt_load + null_shdr + shstr_shdr + dynstr_shdr + dynamic_shdr
            + shstrtab + dynstr + dynamic)
PY

original_size=$(wc -c <"$SCRATCH/input.elf" | tr -d ' ')

# Print the current soname.
before=$("$PATCHELF_BIN" print-soname "$SCRATCH/input.elf")
if [ "$before" != "libc.so" ]; then
  echo "FAIL (setup): pre-op soname was '$before', expected 'libc.so'" >&2
  exit 1
fi

# Set a new (longer) soname.
"$PATCHELF_BIN" set-soname libnewname.so "$SCRATCH/input.elf"

# File should have grown.
new_size=$(wc -c <"$SCRATCH/input.elf" | tr -d ' ')
if [ "$new_size" -le "$original_size" ]; then
  echo "FAIL: file didn't grow ($original_size → $new_size)" >&2
  exit 1
fi

# The new soname should be readable after the op.
after=$("$PATCHELF_BIN" print-soname "$SCRATCH/input.elf")
if [ "$after" != "libnewname.so" ]; then
  echo "FAIL: post-op soname was '$after', expected 'libnewname.so'" >&2
  exit 1
fi

echo "PASS: --set-soname grew dynstr + rewrote DT_SONAME's value"
