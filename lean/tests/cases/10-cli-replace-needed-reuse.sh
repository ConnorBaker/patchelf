#!/bin/sh -e
# CLI: --replace-needed works in-place when the new name is already in .dynstr.
# Expected: DT_NEEDED entry's value updated to the existing-name offset;
# file size unchanged; re-parse succeeds.

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/10-cli-replace-needed-reuse"
mkdir -p "$SCRATCH"

# Fixture: ELF64 with .dynstr containing both "libold.so\0" and "libnew.so\0",
# and .dynamic with a DT_NEEDED pointing at libold.so. The rename from
# libold.so → libnew.so can reuse the existing libnew.so offset.
#
# Layout:
#   bytes 0..64      : ELF header (shnum=4, shstrndx=1)
#   bytes 64..320    : 4 shdrs × 64 bytes
#   bytes 320..348   : shstrtab (28 bytes)
#   bytes 348..369   : dynstr (21 bytes: "\0libold.so\0libnew.so\0")
#   bytes 369..401   : dynamic (32 bytes: DT_NEEDED(1)=libold + DT_NULL)
python3 - "$SCRATCH/input.elf" <<'PY'
import sys, struct
def u8(v): return bytes([v])
def u16(v): return struct.pack("<H", v)
def u32(v): return struct.pack("<I", v)
def u64(v): return struct.pack("<Q", v)

ident = b"\x7fELF" + u8(2) + u8(1) + u8(1) + u8(0) + (b"\x00" * 8)
hdr = ident + u16(2) + u16(62) + u32(1) + u64(0) + u64(0) + u64(64) \
    + u32(0) + u16(64) + u16(56) + u16(0) + u16(64) + u16(4) + u16(1)

null_shdr = b"\x00" * 64
# shstrtab at offset 320, size 28
shstr_shdr = u32(1) + u32(3) + u64(0) + u64(0) + u64(320) + u64(28) \
           + u32(0) + u32(0) + u64(1) + u64(0)
# dynstr at offset 348, size 21
dynstr_shdr = u32(11) + u32(3) + u64(0) + u64(0) + u64(348) + u64(21) \
            + u32(0) + u32(0) + u64(1) + u64(0)
# dynamic at offset 369, size 32
dynamic_shdr = u32(19) + u32(6) + u64(0) + u64(0) + u64(369) + u64(32) \
             + u32(2) + u32(0) + u64(8) + u64(16)

shstrtab = b"\x00.shstrtab\x00.dynstr\x00.dynamic\x00"
dynstr   = b"\x00libold.so\x00libnew.so\x00"  # offsets: "libold.so"=1, "libnew.so"=11
# DT_NEEDED(val=1, i.e. libold.so), then DT_NULL.
dynamic = u64(1) + u64(1) + u64(0) + u64(0)

with open(sys.argv[1], "wb") as f:
    f.write(hdr + null_shdr + shstr_shdr + dynstr_shdr + dynamic_shdr
            + shstrtab + dynstr + dynamic)
PY

# Snapshot before.
original_size=$(wc -c <"$SCRATCH/input.elf" | tr -d ' ')
cp "$SCRATCH/input.elf" "$SCRATCH/before.elf"

# Run CLI — should succeed.
"$PATCHELF_BIN" --replace-needed libold.so libnew.so "$SCRATCH/input.elf"

# File size unchanged.
new_size=$(wc -c <"$SCRATCH/input.elf" | tr -d ' ')
if [ "$new_size" != "$original_size" ]; then
  echo "FAIL: file size changed from $original_size to $new_size" >&2
  exit 1
fi

# The DT_NEEDED value at file offset 369+8=377 should now be 11 (libnew.so offset).
# Bytes [377..385) should be 0b 00 00 00 00 00 00 00 (little-endian 11).
val=$(od -An -tx1 -N8 -j377 "$SCRATCH/input.elf" | tr -d ' \n')
if [ "$val" != "0b00000000000000" ]; then
  echo "FAIL: DT_NEEDED value = $val, expected 0b00000000000000 (offset 11)" >&2
  exit 1
fi

echo "PASS: --replace-needed reuses existing .dynstr offset (libnew.so already present)"
