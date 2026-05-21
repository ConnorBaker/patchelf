#!/bin/sh -e
# CLI: --add-debug-tag on an ELF that already has DT_DEBUG.
# Expected: no-op (exit 0), file unchanged.

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/08-cli-add-debug-tag-noop"
mkdir -p "$SCRATCH"

# Fixture with a dynamic section carrying DT_DEBUG (21=0x15).
# Layout: 4 shdrs (null, shstrtab, dynstr, dynamic); dynamic has 3 entries
# (DT_DEBUG, DT_NEEDED, DT_NULL = 3×16 = 48 bytes).
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
shstr_shdr = u32(1) + u32(3) + u64(0) + u64(0) + u64(320) + u64(28) \
           + u32(0) + u32(0) + u64(1) + u64(0)
dynstr_shdr = u32(11) + u32(3) + u64(0) + u64(0) + u64(348) + u64(11) \
            + u32(0) + u32(0) + u64(1) + u64(0)
dynamic_shdr = u32(19) + u32(6) + u64(0) + u64(0) + u64(359) + u64(48) \
             + u32(2) + u32(0) + u64(8) + u64(16)

shstrtab = b"\x00.shstrtab\x00.dynstr\x00.dynamic\x00"
dynstr   = b"\x00libc.so\x00\x00\x00"  # 11 bytes
# DT_DEBUG (21) val=0, DT_NEEDED val=1, DT_NULL.
dynamic = u64(21) + u64(0) + u64(1) + u64(1) + u64(0) + u64(0)

with open(sys.argv[1], "wb") as f:
    f.write(hdr + null_shdr + shstr_shdr + dynstr_shdr + dynamic_shdr
            + shstrtab + dynstr + dynamic)
PY

# Snapshot before.
cp "$SCRATCH/input.elf" "$SCRATCH/before.elf"

# Run CLI — should succeed (no-op).
"$PATCHELF_BIN" --add-debug-tag "$SCRATCH/input.elf"

# File should be byte-identical.
if ! cmp -s "$SCRATCH/input.elf" "$SCRATCH/before.elf"; then
  echo "FAIL: file changed after no-op --add-debug-tag" >&2
  diff <(od -An -tx1 "$SCRATCH/before.elf") <(od -An -tx1 "$SCRATCH/input.elf") | head -20 >&2
  exit 1
fi

echo "PASS: --add-debug-tag is a no-op when DT_DEBUG is already present"
