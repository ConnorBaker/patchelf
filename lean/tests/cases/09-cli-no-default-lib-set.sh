#!/bin/sh -e
# CLI: --no-default-lib on an ELF that has DT_FLAGS_1.
# Expected: DF_1_NODEFLIB (0x00000800) bit gets OR'd into the value.

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/09-cli-no-default-lib-set"
mkdir -p "$SCRATCH"

# Fixture with a dynamic section carrying DT_FLAGS_1 (0x6ffffffb) with value=0.
# Dynamic has 3 entries: DT_FLAGS_1, DT_NEEDED, DT_NULL = 48 bytes.
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
dynstr   = b"\x00libc.so\x00\x00\x00"
# DT_FLAGS_1 val=0, DT_NEEDED val=1, DT_NULL.
dynamic = u64(0x6ffffffb) + u64(0) + u64(1) + u64(1) + u64(0) + u64(0)

with open(sys.argv[1], "wb") as f:
    f.write(hdr + null_shdr + shstr_shdr + dynstr_shdr + dynamic_shdr
            + shstrtab + dynstr + dynamic)
PY

# Run CLI — should succeed.
"$PATCHELF_BIN" --no-default-lib "$SCRATCH/input.elf"

# The DT_FLAGS_1 value (bytes [367..375) = offset 359 + 8 = 367) should now be 0x800.
val=$(od -An -tx1 -N8 -j367 "$SCRATCH/input.elf" | tr -d ' \n')
# Expected: 00 08 00 00 00 00 00 00 (little-endian 0x800).
if [ "$val" != "0008000000000000" ]; then
  echo "FAIL: DT_FLAGS_1 value = $val, expected 0008000000000000 (0x800)" >&2
  exit 1
fi

echo "PASS: --no-default-lib OR'd DF_1_NODEFLIB into DT_FLAGS_1"
