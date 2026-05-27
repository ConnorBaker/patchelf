#!/bin/sh -e
# CLI: --no-default-lib grows `.dynamic` via the layout engine when
# DT_FLAGS_1 is absent. Expected: the output file re-parses and has
# grown beyond its original size.

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/18-cli-no-default-lib-insert"
mkdir -p "$SCRATCH"

# Fixture: named-sections layout + one pre-existing PT_LOAD phdr so the
# engine's phdr append doesn't clash with the ELF header at offset 0.
# Dynamic has DT_NEEDED + DT_NULL; no DT_FLAGS_1.
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
# DT_NEEDED val=1, DT_NULL. No DT_FLAGS_1.
dynamic = u64(1) + u64(1) + u64(0) + u64(0)

with open(sys.argv[1], "wb") as f:
    f.write(hdr + pt_load + null_shdr + shstr_shdr + dynstr_shdr + dynamic_shdr
            + shstrtab + dynstr + dynamic)
PY

original_size=$(wc -c <"$SCRATCH/input.elf" | tr -d ' ')

# Run the op.
"$PATCHELF_BIN" no-default-lib "$SCRATCH/input.elf"

# File should have grown (one new DT_FLAGS_1 entry of 16 bytes + engine overhead).
new_size=$(wc -c <"$SCRATCH/input.elf" | tr -d ' ')
if [ "$new_size" -le "$original_size" ]; then
  echo "FAIL: file didn't grow (old=$original_size, new=$new_size)" >&2
  exit 1
fi

# Re-parse to verify the result is well-formed.
if ! "$PATCHELF_BIN" parse "$SCRATCH/input.elf" >"$SCRATCH/parse.out" 2>&1; then
  echo "FAIL: post-no-default-lib reparse failed" >&2
  cat "$SCRATCH/parse.out" >&2
  exit 1
fi

if ! grep -q "ok" "$SCRATCH/parse.out"; then
  echo "FAIL: reparse didn't print 'ok'" >&2
  cat "$SCRATCH/parse.out" >&2
  exit 1
fi

echo "PASS: --no-default-lib grew .dynamic via layout engine and output re-parses cleanly"
