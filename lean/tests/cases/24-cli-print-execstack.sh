#!/bin/sh -e
# CLI: --print-execstack reports 'X', '-', or '?' depending on PT_GNU_STACK.
# The minimal fixture has no PT_GNU_STACK, so '?' is expected.
# Then we --set-execstack and check for 'X'. Then --clear-execstack
# would need PT_GNU_STACK to actually exist, so after set we test clear.

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/24-cli-print-execstack"
mkdir -p "$SCRATCH"

# Build a fixture with a PT_GNU_STACK phdr (flags=PF_R|PF_W, no PF_X).
python3 - "$SCRATCH/input.elf" <<'PY'
import sys, struct
def u8(v): return bytes([v])
def u16(v): return struct.pack("<H", v)
def u32(v): return struct.pack("<I", v)
def u64(v): return struct.pack("<Q", v)
ident = b"\x7fELF" + u8(2) + u8(1) + u8(1) + u8(0) + (b"\x00" * 8)
# phnum=1 (PT_GNU_STACK), phoff=64, shoff=120, shnum=2
hdr = ident + u16(2) + u16(62) + u32(1) + u64(0) + u64(64) + u64(120) \
    + u32(0) + u16(64) + u16(56) + u16(1) + u16(64) + u16(2) + u16(1)
# PT_GNU_STACK = 0x6474e551; flags = PF_R|PF_W = 6; offset 0; vaddr 0; paddr 0; filesz 0; memsz 0; align 0x1.
pt_gnu_stack = u32(0x6474e551) + u32(6) + u64(0) + u64(0) + u64(0) + u64(0) + u64(0) + u64(1)
null_shdr = b"\x00" * 64
shstr_shdr = u32(0) + u32(3) + u64(0) + u64(0) + u64(248) + u64(1) \
           + u32(0) + u32(0) + u64(1) + u64(0)
shstr = b"\x00"
with open(sys.argv[1], "wb") as f:
    f.write(hdr + pt_gnu_stack + null_shdr + shstr_shdr + shstr)
PY

# Initially: PF_X is not set, so --print-execstack should print "-".
out=$("$PATCHELF_BIN" print-execstack "$SCRATCH/input.elf")
case "$out" in
  *"execstack: -"*) ;;
  *) echo "FAIL: initial print-execstack got: $out (expected '-')" >&2; exit 1 ;;
esac

# Set PF_X, then print-execstack should be 'X'.
"$PATCHELF_BIN" set-execstack "$SCRATCH/input.elf"
out=$("$PATCHELF_BIN" print-execstack "$SCRATCH/input.elf")
case "$out" in
  *"execstack: X"*) ;;
  *) echo "FAIL: post-set print-execstack got: $out (expected 'X')" >&2; exit 1 ;;
esac

# Clear PF_X, then print-execstack should be '-' again.
"$PATCHELF_BIN" clear-execstack "$SCRATCH/input.elf"
out=$("$PATCHELF_BIN" print-execstack "$SCRATCH/input.elf")
case "$out" in
  *"execstack: -"*) ;;
  *) echo "FAIL: post-clear print-execstack got: $out (expected '-')" >&2; exit 1 ;;
esac

echo "PASS: --print-execstack reports X/- after set/clear"
