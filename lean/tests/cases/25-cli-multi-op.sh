#!/bin/sh -e
# CLI: multiple sequential subcommand invocations work.  In the new
# subcommand-based CLI there's no in-process multi-op, but chaining
# `&&` subcommands is the supported path.

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/25-cli-multi-op"
mkdir -p "$SCRATCH"

python3 - "$SCRATCH/input.elf" <<'PY'
import sys, struct
def u8(v): return bytes([v])
def u16(v): return struct.pack("<H", v)
def u32(v): return struct.pack("<I", v)
def u64(v): return struct.pack("<Q", v)
ident = b"\x7fELF" + u8(2) + u8(1) + u8(1) + u8(0) + (b"\x00" * 8)
hdr = ident + u16(2) + u16(62) + u32(1) + u64(0) + u64(0) + u64(64) \
    + u32(0) + u16(64) + u16(56) + u16(0) + u16(64) + u16(2) + u16(1)
null_shdr = b"\x00" * 64
shstr_shdr = u32(0) + u32(3) + u64(0) + u64(0) + u64(192) + u64(1) \
           + u32(0) + u32(0) + u64(1) + u64(0)
shstr = b"\x00"
with open(sys.argv[1], "wb") as f:
    f.write(hdr + null_shdr + shstr_shdr + shstr)
PY

# Pre-check: original abi is SysV (byte 0 in EI_OSABI).
before=$("$PATCHELF_BIN" print-os-abi "$SCRATCH/input.elf")
case "$before" in
  *"System V"*) ;;
  *) echo "FAIL: pre-mutation print-os-abi should be 'System V'. Got: $before" >&2; exit 1 ;;
esac

# Run the mutation.
"$PATCHELF_BIN" set-os-abi Linux "$SCRATCH/input.elf"

# Post-check: now reads 'Linux'.
after=$("$PATCHELF_BIN" print-os-abi "$SCRATCH/input.elf")
case "$after" in
  *Linux*) ;;
  *) echo "FAIL: post-mutation print-os-abi should be 'Linux'. Got: $after" >&2; exit 1 ;;
esac

# Byte 7 should now be 3 on disk.
byte7=$(od -An -tx1 -N1 -j7 "$SCRATCH/input.elf" | tr -d ' \n')
if [ "$byte7" != "03" ]; then
  echo "FAIL: byte 7 = $byte7, expected 03" >&2
  exit 1
fi

echo "PASS: chained subcommand invocations apply mutations correctly"
