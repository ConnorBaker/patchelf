#!/bin/sh -e
# Edge case: --remove-needed for a library not present in .dynamic
# is a no-op and MUST be byte-identical.  This exercises the
# adapter's `patchDynamicEntries` when the typed-side `needed` array
# is identical to the byte-layer's input (no entries removed).

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/48-cli-remove-needed-no-match-noop"
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
dynstr_shdr = u32(11) + u32(3) + u64(0) + u64(0) + u64(404) + u64(11) \
            + u32(0) + u32(0) + u64(1) + u64(0)
dynamic_shdr = u32(19) + u32(6) + u64(0) + u64(0) + u64(415) + u64(32) \
             + u32(2) + u32(0) + u64(8) + u64(16)

shstrtab = b"\x00.shstrtab\x00.dynstr\x00.dynamic\x00"
dynstr   = b"\x00libfoo.so\x00"
dynamic  = u64(1) + u64(1) + u64(0) + u64(0)

with open(sys.argv[1], "wb") as f:
    f.write(hdr + pt_load + null_shdr + shstr_shdr + dynstr_shdr + dynamic_shdr
            + shstrtab + dynstr + dynamic)
PY

cp "$SCRATCH/input.elf" "$SCRATCH/before.elf"
"$PATCHELF_BIN" --remove-needed libnotpresent.so "$SCRATCH/input.elf"

if ! cmp -s "$SCRATCH/input.elf" "$SCRATCH/before.elf"; then
  echo "FAIL: no-op --remove-needed changed bytes" >&2
  diff <(od -An -tx1 "$SCRATCH/before.elf") <(od -An -tx1 "$SCRATCH/input.elf") | head -10 >&2
  exit 1
fi

echo "PASS: --remove-needed with no match preserves bytes"
