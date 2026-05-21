#!/bin/sh -e
# CLI: --page-size <N> overrides the default alignment. Running a
# growing op with a larger page size should produce a larger aligned
# end-of-file region.
#
# We compare two runs of --add-debug-tag on identical inputs, one with
# default page size (4096) and one with 8192. The 8192 run should
# produce output whose size is >= the 4096 run's size (alignment is
# non-strict: 4096 might round to the same multiple for small payloads,
# but 8192 forces a larger boundary if anything spills).

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/23-cli-page-size"
mkdir -p "$SCRATCH"

# Reuse the add-debug-tag-insert fixture (has .dynamic without DT_DEBUG).
python3 - "$SCRATCH/base.elf" <<'PY'
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
dynamic = u64(1) + u64(1) + u64(0) + u64(0)
with open(sys.argv[1], "wb") as f:
    f.write(hdr + pt_load + null_shdr + shstr_shdr + dynstr_shdr + dynamic_shdr
            + shstrtab + dynstr + dynamic)
PY

# Two copies, different page sizes.
cp "$SCRATCH/base.elf" "$SCRATCH/p4096.elf"
cp "$SCRATCH/base.elf" "$SCRATCH/p8192.elf"

"$PATCHELF_BIN" --add-debug-tag "$SCRATCH/p4096.elf"
"$PATCHELF_BIN" --page-size 8192 --add-debug-tag "$SCRATCH/p8192.elf"

s4096=$(wc -c <"$SCRATCH/p4096.elf" | tr -d ' ')
s8192=$(wc -c <"$SCRATCH/p8192.elf" | tr -d ' ')

if [ "$s8192" -lt "$s4096" ]; then
  echo "FAIL: 8192-aligned output smaller than 4096 (p4096=$s4096 p8192=$s8192)" >&2
  exit 1
fi

# Both must re-parse cleanly.
for f in "$SCRATCH/p4096.elf" "$SCRATCH/p8192.elf"; do
  if ! "$PATCHELF_BIN" --parse "$f" >/dev/null 2>&1; then
    echo "FAIL: $f did not re-parse" >&2
    exit 1
  fi
done

# Rejection: --page-size 0 should error (exit code 1).
if "$PATCHELF_BIN" --page-size 0 --print-os-abi "$SCRATCH/base.elf" >/dev/null 2>&1; then
  echo "FAIL: --page-size 0 was accepted" >&2
  exit 1
fi

echo "PASS: --page-size 4096 and 8192 both produce valid ELFs; 0 rejected"
