#!/bin/sh -e
# End-to-end CLI test: write a synthetic ELF fixture, run patchelf
# via the CLI with --set-os-abi, re-read the file and verify byte 7
# (EI_OSABI) is now 3 (Linux).
#
# This exercises the full pipeline: disk I/O → parse → op → encode →
# disk I/O, via actual argv entry.

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/02-cli-set-os-abi"
mkdir -p "$SCRATCH"

# Ask patchelf to dump its internal minimal fixture to disk via
# a small Lean helper.  We lean on the --smoke's embedded fixture by
# using Python to build the same bytes that `minimalValidElf` produces.
python3 - "$SCRATCH/input.elf" <<'PY'
import sys, struct
def u8(v): return bytes([v])
def u16(v): return struct.pack("<H", v)
def u32(v): return struct.pack("<I", v)
def u64(v): return struct.pack("<Q", v)

# e_ident: magic + class=64 + data=LSB + version=1 + osabi=0 + pad
ident = b"\x7fELF" + u8(2) + u8(1) + u8(1) + u8(0) + (b"\x00" * 8)
# Header (64 bytes).
hdr = ident + u16(2) + u16(62) + u32(1) + u64(0) + u64(0) + u64(64) \
    + u32(0) + u16(64) + u16(56) + u16(0) + u16(64) + u16(2) + u16(1)
# shdr[0] = SHT_NULL.
null_shdr = b"\x00" * 64
# shdr[1] = SHT_STRTAB for shstrtab; offset 192, size 1.
shstr_shdr = u32(0) + u32(3) + u64(0) + u64(0) + u64(192) + u64(1) \
           + u32(0) + u32(0) + u64(1) + u64(0)
# shstrtab contents.
shstr = b"\x00"

out = hdr + null_shdr + shstr_shdr + shstr
with open(sys.argv[1], "wb") as f:
    f.write(out)
PY

# Sanity: byte 7 should be 0 (SysV) before mutation.
before=$(od -An -tx1 -N1 -j7 "$SCRATCH/input.elf" | tr -d ' \n')
if [ "$before" != "00" ]; then
  echo "pre-mutation byte 7 = $before, expected 00" >&2
  exit 1
fi

# Run the CLI.
"$PATCHELF_BIN" --set-os-abi Linux "$SCRATCH/input.elf"

# Byte 7 should now be 3 (Linux).
after=$(od -An -tx1 -N1 -j7 "$SCRATCH/input.elf" | tr -d ' \n')
if [ "$after" != "03" ]; then
  echo "post-mutation byte 7 = $after, expected 03" >&2
  exit 1
fi

# Everything else should be unchanged. Diff to a pristine copy.
python3 - "$SCRATCH/input.elf" "$SCRATCH/pristine.elf" <<'PY'
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
out = hdr + null_shdr + shstr_shdr + shstr
with open(sys.argv[2], "wb") as f:
    f.write(out)
PY

# Compare all bytes except byte 7.
python3 - "$SCRATCH/input.elf" "$SCRATCH/pristine.elf" <<'PY'
import sys
a = open(sys.argv[1], "rb").read()
b = open(sys.argv[2], "rb").read()
if len(a) != len(b):
    print(f"size differs: {len(a)} vs {len(b)}", file=sys.stderr)
    sys.exit(1)
for i in range(len(a)):
    if i == 7:
        continue
    if a[i] != b[i]:
        print(f"byte {i} differs: input={a[i]:02x} pristine={b[i]:02x}", file=sys.stderr)
        sys.exit(1)
print("all bytes match except byte 7 (as expected)")
PY

echo "PASS: patchelf --set-os-abi Linux mutated only byte 7"
