#!/bin/sh -e
# Smoke test: patchelf with NO mutating flag (only --print-os-abi)
# should leave the file byte-identical. This gates the parser/encoder
# pair independently of any mutating op.

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/00-parse-encode-identity"
mkdir -p "$SCRATCH"

# Build a minimally-structured ELF fixture with phdrs + shdrs + shstrtab
# + dynstr + dynamic so the parse+encode pipeline exercises all branches.
python3 - "$SCRATCH/input.elf" <<'PY'
import sys, struct
def u8(v): return bytes([v])
def u16(v): return struct.pack("<H", v)
def u32(v): return struct.pack("<I", v)
def u64(v): return struct.pack("<Q", v)

ident = b"\x7fELF" + u8(2) + u8(1) + u8(1) + u8(0) + (b"\x00" * 8)
# phnum=1 (PT_DYNAMIC), phoff=64, shoff=120, shnum=4 (null, shstr, dynstr, dynamic), shstrndx=1
hdr = ident + u16(2) + u16(62) + u32(1) + u64(0) + u64(64) + u64(120) \
    + u32(0) + u16(64) + u16(56) + u16(1) + u16(64) + u16(4) + u16(1)

pt_dynamic = u32(2) + u32(6) + u64(415) + u64(0) + u64(0) + u64(32) + u64(32) + u64(8)

null_shdr = b"\x00" * 64
# shstrtab at offset 376, size 28: "\x00.shstrtab\x00.dynstr\x00.dynamic\x00"
shstr_shdr = u32(1) + u32(3) + u64(0) + u64(0) + u64(376) + u64(28) \
           + u32(0) + u32(0) + u64(1) + u64(0)
# dynstr at offset 404, size 11: "\x00libc.so\x00\x00\x00"
dynstr_shdr = u32(11) + u32(3) + u64(0) + u64(0) + u64(404) + u64(11) \
            + u32(0) + u32(0) + u64(1) + u64(0)
# dynamic at offset 415, size 32: DT_NEEDED libc.so, DT_NULL
dynamic_shdr = u32(19) + u32(6) + u64(0) + u64(0) + u64(415) + u64(32) \
             + u32(2) + u32(0) + u64(8) + u64(16)

shstrtab = b"\x00.shstrtab\x00.dynstr\x00.dynamic\x00"
dynstr   = b"\x00libc.so\x00\x00\x00"
dynamic  = u64(1) + u64(1) + u64(0) + u64(0)  # DT_NEEDED=1, value=1, DT_NULL, value=0

with open(sys.argv[1], "wb") as f:
    f.write(hdr + pt_dynamic + null_shdr + shstr_shdr + dynstr_shdr + dynamic_shdr
            + shstrtab + dynstr + dynamic)
PY

cp "$SCRATCH/input.elf" "$SCRATCH/backup.elf"

# `roundtrip` is the dedicated parse+encode subcommand.  --output
# forces a write to a separate file (otherwise the CLI elides the
# write since the bytes match the input).
"$PATCHELF_BIN" roundtrip --output "$SCRATCH/output.elf" "$SCRATCH/input.elf" > /dev/null

# Input must be untouched.
if ! cmp -s "$SCRATCH/input.elf" "$SCRATCH/backup.elf"; then
  echo "FAIL: --output mutated the input file" >&2
  exit 1
fi

# Output should be byte-identical to input (parse + encode is no-op on
# already-well-laid-out inputs).
if ! cmp -s "$SCRATCH/input.elf" "$SCRATCH/output.elf"; then
  echo "FAIL: parse+encode produced different bytes" >&2
  echo "  input size : $(wc -c <"$SCRATCH/input.elf")" >&2
  echo "  output size: $(wc -c <"$SCRATCH/output.elf")" >&2
  exit 1
fi

echo "PASS: parse+encode is byte-identity on a well-laid-out fixture"
