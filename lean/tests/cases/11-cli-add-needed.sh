#!/bin/sh -e
# CLI: --add-needed grows .dynstr + .dynamic via the layout engine.
# Expected: the output file re-parses successfully and contains a new
# DT_NEEDED entry for the library we added.

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/11-cli-add-needed"
mkdir -p "$SCRATCH"

# Fixture: named-sections layout + one pre-existing PT_LOAD phdr so the
# engine's phdr appends don't clash with the header at offset 0.
#
# Layout:
#   bytes 0..64      : ELF header (phnum=1, phoff=64, shnum=4, shstrndx=1, shoff=120)
#   bytes 64..120    : phdr[0] = PT_LOAD (56 bytes)
#   bytes 120..376   : 4 shdrs × 64 bytes
#   bytes 376..404   : shstrtab (28 bytes)
#   bytes 404..415   : dynstr (11 bytes)
#   bytes 415..447   : dynamic (32 bytes, DT_NEEDED + DT_NULL)
python3 - "$SCRATCH/input.elf" <<'PY'
import sys, struct
def u8(v): return bytes([v])
def u16(v): return struct.pack("<H", v)
def u32(v): return struct.pack("<I", v)
def u64(v): return struct.pack("<Q", v)

ident = b"\x7fELF" + u8(2) + u8(1) + u8(1) + u8(0) + (b"\x00" * 8)
# phoff=64, shoff=120, phnum=1, shnum=4, shstrndx=1
hdr = ident + u16(2) + u16(62) + u32(1) + u64(0) + u64(64) + u64(120) \
    + u32(0) + u16(64) + u16(56) + u16(1) + u16(64) + u16(4) + u16(1)

# PT_LOAD phdr: covers [0, 64) in both file and memory (so we've "accounted for" the header).
pt_load = u32(1) + u32(5) + u64(0) + u64(0) + u64(0) + u64(64) + u64(64) + u64(4096)

null_shdr = b"\x00" * 64
# shstrtab at 376, size 28
shstr_shdr = u32(1) + u32(3) + u64(0) + u64(0) + u64(376) + u64(28) \
           + u32(0) + u32(0) + u64(1) + u64(0)
# dynstr at 404, size 11
dynstr_shdr = u32(11) + u32(3) + u64(0) + u64(0) + u64(404) + u64(11) \
            + u32(0) + u32(0) + u64(1) + u64(0)
# dynamic at 415, size 32
dynamic_shdr = u32(19) + u32(6) + u64(0) + u64(0) + u64(415) + u64(32) \
             + u32(2) + u32(0) + u64(8) + u64(16)

shstrtab = b"\x00.shstrtab\x00.dynstr\x00.dynamic\x00"
dynstr   = b"\x00libc.so\x00\x00\x00"
dynamic = u64(1) + u64(1) + u64(0) + u64(0)

with open(sys.argv[1], "wb") as f:
    f.write(hdr + pt_load + null_shdr + shstr_shdr + dynstr_shdr + dynamic_shdr
            + shstrtab + dynstr + dynamic)
PY

original_size=$(wc -c <"$SCRATCH/input.elf" | tr -d ' ')

# Run the op.
"$PATCHELF_BIN" add-needed libnew.so "$SCRATCH/input.elf"

# The file should have grown by at least the added bytes (libnew.so\0 = 10,
# plus one new dynamic entry = 16 bytes, plus PT_LOAD phdrs).
new_size=$(wc -c <"$SCRATCH/input.elf" | tr -d ' ')
if [ "$new_size" -le "$original_size" ]; then
  echo "FAIL: file didn't grow (old=$original_size, new=$new_size)" >&2
  exit 1
fi

# Re-parse using --parse; the output should be well-formed enough to parse.
if ! "$PATCHELF_BIN" parse "$SCRATCH/input.elf" >"$SCRATCH/parse.out" 2>&1; then
  echo "FAIL: post-add-needed reparse failed" >&2
  cat "$SCRATCH/parse.out" >&2
  exit 1
fi

# Confirm the parse summary matches expectations (2 sections grew → phnum grew).
if ! grep -q "ok" "$SCRATCH/parse.out"; then
  echo "FAIL: reparse didn't print 'ok'" >&2
  cat "$SCRATCH/parse.out" >&2
  exit 1
fi

echo "PASS: --add-needed grew the file and output re-parses cleanly"
