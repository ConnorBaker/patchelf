#!/bin/sh -e
# CLI: --replace-needed grows .dynstr when the new name isn't already
# present in the string table. DT_NEEDED value is rewritten to point at
# the appended new name; dynstr is relocated to end-of-file by the
# layout engine.

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/16-cli-replace-needed-grow"
mkdir -p "$SCRATCH"

# Fixture: ELF64 with .dynstr containing ONLY "libold.so" (no libbrand.so),
# and a DT_NEEDED pointing at libold.so. Renaming libold.so → libbrand.so
# must grow .dynstr (append libbrand.so) and rewrite the DT_NEEDED value.
#
# Layout:
#   bytes 0..64      : ELF header (phnum=1, phoff=64, shnum=4, shstrndx=1, shoff=120)
#   bytes 64..120    : phdr[0] = PT_LOAD (56 bytes)
#   bytes 120..376   : 4 shdrs × 64 bytes (null, shstrtab, dynstr, dynamic)
#   bytes 376..404   : shstrtab (28 bytes)
#   bytes 404..415   : dynstr (11 bytes: "\0libold.so\0")
#   bytes 415..447   : dynamic (32 bytes: DT_NEEDED(1)=libold + DT_NULL)
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
dynstr   = b"\x00libold.so\x00"
# DT_NEEDED(val=1, →"libold.so"), then DT_NULL.
dynamic = u64(1) + u64(1) + u64(0) + u64(0)

with open(sys.argv[1], "wb") as f:
    f.write(hdr + pt_load + null_shdr + shstr_shdr + dynstr_shdr + dynamic_shdr
            + shstrtab + dynstr + dynamic)
PY

original_size=$(wc -c <"$SCRATCH/input.elf" | tr -d ' ')

# Run: replace libold.so with libbrand.so (not in .dynstr → grows).
"$PATCHELF_BIN" replace-needed libold.so libbrand.so "$SCRATCH/input.elf"

# File should have grown (new name appended + relocated dynstr).
new_size=$(wc -c <"$SCRATCH/input.elf" | tr -d ' ')
if [ "$new_size" -le "$original_size" ]; then
  echo "FAIL: file didn't grow ($original_size -> $new_size)" >&2
  exit 1
fi

# Re-parse must succeed (validates clauses 1-7).
if ! "$PATCHELF_BIN" parse "$SCRATCH/input.elf" >"$SCRATCH/parse.out" 2>&1; then
  echo "FAIL: post-replace reparse failed" >&2
  cat "$SCRATCH/parse.out" >&2
  exit 1
fi

# The DT_NEEDED name should now resolve to libbrand.so via --print-needed.
needed=$("$PATCHELF_BIN" print-needed "$SCRATCH/input.elf")
if [ "$needed" != "libbrand.so" ]; then
  echo "FAIL: post-replace DT_NEEDED value resolved to '$needed', expected 'libbrand.so'" >&2
  exit 1
fi

echo "PASS: --replace-needed grew dynstr + rewrote DT_NEEDED to new name"
