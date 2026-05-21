#!/bin/sh -e
# CLI: --rename-dynamic-symbols <map-file> applies many renames in one
# invocation. Each non-blank line of the map file is parsed as
# '<old> <new>' (whitespace-split). Blank lines and lines that don't
# yield exactly two tokens are skipped.

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/15-cli-rename-dynamic-symbols-mapfile"
mkdir -p "$SCRATCH"

# Fixture: ELF64 with .dynstr "\0foo\0bar\0" and a 2-entry .dynsym
# where entry 1 has st_name = 1 (→"foo") and entry 2 has st_name = 5
# (→"bar"). A map file renames foo->fooX and bar->barY; after the op
# both renames should be visible via .dynstr / .dynsym.
python3 - "$SCRATCH/input.elf" <<'PY'
import sys, struct
def u8(v): return bytes([v])
def u16(v): return struct.pack("<H", v)
def u32(v): return struct.pack("<I", v)
def u64(v): return struct.pack("<Q", v)

ident = b"\x7fELF" + u8(2) + u8(1) + u8(1) + u8(0) + (b"\x00" * 8)
# phnum=1, phoff=64, shnum=4, shstrndx=1, shoff=120
hdr = ident + u16(2) + u16(62) + u32(1) + u64(0) + u64(64) + u64(120) \
    + u32(0) + u16(64) + u16(56) + u16(1) + u16(64) + u16(4) + u16(1)

pt_load = u32(1) + u32(5) + u64(0) + u64(0) + u64(0) + u64(64) + u64(64) + u64(4096)

null_shdr = b"\x00" * 64
# shstrtab at 376, size 27 ("\0.shstrtab\0.dynstr\0.dynsym\0")
shstr_shdr = u32(1) + u32(3) + u64(0) + u64(0) + u64(376) + u64(27) \
           + u32(0) + u32(0) + u64(1) + u64(0)
# dynstr at 403, size 9 ("\0foo\0bar\0")
dynstr_shdr = u32(11) + u32(3) + u64(0) + u64(0) + u64(403) + u64(9) \
            + u32(0) + u32(0) + u64(1) + u64(0)
# dynsym at 412, size 72 (3 entries × 24 bytes), sh_link = 2 (dynstr), entsize = 24
dynsym_shdr = u32(19) + u32(11) + u64(0) + u64(0) + u64(412) + u64(72) \
            + u32(2) + u32(0) + u64(8) + u64(24)

shstrtab = b"\x00.shstrtab\x00.dynstr\x00.dynsym\x00"
dynstr   = b"\x00foo\x00bar\x00"
# Three Elf64_Sym entries (24 bytes each):
#   entry 0: st_name=0 (null)
#   entry 1: st_name=1 (foo)
#   entry 2: st_name=5 (bar)
sym0 = u32(0) + u8(0) + u8(0) + u16(0) + u64(0) + u64(0)
sym1 = u32(1) + u8(0) + u8(0) + u16(0) + u64(0) + u64(0)
sym2 = u32(5) + u8(0) + u8(0) + u16(0) + u64(0) + u64(0)
dynsym = sym0 + sym1 + sym2

with open(sys.argv[1], "wb") as f:
    f.write(hdr + pt_load + null_shdr + shstr_shdr + dynstr_shdr + dynsym_shdr
            + shstrtab + dynstr + dynsym)
PY

# Map file with a blank line and a malformed line (should be skipped).
cat > "$SCRATCH/rename.map" <<'MAP'
foo fooX

malformed-line-no-pair
bar barY
MAP

original_size=$(wc -c <"$SCRATCH/input.elf" | tr -d ' ')

"$PATCHELF_BIN" --rename-dynamic-symbols "$SCRATCH/rename.map" "$SCRATCH/input.elf"

new_size=$(wc -c <"$SCRATCH/input.elf" | tr -d ' ')
if [ "$new_size" -le "$original_size" ]; then
  echo "FAIL: file didn't grow ($original_size -> $new_size)" >&2
  exit 1
fi

# Re-parse to confirm the output is well-formed.
if ! "$PATCHELF_BIN" --parse "$SCRATCH/input.elf" >"$SCRATCH/parse.out" 2>&1; then
  echo "FAIL: post-rename reparse failed" >&2
  cat "$SCRATCH/parse.out" >&2
  exit 1
fi

# Both new names should be present in the binary (substring check via grep -a).
if ! grep -a -q "fooX" "$SCRATCH/input.elf"; then
  echo "FAIL: 'fooX' not found in output" >&2
  exit 1
fi
if ! grep -a -q "barY" "$SCRATCH/input.elf"; then
  echo "FAIL: 'barY' not found in output" >&2
  exit 1
fi

echo "PASS: --rename-dynamic-symbols (map file) applied 2 renames"
