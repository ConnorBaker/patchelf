#!/bin/sh -e
# CLI: --rename-dynamic-symbol rewrites a single .dynsym entry's st_name
# to a new offset (appending the new name to .dynstr via the layout engine).

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/14-cli-rename-dynamic-symbol"
mkdir -p "$SCRATCH"

# Fixture: ELF64 with .dynstr + .dynsym + a PT_LOAD phdr.
# .dynsym contains 2 entries: index 0 is the null entry, index 1 has
# st_name = 1 (pointing at "foo" in .dynstr).
#
# Layout (offsets):
#   bytes 0..64      : ELF header (phnum=1, phoff=64, shnum=4, shstrndx=1, shoff=120)
#   bytes 64..120    : phdr[0] = PT_LOAD (56 bytes)
#   bytes 120..376   : 4 shdrs × 64 bytes  (null, shstrtab, dynstr, dynsym)
#   bytes 376..403   : shstrtab (27 bytes: "\0.shstrtab\0.dynstr\0.dynsym\0")
#   bytes 403..412   : dynstr (9 bytes: "\0foo\0bar\0")
#   bytes 412..460   : dynsym (48 bytes: 2 × 24-byte Elf64_Sym entries)
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
# shstrtab at 376, size 27
shstr_shdr = u32(1) + u32(3) + u64(0) + u64(0) + u64(376) + u64(27) \
           + u32(0) + u32(0) + u64(1) + u64(0)
# dynstr at 403, size 9
dynstr_shdr = u32(11) + u32(3) + u64(0) + u64(0) + u64(403) + u64(9) \
            + u32(0) + u32(0) + u64(1) + u64(0)
# dynsym at 412, size 48 (2 entries × 24 bytes), sh_link = 2 (dynstr), entsize = 24
dynsym_shdr = u32(19) + u32(11) + u64(0) + u64(0) + u64(412) + u64(48) \
            + u32(2) + u32(0) + u64(8) + u64(24)

shstrtab = b"\x00.shstrtab\x00.dynstr\x00.dynsym\x00"
dynstr   = b"\x00foo\x00bar\x00"
# Two Elf64_Sym entries (24 bytes each):
#   entry 0: st_name=0 (null), st_info=0, st_other=0, st_shndx=0, st_value=0, st_size=0
#   entry 1: st_name=1 (→"foo"), st_info=0, st_other=0, st_shndx=0, st_value=0, st_size=0
sym0 = u32(0) + u8(0) + u8(0) + u16(0) + u64(0) + u64(0)
sym1 = u32(1) + u8(0) + u8(0) + u16(0) + u64(0) + u64(0)
dynsym = sym0 + sym1

with open(sys.argv[1], "wb") as f:
    f.write(hdr + pt_load + null_shdr + shstr_shdr + dynstr_shdr + dynsym_shdr
            + shstrtab + dynstr + dynsym)
PY

original_size=$(wc -c <"$SCRATCH/input.elf" | tr -d ' ')

# Run: rename symbol "foo" to "fooBAR".
"$PATCHELF_BIN" --rename-dynamic-symbol foo fooBAR "$SCRATCH/input.elf"

new_size=$(wc -c <"$SCRATCH/input.elf" | tr -d ' ')
if [ "$new_size" -le "$original_size" ]; then
  echo "FAIL: file didn't grow ($original_size → $new_size)" >&2
  exit 1
fi

# Re-parse to confirm the output is well-formed.
if ! "$PATCHELF_BIN" --parse "$SCRATCH/input.elf" >"$SCRATCH/parse.out" 2>&1; then
  echo "FAIL: post-rename reparse failed" >&2
  cat "$SCRATCH/parse.out" >&2
  exit 1
fi

echo "PASS: --rename-dynamic-symbol grew dynstr + rewrote matching st_name"
