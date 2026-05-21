#!/bin/sh -e
# CLI: --clear-symbol-version <sym> sets the .gnu.version entry to
# VER_NDX_GLOBAL (1) for every .dynsym symbol whose name matches <sym>.
# Other versym entries and all other sections are unchanged.

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/30-cli-clear-symbol-version"
mkdir -p "$SCRATCH"

# Build a minimal ELF64 with:
#  - shstrtab
#  - dynstr with names "libc.so\0" and "foo\0"
#  - dynsym with 2 symbols (st_name pointing at "libc.so" and "foo")
#  - versym with 2 entries, both set to 2 (some non-global version NDX)
# Then run --clear-symbol-version foo; the entry for "foo" should be 1
# and the other entry should remain 2.
python3 - "$SCRATCH/input.elf" <<'PY'
import sys, struct
def u8(v): return bytes([v])
def u16(v): return struct.pack("<H", v)
def u32(v): return struct.pack("<I", v)
def u64(v): return struct.pack("<Q", v)

ident = b"\x7fELF" + u8(2) + u8(1) + u8(1) + u8(0) + (b"\x00" * 8)
# 5 shdrs: null, shstrtab, dynstr, dynsym, versym
PHOFF = 64
PHNUM = 1
PHENTSIZE = 56
SHNUM = 5
SHENTSIZE = 64
SHSTRNDX = 1
# Layout:
#   header at 0, size 64
#   phdrs at 64, 56 bytes
#   shdrs at 120, 5*64 = 320 bytes; end at 440
#   shstrtab bytes at 440; sections after
SHOFF = 120

hdr = ident + u16(2) + u16(62) + u32(1) + u64(0) + u64(PHOFF) + u64(SHOFF) \
    + u32(0) + u16(64) + u16(PHENTSIZE) + u16(PHNUM) + u16(SHENTSIZE) \
    + u16(SHNUM) + u16(SHSTRNDX)

pt_load = u32(1) + u32(5) + u64(0) + u64(0) + u64(0) + u64(256) + u64(256) + u64(4096)

# shstrtab: "\0.shstrtab\0.dynstr\0.dynsym\0.gnu.version\0" (40 bytes)
shstrtab_bytes = b"\x00.shstrtab\x00.dynstr\x00.dynsym\x00.gnu.version\x00"
SHSTRTAB_OFF = 440
SHSTRTAB_SZ = len(shstrtab_bytes)   # 40

# dynstr: "\0libc.so\0foo\0"  (13 bytes)
dynstr_bytes = b"\x00libc.so\x00foo\x00"
DYNSTR_OFF = SHSTRTAB_OFF + SHSTRTAB_SZ   # 480
DYNSTR_SZ = len(dynstr_bytes)             # 13

# dynsym: 2 symbols, each 24 bytes = 48 bytes.
# Symbol 0: st_name = 1 ("libc.so"), other fields 0.
# Symbol 1: st_name = 9 ("foo"), other fields 0.
def sym(name_off):
    return u32(name_off) + u8(0) + u8(0) + u16(0) + u64(0) + u64(0)
dynsym_bytes = sym(1) + sym(9)
DYNSYM_OFF = DYNSTR_OFF + DYNSTR_SZ       # 493
DYNSYM_SZ = len(dynsym_bytes)             # 48

# versym: 2 entries, each 2 bytes = 4 bytes. Initially both set to 2.
versym_bytes = u16(2) + u16(2)
VERSYM_OFF = DYNSYM_OFF + DYNSYM_SZ       # 541
VERSYM_SZ = len(versym_bytes)             # 4

# Shdrs: name offsets into shstrtab.
null_shdr = b"\x00" * 64
# shstrtab: sh_name=1, sh_type=3 (STRTAB)
shstrtab_shdr = u32(1) + u32(3) + u64(0) + u64(0) + u64(SHSTRTAB_OFF) + u64(SHSTRTAB_SZ) \
              + u32(0) + u32(0) + u64(1) + u64(0)
# dynstr: sh_name=11, sh_type=3
dynstr_shdr = u32(11) + u32(3) + u64(0) + u64(0) + u64(DYNSTR_OFF) + u64(DYNSTR_SZ) \
            + u32(0) + u32(0) + u64(1) + u64(0)
# dynsym: sh_name=19, sh_type=11 (DYNSYM), sh_link=2 (dynstr idx), sh_entsize=24
dynsym_shdr = u32(19) + u32(11) + u64(0) + u64(0) + u64(DYNSYM_OFF) + u64(DYNSYM_SZ) \
            + u32(2) + u32(0) + u64(8) + u64(24)
# versym: sh_name=27, sh_type=0x6fffffff (SHT_GNU_versym), sh_link=3, sh_entsize=2
versym_shdr = u32(27) + u32(0x6fffffff) + u64(0) + u64(0) + u64(VERSYM_OFF) + u64(VERSYM_SZ) \
            + u32(3) + u32(0) + u64(2) + u64(2)

with open(sys.argv[1], "wb") as f:
    f.write(hdr + pt_load
            + null_shdr + shstrtab_shdr + dynstr_shdr + dynsym_shdr + versym_shdr
            + shstrtab_bytes + dynstr_bytes + dynsym_bytes + versym_bytes)
PY

"$PATCHELF_BIN" --clear-symbol-version foo "$SCRATCH/input.elf"

python3 - "$SCRATCH/input.elf" <<'PY'
import sys, struct
data = open(sys.argv[1], "rb").read()

e_shoff = struct.unpack_from("<Q", data, 0x28)[0]
e_shentsize = struct.unpack_from("<H", data, 0x3a)[0]
e_shnum = struct.unpack_from("<H", data, 0x3c)[0]
e_shstrndx = struct.unpack_from("<H", data, 0x3e)[0]

def shdr(i):
    return struct.unpack_from("<IIQQQQIIQQ", data, e_shoff + i * e_shentsize)

sh = shdr(e_shstrndx)
shstrtab = data[sh[4]:sh[4]+sh[5]]
def shname(i):
    name_off = shdr(i)[0]
    end = shstrtab.index(b"\x00", name_off)
    return shstrtab[name_off:end].decode()

versym_off = versym_size = None
for i in range(e_shnum):
    if shname(i) == ".gnu.version":
        versym_off = shdr(i)[4]
        versym_size = shdr(i)[5]

if versym_off is None:
    print("FAIL: no .gnu.version section in output", file=sys.stderr); sys.exit(1)

v0 = struct.unpack_from("<H", data, versym_off)[0]
v1 = struct.unpack_from("<H", data, versym_off + 2)[0]

# Symbol 0 is "libc.so" — should be unchanged (still 2).
# Symbol 1 is "foo" — should be cleared to 1 (VER_NDX_GLOBAL).
if v0 != 2:
    print(f"FAIL: libc.so versym changed from 2 to {v0}", file=sys.stderr); sys.exit(1)
if v1 != 1:
    print(f"FAIL: foo versym should be 1 (VER_NDX_GLOBAL), got {v1}", file=sys.stderr); sys.exit(1)

print(f"PASS: --clear-symbol-version foo set versym[1]=1 (libc.so versym still 2)")
PY
