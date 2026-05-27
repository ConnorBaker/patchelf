#!/bin/sh -e
# CLI: --set-rpath must update DT_STRSZ to match the grown .dynstr size,
# matching C++ patchelf.cc:1247's rewriteSections() behavior. Without
# this, the dynamic linker sees a stale string-table size, causing
# lookups past the old end to fail.

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/32-cli-set-rpath-strsz-sync"
mkdir -p "$SCRATCH"

# Fixture: named-sections + PT_LOAD + DT_RPATH + DT_STRSZ (matching
# the initial .dynstr size of 11).
python3 - "$SCRATCH/input.elf" <<'PY'
import sys, struct
def u8(v): return bytes([v])
def u16(v): return struct.pack("<H", v)
def u32(v): return struct.pack("<I", v)
def u64(v): return struct.pack("<Q", v)

ident = b"\x7fELF" + u8(2) + u8(1) + u8(1) + u8(0) + (b"\x00" * 8)
# 4 shdrs: null, .shstrtab, .dynstr, .dynamic.
hdr = ident + u16(2) + u16(62) + u32(1) + u64(0) + u64(64) + u64(120) \
    + u32(0) + u16(64) + u16(56) + u16(1) + u16(64) + u16(4) + u16(1)

pt_load = u32(1) + u32(5) + u64(0) + u64(0) + u64(0) + u64(64) + u64(64) + u64(4096)

null_shdr = b"\x00" * 64
# Section layout: shdrs end at 64+56=120; then shstrtab bytes start.
# shstrtab offset = 120+64*4 = 376, size 28
# dynstr offset 404, size 11
# dynamic offset 415, size 48 (3 entries of 16 bytes: DT_RUNPATH, DT_STRSZ, DT_NULL)
shstr_shdr = u32(1) + u32(3) + u64(0) + u64(0) + u64(376) + u64(28) \
           + u32(0) + u32(0) + u64(1) + u64(0)
dynstr_shdr = u32(11) + u32(3) + u64(0) + u64(0) + u64(404) + u64(11) \
            + u32(0) + u32(0) + u64(1) + u64(0)
dynamic_shdr = u32(19) + u32(6) + u64(0) + u64(0) + u64(415) + u64(48) \
             + u32(2) + u32(0) + u64(8) + u64(16)

shstrtab = b"\x00.shstrtab\x00.dynstr\x00.dynamic\x00"
dynstr   = b"\x00libc.so\x00\x00\x00"
# DT_RUNPATH(29) → offset 1; DT_STRSZ(10) → 11 (initial dynstr size);
# DT_NULL(0) terminator.
dynamic = u64(29) + u64(1) + u64(10) + u64(11) + u64(0) + u64(0)

with open(sys.argv[1], "wb") as f:
    f.write(hdr + pt_load + null_shdr + shstr_shdr + dynstr_shdr + dynamic_shdr
            + shstrtab + dynstr + dynamic)
PY

# Set a new rpath — this grows .dynstr by "/new/lib/path\0" (14 bytes),
# so the new size should be 11 + 14 = 25.
"$PATCHELF_BIN" set-rpath /new/lib/path "$SCRATCH/input.elf"

# Extract DT_STRSZ and .dynstr size from the post-op ELF using python.
python3 - "$SCRATCH/input.elf" <<'PY'
import sys, struct

path = sys.argv[1]
with open(path, "rb") as f:
    data = f.read()

# Parse ELF64 header.
if data[:4] != b"\x7fELF":
    print("FAIL: not ELF", file=sys.stderr); sys.exit(1)

e_shoff    = struct.unpack_from("<Q", data, 0x28)[0]
e_shentsize = struct.unpack_from("<H", data, 0x3a)[0]
e_shnum    = struct.unpack_from("<H", data, 0x3c)[0]
e_shstrndx = struct.unpack_from("<H", data, 0x3e)[0]

# Read the shdr table.
def shdr(i):
    base = e_shoff + i * e_shentsize
    return struct.unpack_from("<IIQQQQIIQQ", data, base)
# fields: name type flags addr offset size link info align entsize

# Locate .shstrtab.
sh = shdr(e_shstrndx)
shstrtab = data[sh[4]:sh[4]+sh[5]]
def shname(i):
    name_off = shdr(i)[0]
    end = shstrtab.index(b"\x00", name_off)
    return shstrtab[name_off:end].decode()

dynstr_size = None
dynamic_off = dynamic_size = None
for i in range(e_shnum):
    n = shname(i)
    if n == ".dynstr":
        dynstr_size = shdr(i)[5]
    elif n == ".dynamic":
        _, _, _, _, off, sz, *_ = shdr(i)
        dynamic_off, dynamic_size = off, sz

if dynstr_size is None:
    print("FAIL: no .dynstr", file=sys.stderr); sys.exit(1)
if dynamic_off is None:
    print("FAIL: no .dynamic", file=sys.stderr); sys.exit(1)

# Walk .dynamic searching for DT_STRSZ (tag 10).
strsz_val = None
for i in range(dynamic_size // 16):
    tag, val = struct.unpack_from("<qQ", data, dynamic_off + i * 16)
    if tag == 10:
        strsz_val = val
        break

if strsz_val is None:
    print("FAIL: no DT_STRSZ entry", file=sys.stderr); sys.exit(1)

if strsz_val != dynstr_size:
    print(f"FAIL: DT_STRSZ={strsz_val} but .dynstr.sh_size={dynstr_size}",
          file=sys.stderr)
    sys.exit(1)

print(f"PASS: DT_STRSZ ({strsz_val}) matches .dynstr size ({dynstr_size}) after --set-rpath")
PY
