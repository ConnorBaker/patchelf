#!/bin/sh -e
# CLI: --force-rpath --set-rpath on a binary without an existing rpath
# entry should insert DT_RPATH (tag 15) rather than DT_RUNPATH (29).
# Covers the forceRpath=true dispatch into addRpathEntry.

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/38-cli-set-rpath-no-entry-force-rpath"
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
dynstr_shdr = u32(11) + u32(3) + u64(0) + u64(0) + u64(404) + u64(1) \
            + u32(0) + u32(0) + u64(1) + u64(0)
dynamic_shdr = u32(19) + u32(6) + u64(0) + u64(0) + u64(405) + u64(16) \
             + u32(2) + u32(0) + u64(8) + u64(16)

shstrtab = b"\x00.shstrtab\x00.dynstr\x00.dynamic\x00"
dynstr   = b"\x00"
# Just DT_NULL terminator, no rpath entries.
dynamic = u64(0) + u64(0)

with open(sys.argv[1], "wb") as f:
    f.write(hdr + pt_load + null_shdr + shstr_shdr + dynstr_shdr + dynamic_shdr
            + shstrtab + dynstr + dynamic)
PY

"$PATCHELF_BIN" --force-rpath --set-rpath /legacy/path "$SCRATCH/input.elf"

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
    o = shdr(i)[0]
    return shstrtab[o:shstrtab.index(b"\x00", o)].decode()

dynamic_off = dynamic_size = None
for i in range(e_shnum):
    if shname(i) == ".dynamic":
        dynamic_off = shdr(i)[4]; dynamic_size = shdr(i)[5]

has_rpath = has_runpath = False
for i in range(dynamic_size // 16):
    tag, _ = struct.unpack_from("<qQ", data, dynamic_off + i * 16)
    if tag == 15: has_rpath = True
    elif tag == 29: has_runpath = True

if not has_rpath:
    print("FAIL: --force-rpath didn't insert DT_RPATH", file=sys.stderr); sys.exit(1)
if has_runpath:
    print("FAIL: found DT_RUNPATH when --force-rpath should have emitted DT_RPATH", file=sys.stderr); sys.exit(1)

print("PASS: --force-rpath --set-rpath on fresh binary inserted DT_RPATH (not DT_RUNPATH)")
PY
