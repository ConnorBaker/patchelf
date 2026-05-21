#!/bin/sh -e
# CLI: --add-needed must update DT_STRSZ after growing .dynstr.
# Same invariant as test 32 but exercises the two-section finalize path
# (finalizeDynstrAndDynamicGrowth) instead of the single-section one.

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/35-cli-add-needed-strsz-sync"
mkdir -p "$SCRATCH"

# Fixture: ELF64 with minimal .dynamic (just DT_STRSZ + DT_NULL) and
# .dynstr containing "libc.so\0".
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
dynstr_shdr = u32(11) + u32(3) + u64(0) + u64(0) + u64(404) + u64(9) \
            + u32(0) + u32(0) + u64(1) + u64(0)
dynamic_shdr = u32(19) + u32(6) + u64(0) + u64(0) + u64(413) + u64(32) \
             + u32(2) + u32(0) + u64(8) + u64(16)

shstrtab = b"\x00.shstrtab\x00.dynstr\x00.dynamic\x00"
dynstr   = b"\x00libc.so\x00"   # 9 bytes
# DT_STRSZ(10) → 9; DT_NULL.
dynamic = u64(10) + u64(9) + u64(0) + u64(0)

with open(sys.argv[1], "wb") as f:
    f.write(hdr + pt_load + null_shdr + shstr_shdr + dynstr_shdr + dynamic_shdr
            + shstrtab + dynstr + dynamic)
PY

# --add-needed inserts a new DT_NEEDED + appends name to .dynstr.
"$PATCHELF_BIN" --add-needed libfoo.so "$SCRATCH/input.elf"

# Verify DT_STRSZ matches post-op .dynstr.sh_size.
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

dynstr_size = dynamic_off = dynamic_size = None
for i in range(e_shnum):
    n = shname(i)
    if n == ".dynstr":
        dynstr_size = shdr(i)[5]
    elif n == ".dynamic":
        _, _, _, _, off, sz, *_ = shdr(i)
        dynamic_off, dynamic_size = off, sz

strsz_val = None
for i in range(dynamic_size // 16):
    tag, val = struct.unpack_from("<qQ", data, dynamic_off + i * 16)
    if tag == 10:
        strsz_val = val
        break

if strsz_val != dynstr_size:
    print(f"FAIL: DT_STRSZ={strsz_val} but .dynstr.sh_size={dynstr_size}",
          file=sys.stderr)
    sys.exit(1)

print(f"PASS: DT_STRSZ ({strsz_val}) matches .dynstr size ({dynstr_size}) "
      f"after --add-needed libfoo.so")
PY
