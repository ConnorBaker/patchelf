#!/bin/sh -e
# CLI: --add-needed grows .dynamic, triggering its relocation via
# finalizeDynstrAndDynamicGrowth. The matching PT_DYNAMIC phdr's
# p_offset must be updated to track the relocated .dynamic shdr.

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/37-cli-add-needed-pt-dynamic-sync"
mkdir -p "$SCRATCH"

# Fixture: ELF64 with PT_LOAD + PT_DYNAMIC phdrs + .dynstr + .dynamic.
python3 - "$SCRATCH/input.elf" <<'PY'
import sys, struct
def u8(v): return bytes([v])
def u16(v): return struct.pack("<H", v)
def u32(v): return struct.pack("<I", v)
def u64(v): return struct.pack("<Q", v)

ident = b"\x7fELF" + u8(2) + u8(1) + u8(1) + u8(0) + (b"\x00" * 8)
# 2 phdrs (PT_LOAD, PT_DYNAMIC): 112 bytes; 4 shdrs: 256 bytes.
# phdrs at 64, end at 176.
# shdrs at 176, end at 432.
# shstrtab at 432, size 28.
# dynstr at 460, size 9.
# dynamic at 469, size 32 (2 entries: DT_NEEDED + DT_NULL).
hdr = ident + u16(2) + u16(62) + u32(1) + u64(0) + u64(64) + u64(176) \
    + u32(0) + u16(64) + u16(56) + u16(2) + u16(64) + u16(4) + u16(1)

pt_load = u32(1) + u32(5) + u64(0) + u64(0) + u64(0) + u64(501) + u64(501) + u64(4096)
# PT_DYNAMIC(2) pointing at .dynamic at offset 469.
pt_dynamic = u32(2) + u32(6) + u64(469) + u64(469) + u64(469) + u64(32) + u64(32) + u64(8)

null_shdr = b"\x00" * 64
shstr_shdr = u32(1) + u32(3) + u64(0) + u64(0) + u64(432) + u64(28) \
           + u32(0) + u32(0) + u64(1) + u64(0)
dynstr_shdr = u32(11) + u32(3) + u64(0) + u64(0) + u64(460) + u64(9) \
            + u32(0) + u32(0) + u64(1) + u64(0)
dynamic_shdr = u32(19) + u32(6) + u64(0) + u64(0) + u64(469) + u64(32) \
             + u32(2) + u32(0) + u64(8) + u64(16)

shstrtab = b"\x00.shstrtab\x00.dynstr\x00.dynamic\x00"   # 28 bytes
dynstr   = b"\x00libc.so\x00"   # 9 bytes
# DT_NEEDED(1) → 1 ("libc.so"), DT_NULL.
dynamic = u64(1) + u64(1) + u64(0) + u64(0)

with open(sys.argv[1], "wb") as f:
    f.write(hdr + pt_load + pt_dynamic + null_shdr + shstr_shdr + dynstr_shdr + dynamic_shdr
            + shstrtab + dynstr + dynamic)
PY

"$PATCHELF_BIN" add-needed libfoo.so "$SCRATCH/input.elf"

# Verify PT_DYNAMIC.p_offset matches .dynamic.sh_offset.
python3 - "$SCRATCH/input.elf" <<'PY'
import sys, struct
data = open(sys.argv[1], "rb").read()

e_phoff = struct.unpack_from("<Q", data, 0x20)[0]
e_shoff = struct.unpack_from("<Q", data, 0x28)[0]
e_phentsize = struct.unpack_from("<H", data, 0x36)[0]
e_phnum = struct.unpack_from("<H", data, 0x38)[0]
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

dynamic_sh_offset = None
for i in range(e_shnum):
    if shname(i) == ".dynamic":
        dynamic_sh_offset = shdr(i)[4]

if dynamic_sh_offset is None:
    print("FAIL: no .dynamic section", file=sys.stderr); sys.exit(1)

pt_dynamic_offset = None
for i in range(e_phnum):
    base = e_phoff + i * e_phentsize
    ptype, = struct.unpack_from("<I", data, base)
    if ptype == 2:  # PT_DYNAMIC
        pt_dynamic_offset, = struct.unpack_from("<Q", data, base + 8)
        break

if pt_dynamic_offset is None:
    print("FAIL: no PT_DYNAMIC phdr", file=sys.stderr); sys.exit(1)

if pt_dynamic_offset != dynamic_sh_offset:
    print(f"FAIL: PT_DYNAMIC.p_offset={pt_dynamic_offset:#x} but "
          f".dynamic.sh_offset={dynamic_sh_offset:#x}", file=sys.stderr)
    sys.exit(1)

print(f"PASS: PT_DYNAMIC.p_offset ({pt_dynamic_offset}) matches "
      f".dynamic.sh_offset ({dynamic_sh_offset}) after --add-needed")
PY
