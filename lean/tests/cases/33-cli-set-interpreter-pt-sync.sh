#!/bin/sh -e
# CLI: after --set-interpreter grows .interp, the PT_INTERP phdr's
# p_offset must be updated to match the relocated .interp shdr's
# sh_offset. Without this, the kernel reads the wrong interpreter
# path bytes (the loader uses the phdr, not the shdr).

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/33-cli-set-interpreter-pt-sync"
mkdir -p "$SCRATCH"

# Fixture: a minimal ELF64 with PT_INTERP + .interp section pointing
# at "/lib/ld.so" (11 bytes + NUL = 12).
python3 - "$SCRATCH/input.elf" <<'PY'
import sys, struct
def u8(v): return bytes([v])
def u16(v): return struct.pack("<H", v)
def u32(v): return struct.pack("<I", v)
def u64(v): return struct.pack("<Q", v)

INTERP_STR = b"/lib/ld.so\x00"  # 11 bytes
INTERP_SZ = len(INTERP_STR)

ident = b"\x7fELF" + u8(2) + u8(1) + u8(1) + u8(0) + (b"\x00" * 8)

# 3 shdrs: null, .shstrtab, .interp.
# Header: 64; phdrs: 2 × 56 = 112; phdrs end at 176.
# shdrs at 176; 3 × 64 = 192; shdrs end at 368.
# shstrtab at 368, size 19 = "\0.shstrtab\0.interp\0" → 19 bytes.
# .interp at 387, size 11.
PHOFF = 64
PHENTSIZE = 56
PHNUM = 2
SHOFF = 176
SHENTSIZE = 64
SHNUM = 3
SHSTRNDX = 1
SHSTRTAB_OFF = 368
SHSTRTAB = b"\x00.shstrtab\x00.interp\x00"
SHSTRTAB_SZ = len(SHSTRTAB)
INTERP_OFF = SHSTRTAB_OFF + SHSTRTAB_SZ

hdr = ident + u16(2) + u16(62) + u32(1) + u64(0) + u64(PHOFF) + u64(SHOFF) \
    + u32(0) + u16(64) + u16(PHENTSIZE) + u16(PHNUM) + u16(SHENTSIZE) \
    + u16(SHNUM) + u16(SHSTRNDX)

# PT_LOAD covering the whole file.
pt_load = u32(1) + u32(5) + u64(0) + u64(0) + u64(0) + u64(INTERP_OFF + INTERP_SZ) \
        + u64(INTERP_OFF + INTERP_SZ) + u64(4096)
# PT_INTERP(3) pointing at .interp.
pt_interp = u32(3) + u32(4) + u64(INTERP_OFF) + u64(INTERP_OFF) + u64(INTERP_OFF) \
          + u64(INTERP_SZ) + u64(INTERP_SZ) + u64(1)

null_shdr = b"\x00" * 64
# shstrtab name offset = 1 (".shstrtab\0").
shstr_shdr = u32(1) + u32(3) + u64(0) + u64(0) + u64(SHSTRTAB_OFF) + u64(SHSTRTAB_SZ) \
           + u32(0) + u32(0) + u64(1) + u64(0)
# .interp name offset = 11 (".interp\0").
interp_shdr = u32(11) + u32(1) + u64(2) + u64(INTERP_OFF) + u64(INTERP_OFF) + u64(INTERP_SZ) \
            + u32(0) + u32(0) + u64(1) + u64(0)

with open(sys.argv[1], "wb") as f:
    f.write(hdr + pt_load + pt_interp + null_shdr + shstr_shdr + interp_shdr
            + SHSTRTAB + INTERP_STR)
PY

# Set a longer interpreter — forces .interp to grow and be relocated.
NEW_INTERP="/much/longer/path/to/ld-linux-x86-64.so.2"
"$PATCHELF_BIN" --set-interpreter "$NEW_INTERP" "$SCRATCH/input.elf"

# Parse the output: verify PT_INTERP's p_offset matches .interp's sh_offset.
python3 - "$SCRATCH/input.elf" <<'PY'
import sys, struct
data = open(sys.argv[1], "rb").read()

e_phoff    = struct.unpack_from("<Q", data, 0x20)[0]
e_shoff    = struct.unpack_from("<Q", data, 0x28)[0]
e_phentsize = struct.unpack_from("<H", data, 0x36)[0]
e_phnum    = struct.unpack_from("<H", data, 0x38)[0]
e_shentsize = struct.unpack_from("<H", data, 0x3a)[0]
e_shnum    = struct.unpack_from("<H", data, 0x3c)[0]
e_shstrndx = struct.unpack_from("<H", data, 0x3e)[0]

# Locate .interp shdr (by name).
def shdr(i):
    return struct.unpack_from("<IIQQQQIIQQ", data, e_shoff + i * e_shentsize)
sh = shdr(e_shstrndx)
shstrtab = data[sh[4]:sh[4]+sh[5]]
def shname(i):
    o = shdr(i)[0]
    end = shstrtab.index(b"\x00", o)
    return shstrtab[o:end].decode()

interp_offset = None
for i in range(e_shnum):
    if shname(i) == ".interp":
        interp_offset = shdr(i)[4]

if interp_offset is None:
    print("FAIL: no .interp section", file=sys.stderr); sys.exit(1)

# Find the PT_INTERP phdr.
pt_interp_offset = None
for i in range(e_phnum):
    base = e_phoff + i * e_phentsize
    ptype, = struct.unpack_from("<I", data, base)
    if ptype == 3:  # PT_INTERP
        pt_interp_offset, = struct.unpack_from("<Q", data, base + 8)
        break

if pt_interp_offset is None:
    print("FAIL: no PT_INTERP phdr", file=sys.stderr); sys.exit(1)

if pt_interp_offset != interp_offset:
    print(f"FAIL: PT_INTERP.p_offset={pt_interp_offset:#x} but "
          f".interp.sh_offset={interp_offset:#x}", file=sys.stderr)
    sys.exit(1)

print(f"PASS: PT_INTERP.p_offset ({pt_interp_offset}) matches "
      f".interp.sh_offset ({interp_offset}) after --set-interpreter")
PY
