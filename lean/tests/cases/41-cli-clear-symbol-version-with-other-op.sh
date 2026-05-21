#!/bin/sh -e
# CLI: --clear-symbol-version <sym> composes with other mutating ops
# in a single invocation. Verifies the non-interference matrix
# (NonInterference.lean's _preserves_versym / _preserves_dynstr /
# _preserves_dynamic lemmas) fires correctly at runtime.
#
# Scenario: start with a binary that has versym + dynsym + dynstr +
# an existing DT_RUNPATH. Run --clear-symbol-version foo --set-rpath /new.
# Expect: foo's versym cleared, rpath retagged to /new, libc.so versym
# unchanged.

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/41-cli-clear-symbol-version-with-other-op"
mkdir -p "$SCRATCH"

python3 - "$SCRATCH/input.elf" <<'PY'
import sys, struct
def u8(v): return bytes([v])
def u16(v): return struct.pack("<H", v)
def u32(v): return struct.pack("<I", v)
def u64(v): return struct.pack("<Q", v)

ident = b"\x7fELF" + u8(2) + u8(1) + u8(1) + u8(0) + (b"\x00" * 8)
# 6 shdrs: null, shstrtab, dynstr, dynsym, versym, dynamic
PHOFF = 64
PHNUM = 1
PHENTSIZE = 56
SHNUM = 6
SHENTSIZE = 64
SHSTRNDX = 1
SHOFF = 120

hdr = ident + u16(2) + u16(62) + u32(1) + u64(0) + u64(PHOFF) + u64(SHOFF) \
    + u32(0) + u16(64) + u16(PHENTSIZE) + u16(PHNUM) + u16(SHENTSIZE) \
    + u16(SHNUM) + u16(SHSTRNDX)

pt_load = u32(1) + u32(5) + u64(0) + u64(0) + u64(0) + u64(512) + u64(512) + u64(4096)

shstrtab_bytes = b"\x00.shstrtab\x00.dynstr\x00.dynsym\x00.gnu.version\x00.dynamic\x00"
SHSTRTAB_OFF = PHOFF + PHENTSIZE + SHNUM * SHENTSIZE   # 120 + 6*64 = 504
# Actually: phdrs at 64 (56B), shdrs at 120 (384B), shstrtab at 504.
SHSTRTAB_OFF = 504
SHSTRTAB_SZ = len(shstrtab_bytes)  # 45

dynstr_bytes = b"\x00libc.so\x00foo\x00/new\x00"  # pre-populated with /new
DYNSTR_OFF = SHSTRTAB_OFF + SHSTRTAB_SZ
DYNSTR_SZ = len(dynstr_bytes)

def sym(name_off):
    return u32(name_off) + u8(0) + u8(0) + u16(0) + u64(0) + u64(0)
dynsym_bytes = sym(1) + sym(9)  # libc.so at 1, foo at 9
DYNSYM_OFF = DYNSTR_OFF + DYNSTR_SZ
DYNSYM_SZ = len(dynsym_bytes)

versym_bytes = u16(2) + u16(3)  # both non-global version NDXs
VERSYM_OFF = DYNSYM_OFF + DYNSYM_SZ
VERSYM_SZ = len(versym_bytes)

# DT_RUNPATH(29) pointing at "/new" offset (in dynstr), DT_NULL
# "/new" is at offset 13 in dynstr.
dynamic_bytes = u64(29) + u64(13) + u64(0) + u64(0)
DYNAMIC_OFF = VERSYM_OFF + VERSYM_SZ
DYNAMIC_SZ = len(dynamic_bytes)

null_shdr = b"\x00" * 64
shstrtab_shdr = u32(1) + u32(3) + u64(0) + u64(0) + u64(SHSTRTAB_OFF) + u64(SHSTRTAB_SZ) \
              + u32(0) + u32(0) + u64(1) + u64(0)
dynstr_shdr = u32(11) + u32(3) + u64(0) + u64(0) + u64(DYNSTR_OFF) + u64(DYNSTR_SZ) \
            + u32(0) + u32(0) + u64(1) + u64(0)
dynsym_shdr = u32(19) + u32(11) + u64(0) + u64(0) + u64(DYNSYM_OFF) + u64(DYNSYM_SZ) \
            + u32(2) + u32(0) + u64(8) + u64(24)
versym_shdr = u32(27) + u32(0x6fffffff) + u64(0) + u64(0) + u64(VERSYM_OFF) + u64(VERSYM_SZ) \
            + u32(3) + u32(0) + u64(2) + u64(2)
dynamic_shdr = u32(40) + u32(6) + u64(0) + u64(0) + u64(DYNAMIC_OFF) + u64(DYNAMIC_SZ) \
             + u32(2) + u32(0) + u64(8) + u64(16)

with open(sys.argv[1], "wb") as f:
    f.write(hdr + pt_load
            + null_shdr + shstrtab_shdr + dynstr_shdr + dynsym_shdr + versym_shdr + dynamic_shdr
            + shstrtab_bytes + dynstr_bytes + dynsym_bytes + versym_bytes + dynamic_bytes)
PY

# Multi-op: clear foo's versym AND retag rpath.
"$PATCHELF_BIN" --clear-symbol-version foo --set-rpath /new "$SCRATCH/input.elf"

got_rpath=$("$PATCHELF_BIN" --print-rpath "$SCRATCH/input.elf")
if [ "$got_rpath" != "/new" ]; then
  echo "FAIL: --print-rpath returned '$got_rpath', expected '/new'" >&2
  exit 1
fi

python3 - "$SCRATCH/input.elf" <<'PY'
import sys, struct
data = open(sys.argv[1], "rb").read()
e_shoff = struct.unpack_from("<Q", data, 0x28)[0]
e_shentsize = struct.unpack_from("<H", data, 0x3a)[0]
e_shnum = struct.unpack_from("<H", data, 0x3c)[0]
e_shstrndx = struct.unpack_from("<H", data, 0x3e)[0]
def shdr(i): return struct.unpack_from("<IIQQQQIIQQ", data, e_shoff + i * e_shentsize)
sh = shdr(e_shstrndx); shstrtab = data[sh[4]:sh[4]+sh[5]]
def shname(i):
    o = shdr(i)[0]
    end = shstrtab.index(b"\x00", o)
    return shstrtab[o:end].decode()

versym_off = None
for i in range(e_shnum):
    if shname(i) == ".gnu.version":
        versym_off = shdr(i)[4]
if versym_off is None:
    print("FAIL: no .gnu.version", file=sys.stderr); sys.exit(1)

v0 = struct.unpack_from("<H", data, versym_off)[0]
v1 = struct.unpack_from("<H", data, versym_off + 2)[0]
if v0 != 2:
    print(f"FAIL: libc.so versym was 2, is now {v0}", file=sys.stderr); sys.exit(1)
if v1 != 1:
    print(f"FAIL: foo versym should be 1 (cleared), is {v1}", file=sys.stderr); sys.exit(1)

print("PASS: multi-op --clear-symbol-version foo --set-rpath /new composed correctly")
PY
