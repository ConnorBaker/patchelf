#!/bin/sh -e
# CLI: --set-rpath on a binary with NO existing DT_RPATH/DT_RUNPATH
# entry should INSERT a new DT_RUNPATH entry (matching C++ patchelf's
# appendRPath behavior at patchelf.cc:1701).  This case is handled
# by the `addRpathEntry` op; without it, the string would be appended
# to .dynstr with no corresponding dynamic entry.

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/34-cli-set-rpath-no-entry-inserts"
mkdir -p "$SCRATCH"

# Fixture: ELF64 with .dynamic that has NO rpath entry (just DT_STRSZ + DT_NULL).
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
dynamic_shdr = u32(19) + u32(6) + u64(0) + u64(0) + u64(405) + u64(32) \
             + u32(2) + u32(0) + u64(8) + u64(16)

shstrtab = b"\x00.shstrtab\x00.dynstr\x00.dynamic\x00"
dynstr   = b"\x00"
# DT_STRSZ(10) → 1, DT_NULL.
dynamic = u64(10) + u64(1) + u64(0) + u64(0)

with open(sys.argv[1], "wb") as f:
    f.write(hdr + pt_load + null_shdr + shstr_shdr + dynstr_shdr + dynamic_shdr
            + shstrtab + dynstr + dynamic)
PY

NEW_RPATH="/opt/lib"
"$PATCHELF_BIN" --set-rpath "$NEW_RPATH" "$SCRATCH/input.elf"

# Verify --print-rpath now returns the inserted rpath.
got=$("$PATCHELF_BIN" --print-rpath "$SCRATCH/input.elf")
if [ "$got" != "$NEW_RPATH" ]; then
  echo "FAIL: --print-rpath returned '$got', expected '$NEW_RPATH'" >&2
  exit 1
fi

# Verify .dynamic contains a DT_RUNPATH entry + DT_STRSZ matches.
python3 - "$SCRATCH/input.elf" "$NEW_RPATH" <<'PY'
import sys, struct
data = open(sys.argv[1], "rb").read()
new_rpath = sys.argv[2]

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

dynstr_off = dynstr_size = None
dynamic_off = dynamic_size = None
for i in range(e_shnum):
    n = shname(i)
    if n == ".dynstr":
        dynstr_off, dynstr_size = shdr(i)[4], shdr(i)[5]
    elif n == ".dynamic":
        dynamic_off, dynamic_size = shdr(i)[4], shdr(i)[5]

dynstr_bytes = data[dynstr_off:dynstr_off+dynstr_size]

# Walk .dynamic for DT_RUNPATH(29) or DT_RPATH(15).
runpath_val = None; rpath_val = None; strsz_val = None
for i in range(dynamic_size // 16):
    tag, val = struct.unpack_from("<qQ", data, dynamic_off + i * 16)
    if tag == 29: runpath_val = val
    elif tag == 15: rpath_val = val
    elif tag == 10: strsz_val = val

if runpath_val is None and rpath_val is None:
    print("FAIL: no DT_RUNPATH/DT_RPATH entry in .dynamic", file=sys.stderr)
    sys.exit(1)

v = runpath_val if runpath_val is not None else rpath_val
if v >= dynstr_size:
    print(f"FAIL: rpath offset {v} out of dynstr bounds {dynstr_size}", file=sys.stderr)
    sys.exit(1)
end = dynstr_bytes.index(b"\x00", v)
resolved = dynstr_bytes[v:end].decode()
if resolved != new_rpath:
    print(f"FAIL: resolved rpath {resolved!r} != expected {new_rpath!r}", file=sys.stderr)
    sys.exit(1)

if strsz_val != dynstr_size:
    print(f"FAIL: DT_STRSZ={strsz_val} but .dynstr.sh_size={dynstr_size}",
          file=sys.stderr)
    sys.exit(1)

print(f"PASS: --set-rpath inserted a new rpath entry resolving to "
      f"{new_rpath!r}; DT_STRSZ in sync ({strsz_val})")
PY
