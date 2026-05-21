#!/bin/sh -e
# CLI: --force-rpath causes --set-rpath to emit DT_RPATH (tag 0x0f)
# instead of DT_RUNPATH (0x1d). Without --force-rpath, the default is
# DT_RUNPATH.
#
# We run --set-rpath on a fixture and confirm the resulting .dynamic
# has DT_RUNPATH (under default) vs DT_RPATH (under --force-rpath) by
# re-parsing the output via --print-rpath (which checks both tags) and
# by scanning the output bytes for the expected tag.

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/26-cli-force-rpath"
mkdir -p "$SCRATCH"

# Fixture: has .dynamic with DT_RPATH (value=0, pointing at '' in dynstr)
# + DT_NULL. After --set-rpath we expect the tag to be retagged.
python3 - "$SCRATCH/base.elf" <<'PY'
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
dynstr_shdr = u32(11) + u32(3) + u64(0) + u64(0) + u64(404) + u64(11) \
            + u32(0) + u32(0) + u64(1) + u64(0)
# .dynamic: DT_RPATH (0x0f) pointing at offset 1 in dynstr, then DT_NULL.
dynamic_shdr = u32(19) + u32(6) + u64(0) + u64(0) + u64(415) + u64(32) \
             + u32(2) + u32(0) + u64(8) + u64(16)
shstrtab = b"\x00.shstrtab\x00.dynstr\x00.dynamic\x00"
dynstr   = b"\x00old_path\x00\x00"
dynamic = u64(0x0f) + u64(1) + u64(0) + u64(0)
with open(sys.argv[1], "wb") as f:
    f.write(hdr + pt_load + null_shdr + shstr_shdr + dynstr_shdr + dynamic_shdr
            + shstrtab + dynstr + dynamic)
PY

# Default: --set-rpath retags to DT_RUNPATH (0x1d).
cp "$SCRATCH/base.elf" "$SCRATCH/default.elf"
"$PATCHELF_BIN" --set-rpath /newpath "$SCRATCH/default.elf"
# --force-rpath: retags to DT_RPATH (0x0f).
cp "$SCRATCH/base.elf" "$SCRATCH/forced.elf"
"$PATCHELF_BIN" --force-rpath --set-rpath /newpath "$SCRATCH/forced.elf"

# Both should re-parse, and --print-rpath should return "/newpath" in both.
out_default=$("$PATCHELF_BIN" --print-rpath "$SCRATCH/default.elf")
out_forced=$("$PATCHELF_BIN"  --print-rpath "$SCRATCH/forced.elf")
if [ "$out_default" != "/newpath" ]; then
  echo "FAIL: default --print-rpath = '$out_default', expected /newpath" >&2; exit 1
fi
if [ "$out_forced" != "/newpath" ]; then
  echo "FAIL: forced --print-rpath = '$out_forced', expected /newpath" >&2; exit 1
fi

# Now check tag bytes. Parse the ELF shdrs to find the .dynamic section
# and iterate its 16-byte entries to find the DT_RUNPATH / DT_RPATH tag.
python3 - "$SCRATCH/default.elf" "$SCRATCH/forced.elf" <<'PY'
import sys, struct

def find_dynamic_tags(path):
    data = open(path, "rb").read()
    # Parse ELF64 header.
    shoff, = struct.unpack_from("<Q", data, 0x28)
    shentsize, shnum = struct.unpack_from("<HH", data, 0x3a)
    tags_found = set()
    for i in range(shnum):
        off = shoff + i * shentsize
        sh_type, = struct.unpack_from("<I", data, off + 4)
        if sh_type != 6:  # SHT_DYNAMIC
            continue
        sh_offset, sh_size = struct.unpack_from("<QQ", data, off + 24)
        # Iterate 16-byte DynEntries.
        for j in range(sh_size // 16):
            tag, val = struct.unpack_from("<QQ", data, sh_offset + j * 16)
            tags_found.add(tag)
    return tags_found

def_tags = find_dynamic_tags(sys.argv[1])
force_tags = find_dynamic_tags(sys.argv[2])

if 0x1d not in def_tags:
    print(f"FAIL: default .dynamic has no DT_RUNPATH tag. Found: {[hex(t) for t in def_tags]}", file=sys.stderr)
    sys.exit(1)
if 0x0f not in force_tags:
    print(f"FAIL: --force-rpath .dynamic has no DT_RPATH tag. Found: {[hex(t) for t in force_tags]}", file=sys.stderr)
    sys.exit(1)
if 0x0f in def_tags:
    print(f"FAIL: default unexpectedly has DT_RPATH. Found: {[hex(t) for t in def_tags]}", file=sys.stderr)
    sys.exit(1)
if 0x1d in force_tags:
    print(f"FAIL: --force-rpath unexpectedly has DT_RUNPATH. Found: {[hex(t) for t in force_tags]}", file=sys.stderr)
    sys.exit(1)
print(f"default: {[hex(t) for t in def_tags]}  forced: {[hex(t) for t in force_tags]}")
PY

echo "PASS: --force-rpath chooses DT_RPATH, default chooses DT_RUNPATH"
