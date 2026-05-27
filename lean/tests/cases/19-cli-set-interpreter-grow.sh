#!/bin/sh -e
# End-to-end CLI test: --set-interpreter grow path.
# When the new path is LONGER than the existing .interp slot, the op
# goes through the layout engine (finalizeInterpGrowth), relocating
# .interp to a fresh end-of-file region. Verify the new interpreter
# reads back correctly and the file grew.

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/19-cli-set-interpreter-grow"
mkdir -p "$SCRATCH"

# Fixture: ELF64 with a SHORT .interp slot (8 bytes: "/a.so\0" + 2 pad).
# We'll set a LONG new path that can't possibly fit, forcing the grow path.
python3 - "$SCRATCH/input.elf" <<'PY'
import sys, struct
def u8(v): return bytes([v])
def u16(v): return struct.pack("<H", v)
def u32(v): return struct.pack("<I", v)
def u64(v): return struct.pack("<Q", v)

ident = b"\x7fELF" + u8(2) + u8(1) + u8(1) + u8(0) + (b"\x00" * 8)
pt_interp_offset = 312
pt_interp_size = 8
old_path = b"/a.so\x00"
interp_content = old_path + b"\x00" * (pt_interp_size - len(old_path))
shstrtab_off = pt_interp_offset + pt_interp_size
shstrtab = b"\x00" + b".shstrtab\x00" + b".interp\x00"
hdr = ident + u16(2) + u16(62) + u32(1) + u64(0) + u64(64) + u64(120) \
    + u32(0) + u16(64) + u16(56) + u16(1) + u16(64) + u16(3) + u16(1)
phdr = u32(3) + u32(4) + u64(pt_interp_offset) + u64(0) + u64(0) \
     + u64(len(old_path)) + u64(len(old_path)) + u64(1)
null_shdr = b"\x00" * 64
shstrtab_shdr = u32(1) + u32(3) + u64(0) + u64(0) + u64(shstrtab_off) \
              + u64(len(shstrtab)) + u32(0) + u32(0) + u64(1) + u64(0)
interp_shdr = u32(11) + u32(1) + u64(2) + u64(0) + u64(pt_interp_offset) \
            + u64(pt_interp_size) + u32(0) + u32(0) + u64(1) + u64(0)
out = hdr + phdr + null_shdr + shstrtab_shdr + interp_shdr + interp_content + shstrtab
with open(sys.argv[1], "wb") as f:
    f.write(out)
PY

original_size=$(wc -c <"$SCRATCH/input.elf" | tr -d ' ')

# Initial state: old path is "/a.so".
before_path=$("$PATCHELF_BIN" print-interpreter "$SCRATCH/input.elf")
if [ "$before_path" != "/a.so" ]; then
  echo "FAIL: pre-mutation print-interpreter returned '$before_path'" >&2
  exit 1
fi

# Rewrite to a LONG path that cannot fit the 8-byte slot.
# "/lib64/ld-linux-x86-64.so.2" is 27 bytes + NUL = 28 bytes, way bigger than 8.
new_path="/lib64/ld-linux-x86-64.so.2"
"$PATCHELF_BIN" set-interpreter --no-validate "$new_path" "$SCRATCH/input.elf"

# --print-interpreter now returns the new path.
after_path=$("$PATCHELF_BIN" print-interpreter "$SCRATCH/input.elf")
if [ "$after_path" != "$new_path" ]; then
  echo "FAIL: post-mutation print-interpreter returned '$after_path', expected '$new_path'" >&2
  exit 1
fi

# File must have GROWN (the new interp region is appended end-of-file).
new_size=$(wc -c <"$SCRATCH/input.elf" | tr -d ' ')
if [ "$new_size" -le "$original_size" ]; then
  echo "FAIL: file did not grow (original=$original_size, new=$new_size)" >&2
  exit 1
fi

echo "PASS: --set-interpreter grow path writes new interp end-of-file; file grew from $original_size to $new_size"
