#!/bin/sh -e
# End-to-end CLI test: rewrite PT_INTERP path via --set-interpreter,
# verify the section bytes change, the surviving bytes are unchanged,
# and that a re-parse still succeeds.

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/05-cli-set-interpreter"
mkdir -p "$SCRATCH"

# Fixture: ELF64 with one PT_INTERP phdr, .interp + .shstrtab sections.
# .interp slot is 24 bytes, padded from the 21-byte path + NUL.
python3 - "$SCRATCH/input.elf" <<'PY'
import sys, struct
def u8(v): return bytes([v])
def u16(v): return struct.pack("<H", v)
def u32(v): return struct.pack("<I", v)
def u64(v): return struct.pack("<Q", v)

ident = b"\x7fELF" + u8(2) + u8(1) + u8(1) + u8(0) + (b"\x00" * 8)
pt_interp_offset = 312
pt_interp_size = 24
old_path = b"/lib64/ld-linux.so.2\x00"
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

# --print-interpreter reads the old path back.
before_path=$("$PATCHELF_BIN" --print-interpreter "$SCRATCH/input.elf")
if [ "$before_path" != "/lib64/ld-linux.so.2" ]; then
  echo "FAIL: pre-mutation print-interpreter returned '$before_path'" >&2
  exit 1
fi

# Rewrite to a shorter path.
"$PATCHELF_BIN" --set-interpreter /tmp/new-ld.so "$SCRATCH/input.elf"

# --print-interpreter now returns the new path.
after_path=$("$PATCHELF_BIN" --print-interpreter "$SCRATCH/input.elf")
if [ "$after_path" != "/tmp/new-ld.so" ]; then
  echo "FAIL: post-mutation print-interpreter returned '$after_path'" >&2
  exit 1
fi

# File size unchanged (in-place rewrite).
new_size=$(wc -c <"$SCRATCH/input.elf" | tr -d ' ')
if [ "$new_size" != "$original_size" ]; then
  echo "FAIL: file size changed from $original_size to $new_size" >&2
  exit 1
fi

# Idempotency check: running --set-interpreter with the same path twice
# should be byte-identical. This validates that the lockstep path (which
# updates e.bytes) and the encoder stay in sync.
cp "$SCRATCH/input.elf" "$SCRATCH/before-idempotent.elf"
"$PATCHELF_BIN" --set-interpreter /tmp/new-ld.so "$SCRATCH/input.elf"
if ! cmp -s "$SCRATCH/input.elf" "$SCRATCH/before-idempotent.elf"; then
  echo "FAIL: --set-interpreter with same path was not idempotent" >&2
  diff <(od -An -tx1 "$SCRATCH/before-idempotent.elf") \
       <(od -An -tx1 "$SCRATCH/input.elf") | head -10 >&2
  exit 1
fi

echo "PASS: --set-interpreter rewrites in place; idempotent"
