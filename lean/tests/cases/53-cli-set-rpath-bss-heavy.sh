#!/bin/sh -e
# CLI: --set-rpath on a BSS-heavy binary forces the fresh-PT_LOAD
# allocation path (ROADMAP §3.5a, in-place sub-case).
#
# Setup: a synthetic ELF with
#   * Last PT_LOAD memsz ≫ filesz (huge BSS gap) — `canExtendLastPtLoad`
#     rejects because extending would clobber the BSS allocation.
#   * Phdr table has at least 56 bytes of headroom before the first
#     section — `canAddFreshPtLoad` accepts.
#   * DT_RUNPATH so `set-rpath` triggers a dynstr grow (forcing
#     stale-section detection and the layout pre-pass).
# Expected: set-rpath succeeds (validator accepts); output's phnum
# is +1 (the fresh PT_LOAD entry); reparse + print-rpath roundtrip.

cd "$(dirname "$0")/.."

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"

SCRATCH="scratch/53-cli-set-rpath-bss-heavy"
mkdir -p "$SCRATCH"

python3 - "$SCRATCH/input.elf" <<'PY'
import sys, struct
def u8(v): return bytes([v])
def u16(v): return struct.pack("<H", v)
def u32(v): return struct.pack("<I", v)
def u64(v): return struct.pack("<Q", v)

# ELF header: ET_DYN x86-64, 1 phdr at 64, 4 shdrs at offset 1024.
# phdrs.size = 1 → phdr table at [64, 64+56) = [64, 120).
# Section starts after a 56+ byte gap, so canAddFreshPtLoad has room.
# shdr table at offset 1024 (well clear of the appended region's start).
PHDR_OFF = 64
SHDR_OFF = 1024
SHDR_COUNT = 5
PHDR_COUNT = 1

ident = b"\x7fELF" + u8(2) + u8(1) + u8(1) + u8(0) + (b"\x00" * 8)
hdr = ident + u16(2) + u16(62) + u32(1) + u64(0) + u64(PHDR_OFF) + u64(SHDR_OFF) \
    + u32(0) + u16(64) + u16(56) + u16(PHDR_COUNT) + u16(64) + u16(SHDR_COUNT) + u16(1)

# Single PT_LOAD covering the whole file with a large BSS gap.
# offset=0, vaddr=0, filesz=4096 (covers everything in the input file),
# memsz=4096+0x10000 = ~64KB BSS.  align=0x1000.
# This forces canExtendLastPtLoad to fail (vaddr+memsz roundUp would not
# match maxPtLoadVaddrEnd-derived startPage).
pt_load = u32(1) + u32(5) + u64(0) + u64(0) + u64(0) \
        + u64(4096) + u64(4096 + 0x10000) + u64(0x1000)

# Sections: NULL + shstrtab + dynstr + dynamic + .data (small).
# shstrtab content at offset 0x800 (after 56-byte phdr gap from 0x80
# onwards, with plenty of headroom).
SHSTRTAB_OFF = 0x800
SHSTRTAB = b"\x00.shstrtab\x00.dynstr\x00.dynamic\x00.data\x00"

DYNSTR_OFF = SHSTRTAB_OFF + len(SHSTRTAB)
DYNSTR = b"\x00libfoo.so\x00"  # offset 1 = "libfoo.so" (length 9 + null)

DYNAMIC_OFF = DYNSTR_OFF + len(DYNSTR)
# DT_RUNPATH(29) pointing at "libfoo.so" at offset 1, then DT_NULL.
DYNAMIC = u64(29) + u64(1) + u64(0) + u64(0)

DATA_OFF = DYNAMIC_OFF + len(DYNAMIC)
DATA = b"\x42\x00\x00\x00"

null_shdr = b"\x00" * 64

shstr_shdr = (u32(1) + u32(3) + u64(0) + u64(0) + u64(SHSTRTAB_OFF)
              + u64(len(SHSTRTAB)) + u32(0) + u32(0) + u64(1) + u64(0))
dynstr_shdr = (u32(11) + u32(3) + u64(0) + u64(0) + u64(DYNSTR_OFF)
               + u64(len(DYNSTR)) + u32(0) + u32(0) + u64(1) + u64(0))
dynamic_shdr = (u32(19) + u32(6) + u64(0) + u64(0) + u64(DYNAMIC_OFF)
                + u64(len(DYNAMIC)) + u32(2) + u32(0) + u64(8) + u64(16))
data_shdr = (u32(28) + u32(1) + u64(2) + u64(0) + u64(DATA_OFF)
             + u64(len(DATA)) + u32(0) + u32(0) + u64(1) + u64(0))

# Lay out the file:
# 0x000-0x040: ehdr
# 0x040-0x078: phdr  [56 bytes for 1 phdr]
# 0x078-0x400: zero-padded gap (room for new phdr at 0x078)
# 0x400-0x420: shdrs (5 * 64 = 320 bytes = 0x140 → ends 0x540)
# Wait, that's at SHDR_OFF=0x400, ending 0x540.
# Then at 0x800 onwards: shstrtab, dynstr, dynamic, data.
buf = bytearray()
buf += hdr             # 0..64
buf += pt_load         # 64..120
buf += b"\x00" * (SHDR_OFF - len(buf))    # pad to 1024
buf += null_shdr + shstr_shdr + dynstr_shdr + dynamic_shdr + data_shdr  # 5*64
buf += b"\x00" * (SHSTRTAB_OFF - len(buf))  # pad to 0x800
buf += SHSTRTAB
buf += DYNSTR
buf += DYNAMIC
buf += DATA

with open(sys.argv[1], "wb") as f:
    f.write(bytes(buf))
PY

# Pre-condition: parse + print-rpath shows libfoo.so.
before=$("$PATCHELF_BIN" print-rpath "$SCRATCH/input.elf")
if [ "$before" != "libfoo.so" ]; then
  echo "FAIL (setup): pre-op rpath was '$before', expected 'libfoo.so'" >&2
  exit 1
fi

before_phnum=$(LANG=C.UTF-8 od -An -j 56 -N 2 -tu2 --endian=little "$SCRATCH/input.elf" | tr -d ' ')
if [ "$before_phnum" != "1" ]; then
  echo "FAIL (setup): pre-op phnum was '$before_phnum', expected 1" >&2
  exit 1
fi

# Set new rpath (must succeed — validator-accepted output).
if ! "$PATCHELF_BIN" set-rpath /new/path "$SCRATCH/input.elf" >"$SCRATCH/setrpath.out" 2>&1; then
  echo "FAIL: set-rpath did not exit 0" >&2
  cat "$SCRATCH/setrpath.out" >&2
  exit 1
fi

# Output's phnum should be 2 (original 1 + 1 fresh PT_LOAD).
after_phnum=$(LANG=C.UTF-8 od -An -j 56 -N 2 -tu2 --endian=little "$SCRATCH/input.elf" | tr -d ' ')
if [ "$after_phnum" != "2" ]; then
  echo "FAIL: post-op phnum was '$after_phnum', expected 2 (fresh PT_LOAD)" >&2
  exit 1
fi

# Reparse must succeed.
if ! "$PATCHELF_BIN" parse "$SCRATCH/input.elf" >"$SCRATCH/parse.out" 2>&1; then
  echo "FAIL: post-op reparse failed" >&2
  cat "$SCRATCH/parse.out" >&2
  exit 1
fi

# rpath should resolve to the new value.
after=$("$PATCHELF_BIN" print-rpath "$SCRATCH/input.elf")
if [ "$after" != "/new/path" ]; then
  echo "FAIL: post-op rpath was '$after', expected '/new/path'" >&2
  exit 1
fi

echo "PASS: --set-rpath on BSS-heavy binary used the fresh-PT_LOAD path"
