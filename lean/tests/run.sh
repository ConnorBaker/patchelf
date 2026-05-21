#!/bin/sh -e
# Top-level test runner. Each file in tests/cases/*.sh is run; failures
# are collected and reported at the end.
#
# Environment variables:
#   PATCHELF_BIN   path to patchelf binary (default: ../.lake/build/bin/patchelf)
#   PATCHELF_C_BIN    path to reference C patchelf (default: search PATH)

cd "$(dirname "$0")"

: "${PATCHELF_BIN:=$(pwd)/../.lake/build/bin/patchelf}"
: "${PATCHELF_C_BIN:=$(command -v patchelf || echo /missing-patchelf)}"

export PATCHELF_BIN PATCHELF_C_BIN

echo "Lean binary: $PATCHELF_BIN"
echo "C binary   : $PATCHELF_C_BIN"

[ -x "$PATCHELF_BIN" ] || { echo "Lean binary not found or not executable" >&2; exit 2; }

if ! [ -x "$PATCHELF_C_BIN" ]; then
  echo "Warning: reference C patchelf not found. Golden-diff cases will be skipped." >&2
fi

rm -rf scratch && mkdir -p scratch

pass=0
fail=0
skip=0
for case_file in cases/*.sh; do
  [ -f "$case_file" ] || continue
  name="$(basename "$case_file" .sh)"
  printf "[%s]... " "$name"
  rc=0
  sh -e "$case_file" >scratch/"$name".log 2>&1 || rc=$?
  case $rc in
    0)
      echo "PASS"
      pass=$((pass + 1))
      ;;
    77)
      echo "SKIP"
      skip=$((skip + 1))
      ;;
    *)
      echo "FAIL (see scratch/$name.log)"
      fail=$((fail + 1))
      ;;
  esac
done

echo
echo "$pass passed, $fail failed, $skip skipped"
[ $fail -eq 0 ] || exit 1
