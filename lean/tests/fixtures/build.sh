#!/bin/sh -e
# Build test fixtures.
#
# Fixtures are small Linux ELF binaries. Darwin hosts can't execute them
# but can still parse/rewrite them, which is all the test harness needs.
#
# Outputs go into this directory as plain files (no extension).

cd "$(dirname "$0")"

if ! [ -f hello.c ]; then
  cat >hello.c <<'EOF'
#include <stdio.h>
int main(void) { puts("hello"); return 0; }
EOF
fi

if command -v x86_64-linux-gcc >/dev/null; then
  x86_64-linux-gcc -o hello hello.c
elif command -v x86_64-unknown-linux-gnu-gcc >/dev/null; then
  x86_64-unknown-linux-gnu-gcc -o hello hello.c
else
  echo "No Linux-targeting cross-compiler found on PATH."
  echo "Pre-built fixtures can be committed to tests/fixtures/ instead."
  exit 1
fi

echo "fixtures built:"
ls -la hello
