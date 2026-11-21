#!/usr/bin/env bash
# Build the examples into examples/build/ and check them against the profile.
#
# The committed ELF files under examples/elf/ are what the Lean proofs are
# about. This script rebuilds them and reports whether the build reproduces
# the committed bytes; a different clang may legitimately emit different code,
# in which case the proofs keep holding for the committed files and would
# need redoing for the new ones.
#
#   examples/build.sh            build, check, compare with examples/elf/
#   examples/build.sh --update   also replace examples/elf/ and the Lean images
#
# CLANG, LLD and NOCOMPILER override the tools.
set -euo pipefail
cd "$(dirname "$0")/.."
CLANG=${CLANG:-clang}
LLD=${LLD:-$(command -v ld.lld || command -v ld.lld-20 || echo ld.lld)}
NOCOMPILER=${NOCOMPILER:-target/release/nocompiler}
out=examples/build
mkdir -p "$out"
# The profile: RV64IM + Zba + Zbb, no C, statically linked, no relaxation
# (so calls stay auipc/jalr or jal as the compiler wrote them), no PIC.
cflags=(--target=riscv64-unknown-elf -march=rv64im_zba_zbb -mabi=lp64 -mcmodel=medany -mno-relax -O2
  -ffreestanding -nostdlib -fno-pic -fno-asynchronous-unwind-tables -fno-unwind-tables
  -fno-ident)
status=0
for src in examples/*.c; do
  name=$(basename "$src" .c)
  "$CLANG" "${cflags[@]}" -c "$src" -o "$out/$name.o"
  "$LLD" -static -e _start --build-id=none -z noseparate-code "$out/$name.o" -o "$out/$name.raw.elf"
  "$NOCOMPILER" annotate "$out/$name.raw.elf" -o "$out/$name.elf" >/dev/null
  "$NOCOMPILER" check "$out/$name.elf" | tail -1
  if [ "${1:-}" = --update ]; then
    mkdir -p examples/elf
    cp "$out/$name.elf" "examples/elf/$name.elf"
    mod=$(echo "$name" | sed -E 's/(^|_)([a-z])/\U\2/g')
    "$NOCOMPILER" export --lean-level-check "examples/elf/$name.elf" --namespace "Examples.$mod.Image" \
      -o "lean/Examples/$mod/Image.lean"
  elif ! cmp -s "$out/$name.elf" "examples/elf/$name.elf"; then
    echo "$name: the build differs from examples/elf/$name.elf ($("$CLANG" --version | head -1))"
    status=1
  fi
done
exit $status
