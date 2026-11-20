#!/usr/bin/env bash
# Build each demo source twice (examples/demo/README.md):
#   A, ordinary:  clang -O2 --target=riscv64-unknown-elf -march=rv64gc, default
#                 layout and options (compressed code, clang's block placement)
#   B, nocompiler:       nocompiler cc -O2 (the profile: RV64IM+Zba+Zbb, structured, checked)
# Both are freestanding and statically linked, as a program without libc must be.
# Writes examples/demo/build/*.elf; with --update also replaces the committed examples/demo/elf/.
set -euo pipefail
cd "$(dirname "$0")/../.."
CLANG=${CLANG:-clang}
LLD=${LLD:-$(command -v ld.lld || command -v ld.lld-20)}
NOCOMPILER=${NOCOMPILER:-target/release/nocompiler}
out=examples/demo/build
mkdir -p "$out"
acflags=(--target=riscv64-unknown-elf -march=rv64gc -O2 -ffreestanding -nostdlib)
build_a() {  # output, sources...
  local name=$1; shift; local objs=()
  for src in "$@"; do
    "$CLANG" "${acflags[@]}" -c "$src" -o "$out/$(basename "$src" .c).a.o"
    objs+=("$out/$(basename "$src" .c).a.o")
  done
  "$LLD" -static -e _start "${objs[@]}" -o "$out/$name"
}
build_b() { local name=$1; shift; LLD=$LLD "$NOCOMPILER" cc -O2 "$@" -o "$out/$name" >/dev/null 2>&1 || true; }
build_a sum.a.elf examples/demo/src/sum.c
build_b sum.b.elf examples/demo/src/sum.c
build_a cobs.a.elf examples/demo/src/cobs.c examples/demo/src/cobs_start.c
build_b cobs.b.elf examples/demo/src/cobs.c examples/demo/src/cobs_start.c
# Test drivers: not proved; they contain cobs_decode with the proved bytes
# (examples/demo/test/cobs_test.py checks), and their own _start need not conform.
build_a cobs_test.a.elf examples/demo/src/cobs.c examples/demo/src/cobs_test_main.c
build_b cobs_test.b.elf examples/demo/src/cobs.c examples/demo/src/cobs_test_main.c
for e in sum.b cobs.b; do "$NOCOMPILER" check "$out/$e.elf" | tail -1; done
for e in sum.a cobs.a; do
  echo "$out/$e.elf: $("$NOCOMPILER" check "$out/$e.elf" 2>&1 | head -1 | sed 's/^nocompiler: //') (ordinary code)"
done
if [ "${1:-}" = --update ]; then
  cp "$out"/{sum,cobs}.{a,b}.elf examples/demo/elf/
else
  for e in sum.a sum.b cobs.a cobs.b; do
    cmp -s "$out/$e.elf" "examples/demo/elf/$e.elf" || echo "$e.elf: the build differs from examples/demo/elf/ ($("$CLANG" --version | head -1))"
  done
fi
