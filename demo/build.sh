#!/usr/bin/env bash
# Build each demo source twice (demo/README.md):
#   A, ordinary:  clang -O2 --target=riscv64-unknown-elf -march=rv64gc, default
#                 layout and options (compressed code, clang's block placement)
#   B, e5r:       e5r cc -O2 (the profile: RV64IM+Zba+Zbb, structured, checked)
# Both are freestanding and statically linked, as a program without libc must be.
# Writes demo/build/*.elf; with --update also replaces the committed demo/elf/.
set -euo pipefail
cd "$(dirname "$0")/.."
CLANG=${CLANG:-clang}
LLD=${LLD:-$(command -v ld.lld || command -v ld.lld-20)}
E5R=${E5R:-target/release/e5r}
out=demo/build
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
build_b() { local name=$1; shift; LLD=$LLD "$E5R" cc -O2 "$@" -o "$out/$name" >/dev/null 2>&1 || true; }
build_a sum.a.elf demo/src/sum.c
build_b sum.b.elf demo/src/sum.c
build_a cobs.a.elf demo/src/cobs.c demo/src/cobs_start.c
build_b cobs.b.elf demo/src/cobs.c demo/src/cobs_start.c
# Test drivers: not proved; they contain cobs_decode with the proved bytes
# (demo/test/cobs_test.py checks), and their own _start need not conform.
build_a cobs_test.a.elf demo/src/cobs.c demo/src/cobs_test_main.c
build_b cobs_test.b.elf demo/src/cobs.c demo/src/cobs_test_main.c
for e in sum.b cobs.b; do "$E5R" check "$out/$e.elf" | tail -1; done
for e in sum.a cobs.a; do
  echo "$out/$e.elf: $("$E5R" check "$out/$e.elf" 2>&1 | head -1 | sed 's/^e5r: //') (ordinary code)"
done
if [ "${1:-}" = --update ]; then
  cp "$out"/{sum,cobs}.{a,b}.elf demo/elf/
else
  for e in sum.a sum.b cobs.a cobs.b; do
    cmp -s "$out/$e.elf" "demo/elf/$e.elf" || echo "$e.elf: the build differs from demo/elf/ ($("$CLANG" --version | head -1))"
  done
fi
