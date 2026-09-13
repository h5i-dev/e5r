#!/usr/bin/env bash
# Build the fixture corpus into fixtures/build/ (gitignored).
#
# This machine is aarch64, so native builds are AArch64 ELF executables with
# DWARF kept (ground truth for the G4 boundary gate) plus a stripped copy. x86
# fixtures are cross-compiled object files: clang needs no sysroot for -c, and
# llvm-objdump disassembles the result, which is enough for decoder parity.
set -euo pipefail
cd "$(dirname "$0")/.."

out=fixtures/build
mkdir -p "$out"
cc=${CC:-gcc}
xcc=${XCC:-clang}

for src in fixtures/src/*.c; do
  [ -e "$src" ] || continue
  base=$(basename "$src" .c)
  for opt in O0 O2; do
    "$cc" -g -"$opt" -fno-pie -no-pie -o "$out/${base}.a64.${opt}" "$src"
    cp "$out/${base}.a64.${opt}" "$out/${base}.a64.${opt}.stripped"
    strip "$out/${base}.a64.${opt}.stripped"
  done
done

# A patched pair: the same program with one string changed, and a second with
# two functions added. This is what the diff gate measures against.
if [ -e fixtures/src/hello.c ]; then
  # The patch changes code, not a string: a changed literal moves no
  # instruction, so a string edit would test nothing about the matcher.
  sed 's|acc += i;|acc += i * 2;|' fixtures/src/hello.c > "$out/hello-patched.c"
  sed -e 's|acc += i;|acc += i * 2;|' \
      -e 's|^int main(|int extra_helper(int a, int b) { return a * b + (a ^ b); }\nint another_one(int a) { return a << 3; }\n\nint main(|' \
    fixtures/src/hello.c > "$out/hello-grown.c"
  "$cc" -g -O2 -fno-pie -no-pie -o "$out/hello-patched.a64.O2" "$out/hello-patched.c"
  "$cc" -g -O2 -fno-pie -no-pie -o "$out/hello-grown.a64.O2" "$out/hello-grown.c"
  rm -f "$out/hello-patched.c" "$out/hello-grown.c"
fi

# Freestanding sources build for every target without a sysroot, so the same
# source yields comparable AArch64 and x86-64 objects.
for src in fixtures/portable/*.c; do
  [ -e "$src" ] || continue
  base=$(basename "$src" .c)
  # Several optimization levels, because each one emits a different corner of
  # the instruction set, and that is what the decoder gates are measured on.
  for opt in O0 O1 O2 O3 Os; do
    "$cc" -g -"$opt" -ffreestanding -c -o "$out/${base}.a64.${opt}.o" "$src"
    "$xcc" --target=x86_64-linux-gnu -g -"$opt" -ffreestanding -c \
      -o "$out/${base}.x64.${opt}.o" "$src"
  done
  # A COFF object, so the PE loader has real input on a machine with no
  # Windows linker.
  "$xcc" --target=x86_64-pc-windows-msvc -O2 -ffreestanding -c \
    -o "$out/${base}.coff.o" "$src" 2>/dev/null || true
  # One SSE4.2 build, to reach past the x86-64 baseline.
  "$xcc" --target=x86_64-linux-gnu -g -O2 -msse4.2 -ffreestanding -c \
    -o "$out/${base}.x64.sse42.o" "$src" 2>/dev/null || true
done

# x86-64 assembly fixtures, kept from the C++ project: they pin encodings.
for src in fixtures/asm/*.s; do
  [ -e "$src" ] || continue
  base=$(basename "$src" .s)
  "$xcc" --target=x86_64-linux-gnu -c -o "$out/asm-${base}.x64.o" "$src" 2>/dev/null \
    || echo "skip $src (does not assemble)" >&2
done

ls "$out"
