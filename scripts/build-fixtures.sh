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
  # Mach-O objects for both architectures. clang cross-compiles these without
  # a sysroot, which is the only Mach-O this machine can produce.
  "$xcc" --target=arm64-apple-macos11 -O2 -ffreestanding -c \
    -o "$out/${base}.macho.a64.o" "$src" 2>/dev/null || true
  "$xcc" --target=x86_64-apple-macos11 -O2 -ffreestanding -c \
    -o "$out/${base}.macho.x64.o" "$src" 2>/dev/null || true
  # A COFF object, so the PE loader has real input on a machine with no
  # Windows linker.
  "$xcc" --target=x86_64-pc-windows-msvc -O2 -ffreestanding -c \
    -o "$out/${base}.coff.o" "$src" 2>/dev/null || true
  # One SSE4.2 build, to reach past the x86-64 baseline.
  "$xcc" --target=x86_64-linux-gnu -g -O2 -msse4.2 -ffreestanding -c \
    -o "$out/${base}.x64.sse42.o" "$src" 2>/dev/null || true
done

# The lifter oracle: one program, two architectures, executed for real.
#
# The driver is generated from the case table so the test and the machine run
# the same calls. Each build is executed and its output recorded, which is what
# the lifter is then measured against. Recording at build time rather than test
# time means a machine without qemu can still run the gate.
lld=$(ls -d "$HOME"/.rustup/toolchains/*/lib/rustlib/*/bin/rust-lld 2>/dev/null | head -1)
if [ -n "$lld" ]; then
  mkdir -p "$out/ld"
  ln -sf "$lld" "$out/ld/ld.lld"
  python3 scripts/gen-driver.py fixtures/portable/cases.txt "$out/driver.c"
  cp fixtures/portable/wide.c "$out/wide.c"
  for opt in O0 O1 O2 O3 Os; do
    "$xcc" --target=x86_64-unknown-linux-gnu -B"$out/ld" -fuse-ld=lld -"$opt" \
      -fno-inline -ffreestanding -fno-stack-protector -fno-builtin -nostdlib \
      -static -o "$out/driver.x64.$opt" "$out/driver.c" 2>/dev/null || true
    # clang for both: gcc's freestanding entry needs a runtime this has not.
    "$xcc" -"$opt" -fno-inline -ffreestanding -fno-stack-protector -fno-builtin \
      -nostdlib -static -o "$out/driver.a64.$opt" "$out/driver.c" 2>/dev/null || true
    if [ -x "$out/driver.a64.$opt" ]; then
      "$out/driver.a64.$opt" > "$out/driver.a64.$opt.out" || true
    fi
    if [ -x "$out/driver.x64.$opt" ] && command -v qemu-x86_64 > /dev/null; then
      qemu-x86_64 "$out/driver.x64.$opt" > "$out/driver.x64.$opt.out" || true
    fi
  done
  # The two architectures computing the same answers is the harness checking
  # itself before anything is measured against it.
  for opt in O0 O1 O2 O3 Os; do
    if [ -s "$out/driver.a64.$opt.out" ] && [ -s "$out/driver.x64.$opt.out" ]; then
      cmp -s "$out/driver.a64.$opt.out" "$out/driver.x64.$opt.out" \
        || echo "warning: driver.$opt disagrees across architectures" >&2
    fi
  done
fi

# C++ fixtures: virtual dispatch, inheritance and RTTI, which is what vtable
# recovery has to find. Freestanding, so no C++ runtime is needed to build them.
cxx=${CXX:-g++}
for src in fixtures/cpp/*.cpp; do
  [ -e "$src" ] || continue
  base=$(basename "$src" .cpp)
  case "$base" in start) continue ;; esac
  for opt in O0 O2; do
    "$cxx" -g -"$opt" -fno-exceptions -c -o "$out/${base}.a64.${opt}.cpp.o" "$src" \
      2>/dev/null || true
    # And linked, so the vtable scan has a binary where every slot resolves.
    # Without RTTI: the type information refers to the ABI runtime's own
    # tables, which a freestanding link has nothing to resolve against.
    # `-ffreestanding` as well: without it the optimizer rewrites a counting
    # loop into a call to `strlen`, which there is nothing here to link.
    "$cxx" -g -"$opt" -fno-exceptions -fno-rtti -ffreestanding -fno-pie -no-pie \
      -nostdlib -static \
      -o "$out/${base}.a64.${opt}.cpp" "$src" fixtures/cpp/start.cpp 2>/dev/null || true
    if [ -x "$out/${base}.a64.${opt}.cpp" ]; then
      "$out/${base}.a64.${opt}.cpp" > "$out/${base}.a64.${opt}.cpp.out" || true
    fi
  done
done

# x86-64 assembly fixtures, kept from the C++ project: they pin encodings.
for src in fixtures/asm/*.s; do
  [ -e "$src" ] || continue
  base=$(basename "$src" .s)
  "$xcc" --target=x86_64-linux-gnu -c -o "$out/asm-${base}.x64.o" "$src" 2>/dev/null \
    || echo "skip $src (does not assemble)" >&2
done

# Runtime metadata fixtures: a language's own runtime tables, which is the only
# thing a stripped binary of that language still says about itself.
#
# The Go pair is a real oracle: the stripped copy has no symbols at all, so
# every name the pclntab reader recovers is checked against the unstripped
# copy's symbol table.
if command -v go > /dev/null; then
  mkdir -p "$out/gosrc"
  cat > "$out/gosrc/go.mod" <<'EOF'
module r12efixture

go 1.16
EOF
  cat > "$out/gosrc/main.go" <<'EOF'
package main

import "os"

func alpha(x int) int { return x*3 + 1 }

func beta(x int) int { return alpha(x) - 7 }

func main() {
	if beta(len(os.Args)) == 0 {
		os.Exit(1)
	}
}
EOF
  (cd "$out/gosrc" && GOFLAGS=-trimpath go build -o ../hello.go . 2>/dev/null) || true
  if [ -x "$out/hello.go" ]; then
    cp "$out/hello.go" "$out/hello.go.stripped"
    strip "$out/hello.go.stripped"
  fi
  rm -rf "$out/gosrc"
fi

# Rust panic locations. Compiled from inside the output directory so the file
# name recorded in the Location records is exactly "panicky.rs", which is what
# the test compares against.
if command -v rustc > /dev/null; then
  cat > "$out/panicky.rs" <<'EOF'
fn pick(v: &[u32], i: usize) -> u32 {
    v[i]
}

fn main() {
    let n = std::env::args().count();
    println!("{}", pick(&[1, 2, 3], n * 7));
    assert!(n < 100, "too many arguments");
}
EOF
  (cd "$out" && rustc -O -C panic=abort -o panicky panicky.rs 2>/dev/null) || true
fi

# An Objective-C object, for the class and method lists. It is relocatable, so
# every pointer in it is still zero: it proves the reader survives a file whose
# metadata sections are present and unresolved, not that it reads a class. A
# linked Mach-O would prove that, and there is no macOS linker here.
cat > "$out/greeter.m" <<'EOF'
@interface Greeter { Class isa; }
- (int)count;
+ (int)make;
@end

@implementation Greeter
- (int)count { return 7; }
+ (int)make { return 1; }
@end
EOF
"$xcc" --target=arm64-apple-macos11 -O1 -Wno-objc-root-class -c \
  -o "$out/greeter.macho.a64.o" "$out/greeter.m" 2>/dev/null || true


# ARM fixtures, A32 and T32 from the same sources: the two instruction sets
# compile the same C into different encodings, which is what the ARM decoder
# gate is measured on. Freestanding again, so no ARM sysroot is needed.
for src in fixtures/portable/*.c; do
  [ -e "$src" ] || continue
  base=$(basename "$src" .c)
  for opt in O0 O1 O2; do
    "$xcc" --target=arm-linux-gnueabihf -"$opt" -ffreestanding -c \
      -o "$out/${base}.arm.${opt}.o" "$src" 2>/dev/null || true
    "$xcc" --target=thumbv7-linux-gnueabihf -mthumb -"$opt" -ffreestanding -c \
      -o "$out/${base}.thumb.${opt}.o" "$src" 2>/dev/null || true
  done
done

ls "$out"
