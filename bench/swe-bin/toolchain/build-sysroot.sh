#!/usr/bin/env bash
# Build the riscv64 Linux musl sysroot used by every swe-bin task, without the C extension
# (-march=rv64imafd_zba_zbb -mabi=lp64d): nocompiler refuses RVC binaries (e_flags RVC).
#   musl 1.2.5 (libc.a, crt*.o), compiler-rt 15.0.7 builtins (libclang_rt.builtins.a, also
#   installed as libgcc.a), libunwind 15.0.7 (libunwind.a, for Rust's panic=unwind).
# Inputs: SWB (work dir, default /mnt/scratch/ec2-user/swe-bin), RUST_TC (rustup toolchain dir
# providing rust-lld and llvm-ar). Output: $SWB/tc/{bin,sysroot}.
set -euo pipefail
SWB=${SWB:-/mnt/scratch/ec2-user/swe-bin}
RUST_TC=${RUST_TC:-/mnt/scratch/ec2-user/rustup/toolchains/nightly-2026-11-01-x86_64-unknown-linux-gnu}
J=${J:-4}
SRC=$SWB/src; SR=$SWB/tc/sysroot; BIN=$SWB/tc/bin; B=$SWB/build
# nocompiler's own code-generation flags (crates/nocompiler/src/cc.rs), on a Linux target with F/D/A
MARCH="-march=rv64imafd_zba_zbb -mabi=lp64d -mcmodel=medany -mno-relax -fno-pic -fno-jump-tables -mllvm -disable-block-placement"
mkdir -p "$SRC" "$BIN" "$B"
cd "$SRC"
for u in https://musl.libc.org/releases/musl-1.2.5.tar.gz \
         https://github.com/llvm/llvm-project/releases/download/llvmorg-15.0.7/compiler-rt-15.0.7.src.tar.xz \
         https://github.com/llvm/llvm-project/releases/download/llvmorg-15.0.7/libunwind-15.0.7.src.tar.xz; do
  f=${u##*/}; [ -f "$f" ] || curl -sSLO "$u"; d=${f%.tar.*}; [ -d "$d" ] || tar xf "$f"
done
L=$RUST_TC/lib/rustlib/x86_64-unknown-linux-gnu/bin
ln -sf "$L/rust-lld" "$BIN/ld.lld"
for t in llvm-ar llvm-nm llvm-objcopy llvm-objdump llvm-strip; do ln -sf "$L/$t" "$BIN/$t"; done
ln -sf llvm-ar "$BIN/llvm-ranlib"; ln -sf llvm-ar "$BIN/ranlib"; ln -sf llvm-ar "$BIN/ar"
export PATH=$BIN:$PATH
CC="clang --target=riscv64-linux-musl $MARCH"

# musl
mkdir -p "$B/musl"; cd "$B/musl"
"$SRC/musl-1.2.5/configure" --target=riscv64-linux-musl --prefix="$SR" --disable-shared \
  CC="$CC" AR=llvm-ar RANLIB=llvm-ranlib CFLAGS="-O2" LIBCC=" " > cfg.log 2>&1
make -j"$J" > make.log 2>&1; make install > install.log 2>&1

# compiler-rt builtins: the generic C files plus lib/builtins/riscv
mkdir -p "$B/crt"; cd "$B/crt"; rm -f ./*.o
RT=$SRC/compiler-rt-15.0.7.src/lib/builtins
for f in "$RT"/*.c "$RT"/riscv/*.S "$RT"/riscv/*.c; do
  [ -e "$f" ] || continue
  case "${f##*/}" in
    # host or OS specific, or needing headers this sysroot does not have
    emutls.c|enable_execute_stack.c|clear_cache.c|eprintf.c|gcc_personality_v0.c|atomic*.c|os_version_check.c|trampoline_setup.c) continue;;
  esac
  o=$(basename "${f%.*}").o
  $CC -O2 -fPIC -fno-builtin -fvisibility=hidden --sysroot="$SR" -c "$f" -o "$o" 2>>errs.log || echo "skip $f" >> skipped.log
done
rm -f "$SR/lib/libclang_rt.builtins.a"; llvm-ar rcs "$SR/lib/libclang_rt.builtins.a" ./*.o
cp "$SR/lib/libclang_rt.builtins.a" "$SR/lib/libgcc.a"
# crtbegin/crtend (empty: musl's crt does the init/fini work); clang's driver asks for them
for x in crtbegin crtend crtbeginS crtendS crtbeginT; do : > e.c; $CC -c e.c -o "$SR/lib/$x.o"; done

# libunwind
mkdir -p "$B/unwind"; cd "$B/unwind"; rm -f ./*.o
U=$SRC/libunwind-15.0.7.src
for f in "$U"/src/*.c "$U"/src/*.cpp "$U"/src/*.S; do
  o=$(basename "$f").o
  case "$f" in *.cpp) X="clang++ --target=riscv64-linux-musl $MARCH -std=c++17 -fno-rtti -fno-exceptions -nostdinc++";; *) X="$CC";; esac
  $X -O2 -fPIC -funwind-tables -D_LIBUNWIND_IS_NATIVE_ONLY -D_LIBUNWIND_HAS_NO_THREADS=0 -DNDEBUG \
     --sysroot="$SR" -isystem "$SR/include" -I"$U/include" -c "$f" -o "$o"
done
rm -f "$SR/lib/libunwind.a"; llvm-ar rcs "$SR/lib/libunwind.a" ./*.o
echo "sysroot: $SR"; ls "$SR/lib"
# clang's driver links -lgcc -lgcc_eh for a static Linux target
cp "$SR/lib/libunwind.a" "$SR/lib/libgcc_eh.a"
# rv-cc / rv-c++: the C compiler every C task uses (flags recorded in each task's recipe)
for n in cc c++; do
  d=clang; [ $n = c++ ] && d=clang++
  # -static, except for a -shared link (jemalloc's build makes a .so that is never used):
  # that one links its objects only, -nostdlib (the sysroot has no shared libc)
  cat > "$BIN/rv-$n" <<EOS
#!/bin/sh
st=-static
for a in "\$@"; do [ "\$a" = -shared ] && st=-nostdlib; done
# the cc crate adds its own -march (rv64gc, from the target name): it would win over ours, so
# every -march, -mabi and -mcmodel of the caller is dropped
n=\$#
while [ \$n -gt 0 ]; do
  a=\$1; shift; n=\$((n-1))
  case "\$a" in -march=*|-mabi=*|-mcmodel=*) ;; *) set -- "\$@" "\$a";; esac
done
exec $d --target=riscv64-linux-musl $MARCH --sysroot=$SR -Qunused-arguments -fuse-ld=lld \$st -Wl,--emit-relocs "\$@"
EOS
  chmod +x "$BIN/rv-$n"
done
# riscv64-linux-musl-* names, for build systems that take a CROSS_COMPILE prefix
L=$RUST_TC/lib/rustlib/x86_64-unknown-linux-gnu/bin
ln -sf rv-cc "$BIN/riscv64-linux-musl-gcc"; ln -sf rv-cc "$BIN/riscv64-linux-musl-cc"
ln -sf rv-c++ "$BIN/riscv64-linux-musl-g++"
for t in ar nm objcopy objdump strip size; do ln -sf "$L/llvm-$t" "$BIN/riscv64-linux-musl-$t"; done
ln -sf "$L/llvm-ar" "$BIN/riscv64-linux-musl-ranlib"; ln -sf ld.lld "$BIN/riscv64-linux-musl-ld"
# sys/cdefs.h, which musl does not ship (berkeley-db in micropython includes it): the usual shim
mkdir -p "$SR/include/sys"
cat > "$SR/include/sys/cdefs.h" <<'EOH'
#ifndef _SYS_CDEFS_H
#define _SYS_CDEFS_H
#ifdef __cplusplus
#define __BEGIN_DECLS extern "C" {
#define __END_DECLS }
#else
#define __BEGIN_DECLS
#define __END_DECLS
#endif
#define __P(args) args
#define __PMT(args) args
#define __CONCAT(x, y) x##y
#define __STRING(x) #x
#define __THROW
#endif
EOH
# libswb_lfs64.a: the LFS64 names (stat64, lseek64, open64, ...) as tail calls to the plain
# functions. musl >= 1.2.4 has them only as macros in its headers, but std from 2022 and
# earlier links them by name. Generated from the headers' `#define X64 X`, for every X that
# libc.a defines as a function.
mkdir -p "$B/lfs64"; cd "$B/lfs64"
llvm-nm --defined-only "$SR/lib/libc.a" 2>/dev/null | awk '$2=="T"||$2=="W"{print $3}' | sort -u > defined.txt
grep -rhoE "^#define [a-z_0-9]+64(_r)? [a-z_0-9]+$" "$SRC/musl-1.2.5/include" | awk '{print $2, $3}' | sort -u |
  while read -r a b; do
    # a tail call, not `.set` (which cannot alias a symbol of another object)
    if grep -qx "$b" defined.txt; then printf '.globl %s\n.type %s, @function\n%s:\n  tail %s\n' "$a" "$a" "$a" "$b"; fi
  done > lfs64.s
$CC -c lfs64.s -o lfs64.o
rm -f "$SR/lib/libswb_lfs64.a"; llvm-ar rcs "$SR/lib/libswb_lfs64.a" lfs64.o
echo "lfs64 aliases: $(grep -c '^  tail' lfs64.s)"
