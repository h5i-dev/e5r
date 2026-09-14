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

# Ghidra's decompiler datatests, ported. Each source is one theme and links to
# its own static freestanding executable, because the shapes these pin need a
# linked image: a jump table's entries and a reference to a global are both
# relocations until the linker resolves them, and a relocatable object shows the
# decompiler neither. `-fno-pie` for the same reason, so a global is a plain
# address rather than a load from the GOT.
#
# Two optimization levels: a datatest is written against one compiler's output,
# and the only honest substitute for that is checking the property at more than
# one, since which of the two shows a given shape differs case by case.
if [ -d fixtures/datatests ]; then
  for src in fixtures/datatests/*.c; do
    [ -e "$src" ] || continue
    base=$(basename "$src" .c)
    case "$base" in support) continue ;; esac
    for opt in O1 O2; do
      "$xcc" -"$opt" -ffreestanding -fno-stack-protector -fno-builtin -fno-pie \
        -nostdlib -static -Ifixtures/datatests \
        -o "$out/dt-${base}.a64.${opt}" "$src" fixtures/datatests/support.c \
        2>/dev/null || true
      if [ -n "${lld:-}" ]; then
        "$xcc" --target=x86_64-unknown-linux-gnu -B"$out/ld" -fuse-ld=lld -"$opt" \
          -ffreestanding -fno-stack-protector -fno-builtin -fno-pie -nostdlib \
          -static -Ifixtures/datatests \
          -o "$out/dt-${base}.x64.${opt}" "$src" fixtures/datatests/support.c \
          2>/dev/null || true
      fi
    done
  done
fi

# An `ar` archive, for the archive reader. Built from objects that are already
# here, with one deliberately long member name so the GNU `//` long-name table
# is exercised rather than only the sixteen-byte name field. `ar t` and `nm -s`
# are the oracle the tests compare against, so the archive has to be a real one.
if command -v ar >/dev/null 2>&1; then
  members=""
  for o in shapes.a64.O0.o shapes.a64.O1.o shapes.a64.O2.o; do
    if [ -e "$out/$o" ]; then
      members="$members $o"
    fi
  done
  if [ -n "$members" ]; then
    first=${members# }
    first=${first%% *}
    long=a-member-name-far-longer-than-sixteen-bytes.o
    cp "$out/$first" "$out/$long"
    rm -f "$out/libshapes.a" "$out/libshapes-thin.a"
    # shellcheck disable=SC2086
    (cd "$out" && ar rcs libshapes.a $members "$long") || true
    # A thin archive: the members stay on disk and only their names are stored,
    # which is a different name encoding and a different member walk.
    # shellcheck disable=SC2086
    (cd "$out" && ar rcsT libshapes-thin.a $members) || true
  fi
fi

ls "$out"

# Windows images, for the PE loader's Windows-specific directories: the TLS
# callback array, .pdata/.xdata unwind data, the SEH scope table, base
# relocations and the load config's control-flow-guard function table.
#
# There is no Windows toolchain on this machine, but there does not need to be:
# clang cross-compiles COFF objects without a sysroot and rust-lld, which is
# already unpacked next to the Rust toolchain, is lld-link under another name.
# The image links against no CRT at all, so the two pieces the CRT would
# normally supply are written out here: `_tls_used`, the IMAGE_TLS_DIRECTORY the
# linker points the TLS directory at, and `__C_specific_handler`, the SEH
# dispatcher whose address UNWIND_INFO records.
#
# `-fasynchronous-unwind-tables` is what makes clang emit .pdata for every
# function rather than only for the one with a handler; without it a C image
# has a single runtime function and proves nothing.
if command -v "$xcc" >/dev/null 2>&1 && [ -n "${lld:-}" ]; then
  cat > "$out/win.c" <<'WINC'
typedef unsigned long long u64;
typedef unsigned long u32;

int g_counter;
int g_tls_index;
char tls_block[64];

int callee(int x);

__attribute__((noinline)) int worker(int x) {
    int a[8];
    for (int i = 0; i < 8; i++) a[i] = x + i;
    g_counter += a[x & 7];
    return callee(a[0]) + a[7];
}

__attribute__((noinline)) int callee(int x) { return x * 3 + g_counter; }

/* __try/__except is what puts a scope table in the language-specific handler
   data that follows UNWIND_INFO. */
__attribute__((noinline)) int guarded(int x) {
    int r = 0;
    __try {
        r = worker(x);
        if (r == 0) r = *(volatile int *)0;
    } __except (1) {
        r = -1;
    }
    return r;
}

static void __stdcall tls_callback_one(void *h, u32 reason, void *res) {
    (void)h; (void)res;
    g_counter += (int)reason + 1;
}

static void __stdcall tls_callback_two(void *h, u32 reason, void *res) {
    (void)h; (void)res;
    g_counter += (int)reason + 2;
}

typedef void (__stdcall *tls_cb_t)(void *, u32, void *);

/* The null-terminated array the loader walks before the entry point runs. */
const tls_cb_t tls_callbacks[] = { tls_callback_one, tls_callback_two, 0 };

struct tls_directory64 {
    u64 StartAddressOfRawData;
    u64 EndAddressOfRawData;
    u64 AddressOfIndex;
    u64 AddressOfCallBacks;
    u32 SizeOfZeroFill;
    u32 Characteristics;
};

/* The linker finds this symbol by name and points the TLS directory at it. */
const struct tls_directory64 _tls_used = {
    (u64)(void *)&tls_block[0],
    (u64)(void *)&tls_block[64],
    (u64)(void *)&g_tls_index,
    (u64)(void *)&tls_callbacks[0],
    0,
    0,
};

/* A stand-in for the CRT's SEH dispatcher. */
long __C_specific_handler(void *rec, void *frame, void *ctx, void *disp) {
    (void)rec; (void)frame; (void)ctx; (void)disp;
    return 1;
}

/* A frame too large for the four-bit UWOP_ALLOC_SMALL form. */
__attribute__((noinline)) int big_frame(int x) {
    volatile int a[600];
    for (int i = 0; i < 600; i++) a[i] = x + i;
    return a[x % 600] + callee(a[0]);
}

/* Enough live values across calls to force callee-saved pushes. */
__attribute__((noinline)) int many_saves(int a, int b, int c, int d, int e, int f) {
    int r = callee(a) + callee(b);
    r += callee(c) + callee(d);
    r += callee(e) + callee(f);
    return r + a + b + c + d + e + f;
}

/* Floating point, which on win64 means UWOP_SAVE_XMM128. */
__attribute__((noinline)) double fp_saves(double a, double b, double c) {
    double r = a * b;
    g_counter += (int)(r + c);
    r += (double)callee(g_counter);
    return r * c + a - b;
}

__attribute__((noinline)) int tail(int x) { return x ^ 0x5a5a; }

int _fltused = 0x9875;

int mainCRTStartup(void) {
    int r = guarded(g_counter);
    r += big_frame(r) + many_saves(r, 1, 2, 3, 4, 5);
    r += (int)fp_saves((double)r, 2.0, 3.0);
    return r + tail(r);
}
WINC
  cat > "$out/win-loadcfg.c" <<'LCC'
typedef unsigned long long u64;
typedef unsigned long u32;
typedef unsigned short u16;

/* IMAGE_LOAD_CONFIG_DIRECTORY64 through the long-jump table. The linker
   recognizes it by name and fills the guard tables in when /guard:cf is on. */
struct load_config64 {
    u32 Size; u32 TimeDateStamp; u16 MajorVersion; u16 MinorVersion;
    u32 GlobalFlagsClear; u32 GlobalFlagsSet; u32 CriticalSectionDefaultTimeout;
    u64 DeCommitFreeBlockThreshold; u64 DeCommitTotalFreeThreshold;
    u64 LockPrefixTable; u64 MaximumAllocationSize; u64 VirtualMemoryThreshold;
    u64 ProcessAffinityMask; u32 ProcessHeapFlags; u16 CSDVersion; u16 DependentLoadFlags;
    u64 EditList; u64 SecurityCookie; u64 SEHandlerTable; u64 SEHandlerCount;
    u64 GuardCFCheckFunctionPointer; u64 GuardCFDispatchFunctionPointer;
    u64 GuardCFFunctionTable; u64 GuardCFFunctionCount; u32 GuardFlags;
    u32 CodeIntegrity0; u64 CodeIntegrity1; u32 CodeIntegrity2; u32 pad;
    u64 GuardAddressTakenIatEntryTable; u64 GuardAddressTakenIatEntryCount;
    u64 GuardLongJumpTargetTable; u64 GuardLongJumpTargetCount;
};

u64 __security_cookie = 0x2b992ddfa232ULL;

/* Synthesized by the linker under /guard:cf. */
extern u64 __guard_fids_table[];
extern u64 __guard_fids_count;
extern u64 __guard_iat_table[];
extern u64 __guard_iat_count;
extern u64 __guard_longjmp_table[];
extern u64 __guard_longjmp_count;
/* Normally the CRT's; defined here because there is no CRT. */
void (*__guard_check_icall_fptr)(void);
void (*__guard_dispatch_icall_fptr)(void);

const struct load_config64 _load_config_used = {
  sizeof(struct load_config64), 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  (u64)(void*)&__security_cookie, 0, 0,
  (u64)(void*)&__guard_check_icall_fptr, (u64)(void*)&__guard_dispatch_icall_fptr,
  (u64)(void*)&__guard_fids_table[0], (u64)(void*)&__guard_fids_count,
  0, 0,0,0,0,
  (u64)(void*)&__guard_iat_table[0], (u64)(void*)&__guard_iat_count,
  (u64)(void*)&__guard_longjmp_table[0], (u64)(void*)&__guard_longjmp_count };
LCC
  for opt in O0 O2; do
    for t in "x64:x86_64-pc-windows-msvc:x64" "a64:aarch64-pc-windows-msvc:arm64"; do
      tag=${t%%:*}; rest=${t#*:}; triple=${rest%%:*}; machine=${rest##*:}
      "$xcc" --target="$triple" -"$opt" -fasynchronous-unwind-tables \
        -ffreestanding -c -o "$out/win.$tag.$opt.obj" "$out/win.c" 2>/dev/null || continue
      "$xcc" --target="$triple" -"$opt" -ffreestanding -c \
        -o "$out/win-loadcfg.$tag.$opt.obj" "$out/win-loadcfg.c" 2>/dev/null || continue
      # /guard:cf makes the linker build the CFG function table, which is
      # another list of real entry points. The GuardFlags warning is expected:
      # setting that field needs an absolute symbol a C initializer cannot name.
      "$lld" -flavor link /machine:"$machine" /nodefaultlib /entry:mainCRTStartup \
        /subsystem:console /guard:cf /out:"$out/win.$tag.$opt.exe" \
        "$out/win.$tag.$opt.obj" "$out/win-loadcfg.$tag.$opt.obj" 2>/dev/null || true
    done
  done
  rm -f "$out"/win.*.obj "$out"/win-loadcfg.*.obj
fi

# i386 objects, for the 32-bit x86 decoder gate. clang cross-compiles these
# without a sysroot the same way it does x86-64, and the interesting part is
# that a 32-bit compiler reaches for encodings long mode never emits: the
# one-byte inc and dec, the stack-relative addressing without a REX prefix, and
# x87 wherever the ABI returns a floating point value on the stack.
for src in fixtures/portable/*.c; do
  [ -e "$src" ] || continue
  base=$(basename "$src" .c)
  for opt in O0 O1 O2 O3 Os; do
    "$xcc" --target=i386-linux-gnu -g -"$opt" -ffreestanding -c \
      -o "$out/${base}.x32.${opt}.o" "$src" 2>/dev/null || true
  done
  # One build without SSE, so the floating point goes through the x87 stack
  # rather than through xmm registers.
  "$xcc" --target=i386-linux-gnu -g -O2 -mno-sse -mfpmath=387 -ffreestanding -c \
    -o "$out/${base}.x32.x87.o" "$src" 2>/dev/null || true
done

# The x86 assembly fixtures assembled for 32-bit as well, where they assemble.
for src in fixtures/asm/*.s; do
  [ -e "$src" ] || continue
  base=$(basename "$src" .s)
  "$xcc" --target=i386-linux-gnu -c -o "$out/asm-${base}.x32.o" "$src" 2>/dev/null || true
done

# Calls whose argument bounds are known by construction, for the dataflow query
# gate. Linked and static for both architectures at two optimization levels:
# the question is about a call site, and a relocatable object has none of the
# call targets resolved. `-fno-builtin` so the file's own `memcpy` is what the
# calls reach, and `-fno-pie` so the address of a global is an address.
for src in fixtures/dataflow/*.c; do
  [ -e "$src" ] || continue
  base=$(basename "$src" .c)
  for opt in O0 O2; do
    "$xcc" -"$opt" -ffreestanding -fno-stack-protector -fno-builtin -fno-pie \
      -nostdlib -static -o "$out/df-${base}.a64.${opt}" "$src" 2>/dev/null || true
    if [ -n "${lld:-}" ]; then
      "$xcc" --target=x86_64-unknown-linux-gnu -B"$out/ld" -fuse-ld=lld -"$opt" \
        -ffreestanding -fno-stack-protector -fno-builtin -fno-pie -nostdlib \
        -static -o "$out/df-${base}.x64.${opt}" "$src" 2>/dev/null || true
    fi
  done
done

# DWARF 4, which is the reader's other half. GCC 13 defaults to DWARF 5, and
# the two versions keep ranges and location lists in different sections with
# different encodings: `.debug_ranges` and `.debug_loc` rather than
# `.debug_rnglists` and `.debug_loclists`, addresses in pairs rather than
# behind entry kinds, and `DW_TAG_GNU_call_site` rather than `DW_TAG_call_site`.
# Without a fixture at -gdwarf-4 none of that path is measured against readelf.
for src in fixtures/portable/*.c; do
  [ -e "$src" ] || continue
  base=$(basename "$src" .c)
  "$cc" -gdwarf-4 -O2 -ffreestanding -c -o "$out/${base}.a64.dwarf4.o" "$src" \
    2>/dev/null || true
done
if [ -e fixtures/src/hello.c ]; then
  "$cc" -gdwarf-4 -O2 -fno-pie -no-pie -o "$out/hello.a64.dwarf4" fixtures/src/hello.c \
    2>/dev/null || true
fi

# i386 relocations, for the M1 relocation gate. Two memory models, because the
# relocation types barely overlap: -fno-pic emits R_386_32 and R_386_PC32,
# -fpic emits the whole GOT family (R_386_GOTPC, R_386_GOTOFF, R_386_GOT32X)
# plus R_386_PLT32. Relocatable objects only: the binutils here is built for
# aarch64 alone and there is no lld, so nothing on this machine can link an
# i386 image. The dynamic case with a real PLT is synthesized inside
# crates/r12e-format/tests/ instead.
cat > "$out/relocs32.c" <<'EOF'
/* One call that stays inside the file, one that leaves it, a reference to a
   local datum, to a local string and to an external datum, and a function
   pointer in .data. noinline so the intra-file call survives -O2, which is the
   relocation the call graph is actually about. */
extern int outside(int);
extern int outside_data;
int glob = 5;
static int stat_var = 9;
static const char msg[] = "relocated";
__attribute__((noinline)) int leaf(int x) { return x + stat_var; }
const char *name(void) { return msg; }
int caller(int x) { return leaf(x) + glob + outside(x) + outside_data; }
int (*fp)(int) = leaf;
int tail(int x) { return outside(x + 1); }
EOF
for opt in O0 O2; do
  "$xcc" --target=i386-linux-gnu -g -"$opt" -fno-pic -ffreestanding -c \
    -o "$out/relocs32.nopic.${opt}.o" "$out/relocs32.c" 2>/dev/null || true
  "$xcc" --target=i386-linux-gnu -g -"$opt" -fpic -ffreestanding -c \
    -o "$out/relocs32.pic.${opt}.o" "$out/relocs32.c" 2>/dev/null || true
done
rm -f "$out/relocs32.c"

# The C++ hierarchy fixture, built twice over: once with type information and
# once with -fno-rtti, so what RTTI adds and what its absence costs are
# measured rather than assumed. Both architectures at two optimization levels.
# The link is freestanding and static: the fixture defines the ABI's own
# type-info class vtable symbols itself, which is the only thing a -nostdlib
# link is missing when RTTI is on.
xcxx=${XCXX:-clang++}
if [ -e fixtures/cpp/hierarchy.cpp ]; then
  for opt in O0 O2; do
    for rtti in rtti nortti; do
      flag=""
      [ "$rtti" = nortti ] && flag="-fno-rtti"
      "$cxx" -g -"$opt" $flag -fno-exceptions -ffreestanding -fno-pie -no-pie \
        -nostdlib -static -o "$out/cpp-hierarchy.a64.${opt}.${rtti}" \
        fixtures/cpp/hierarchy.cpp fixtures/cpp/start.cpp 2>/dev/null || true
      if [ -n "${lld:-}" ]; then
        "$xcxx" --target=x86_64-unknown-linux-gnu -B"$out/ld" -fuse-ld=lld \
          -g -"$opt" $flag -fno-exceptions -ffreestanding -nostdlib -static \
          -o "$out/cpp-hierarchy.x64.${opt}.${rtti}" \
          fixtures/cpp/hierarchy.cpp fixtures/cpp/start.cpp 2>/dev/null || true
      fi
    done
    # Stripped, so the reader is measured with no symbols to lean on: the
    # degradation from proven to inferred is the point of the pair.
    for rtti in rtti nortti; do
      if [ -e "$out/cpp-hierarchy.a64.${opt}.${rtti}" ]; then
        cp "$out/cpp-hierarchy.a64.${opt}.${rtti}" \
           "$out/cpp-hierarchy.a64.${opt}.${rtti}.stripped"
        strip "$out/cpp-hierarchy.a64.${opt}.${rtti}.stripped"
        "$out/cpp-hierarchy.a64.${opt}.${rtti}" \
          > "$out/cpp-hierarchy.a64.${opt}.${rtti}.out" || true
      fi
    done
  done
fi

# The same hierarchy in the Microsoft C++ ABI, which writes its type
# information down in a different shape: a complete object locator before each
# vftable, naming a type descriptor and a class hierarchy descriptor, all of it
# in relative virtual addresses. clang targets that ABI without a Windows SDK
# because the fixture is freestanding, and lld links a PE. `/opt:noref` keeps
# the type information a linker would otherwise drop as unreferenced, which is
# what a real image keeps too because the runtime reaches it through the
# tables. Both machines, because a relative address is read the same way on
# each and the claim is worth nothing if only one was tried.
if [ -e fixtures/cpp/hierarchy.cpp ] && [ -n "${lld:-}" ]; then
  for opt in O0 O2; do
    for t in "x64:x86_64-pc-windows-msvc:x64" "a64:aarch64-pc-windows-msvc:arm64"; do
      tag=${t%%:*}; rest=${t#*:}; triple=${rest%%:*}; machine=${rest##*:}
      for rtti in rtti nortti; do
        flag="-frtti"
        [ "$rtti" = nortti ] && flag="-fno-rtti"
        obj="$out/cpp-hierarchy.win-$tag.$opt.$rtti.obj"
        "$xcxx" --target="$triple" -"$opt" -ffreestanding -fno-exceptions \
          $flag -c -o "$obj" fixtures/cpp/hierarchy.cpp 2>/dev/null || continue
        "$lld" -flavor link /machine:"$machine" /nodefaultlib /opt:noref \
          /entry:mainCRTStartup /subsystem:console \
          /out:"$out/cpp-hierarchy.win-$tag.$opt.$rtti.exe" "$obj" 2>/dev/null || true
      done
    done
  done
  rm -f "$out"/cpp-hierarchy.win-*.obj
fi

# Windows program databases, which this machine can produce after all.
#
# The earlier note that there is no Windows toolchain here was about a *linker
# and a CRT*, not about debug information: clang emits CodeView with
# `-gcodeview`, and rust-lld under its link flavour writes the .pdb when it is
# given /debug. So the PDB reader is measured against databases a real producer
# wrote rather than only against ones the test synthesized, and llvm-pdbutil
# dumps the same files as an external oracle.
#
# The source is written here rather than under fixtures/ because it exists only
# to make a producer emit one of everything the reader claims to read: a struct
# with a bitfield and a function pointer, a union, an enum, an array, globals
# with internal and external linkage, and a static helper called from three
# places so that -O2 inlines it and the producer emits S_INLINESITE. -O0 keeps
# the locals on the stack (S_DEFRANGE_FRAMEPOINTER_REL) and -O2 puts them in
# registers (S_DEFRANGE_REGISTER), which are different code paths in the
# reader. `_fltused` is what the CRT would normally supply for the float.
if command -v "$xcc" >/dev/null 2>&1 && [ -n "${lld:-}" ]; then
  cat > "$out/pdb.c" <<'PDBC'
int _fltused = 0;

enum Color { RED = 0, GREEN = 1, BLUE = 7 };

struct Point { int x; int y; float w; };

union Word { unsigned u; float f; unsigned char b[4]; };

struct Node {
  struct Point at;
  enum Color color;
  unsigned flags : 3;
  unsigned kind : 5;
  struct Node *next;
  int (*compare)(struct Point *, struct Point *);
};

int global_counter = 7;
static struct Point origin = {0, 0, 0.0f};
struct Node the_head;

static int scale(int a, int b) { int t = a * b; return t + 1; }

int compare_points(struct Point *a, struct Point *b) {
  int dx = a->x - b->x;
  int dy = a->y - b->y;
  return scale(dx, 3) + scale(dy, 5);
}

int walk(struct Node *n, int k) {
  int total = 0;
  while (n) { total += scale(n->at.x, k) + (int)n->color; n = n->next; }
  return total;
}

int mainCRTStartup(void) {
  struct Point p = {1, 2, 3.0f};
  union Word w;
  w.u = 0x41424344;
  the_head.at = p;
  the_head.color = BLUE;
  the_head.compare = compare_points;
  return compare_points(&p, &origin) + walk(&the_head, 2) + (int)w.f + global_counter;
}
PDBC
  for opt in O0 O2; do
    for t in "x64:x86_64-pc-windows-msvc:x64" "a64:aarch64-pc-windows-msvc:arm64"; do
      tag=${t%%:*}; rest=${t#*:}; triple=${rest%%:*}; machine=${rest##*:}
      "$xcc" --target="$triple" -g -gcodeview -"$opt" -ffreestanding -c \
        -o "$out/pdb.$tag.$opt.obj" "$out/pdb.c" 2>/dev/null || continue
      # /debug is what makes the linker write the database at all, and the
      # image's debug directory then points at the path /pdb names.
      "$lld" -flavor link /machine:"$machine" /nodefaultlib /entry:mainCRTStartup \
        /subsystem:console /debug /pdb:"$out/pdb.$tag.$opt.pdb" \
        /out:"$out/pdb.$tag.$opt.exe" "$out/pdb.$tag.$opt.obj" 2>/dev/null || true
    done
  done
  rm -f "$out"/pdb.*.obj "$out/pdb.c"
fi

# Instruction-granularity diff: the same program four times over, with one
# source line different each time, so the expected edit list is exact rather
# than "some difference was found".
#
# -O0 and gcc on purpose. The question this pair asks is whether the alignment
# survives the shift an edit causes; an optimizer rewriting the function would
# make the expected list a property of the compiler's scheduling instead. The
# function under test carries no global and no string literal either, because a
# data address the linker moves would surface as a retargeted operand and make
# the list depend on section layout.
cat > "$out/insndiff.c" <<'IDC'
__attribute__((noinline)) static int mix(int n) {
    int acc = 1;
    for (int i = 0; i < n; i++) {
        acc = acc + i;
        acc = acc ^ (acc >> 3);
        acc = acc - 7;
        acc = acc * 3;
        /* INSERT */
    }
    return acc;
}

__attribute__((noinline)) static int other(int n) { return n * 5 + 1; }

volatile int keep;

void _start(void) {
    for (;;) keep = mix(keep) + other(keep);
}
IDC
# One operator changed, so one instruction is replaced and nothing moves.
sed 's|acc = acc + i;|acc = acc - i;|' "$out/insndiff.c" > "$out/insndiff-sub.c"
# One statement added, so instructions appear and everything after them shifts.
sed 's|/\* INSERT \*/|acc = acc ^ 21;|' "$out/insndiff.c" > "$out/insndiff-ins.c"
# One statement removed, which is the same test in the other direction.
sed '/acc = acc - 7;/d' "$out/insndiff.c" > "$out/insndiff-del.c"
for v in "" -sub -ins -del; do
  "$cc" -O0 -ffreestanding -fno-stack-protector -fno-builtin -fno-pie -no-pie \
    -nostdlib -static -o "$out/insndiff${v}.a64" "$out/insndiff${v}.c" 2>/dev/null || true
done
rm -f "$out"/insndiff*.c

# A statically linked binary, which is what signature matching exists for: the
# same program as hello.a64 with every libc function it uses copied into it out
# of the distribution's own libc.a. Unstripped as the oracle and stripped as the
# thing to be measured, so a name the signature library recovers can be checked
# against the name the linker actually gave that address.
if [ -e fixtures/src/hello.c ]; then
  "$cc" -O2 -static -fno-pie -no-pie -o "$out/hello.static.a64" fixtures/src/hello.c \
    2>/dev/null || true
  if [ -e "$out/hello.static.a64" ]; then
    cp "$out/hello.static.a64" "$out/hello.static.a64.stripped"
    strip "$out/hello.static.a64.stripped"
  fi
fi

# Emulation fixtures: the three things M10 says emulation is for, plus a run
# that does not terminate. Built for both architectures and executed, so the
# emulation tests compare against what a processor produced rather than against
# the emulator.
#
# gcc for AArch64 and clang for x86-64 on purpose, and not because of the
# sysroot: clang compiles this switch into a decision tree on AArch64 and into a
# jump table on x86-64, and gcc does the opposite, so this pairing is the one
# that leaves a real table on each architecture for the confirmation gate to
# check. The AArch64 one is the compact byte-offset form, which is exactly the
# form that cannot be bounded by scanning.
if [ -e fixtures/emulate/paths.c ]; then
  for opt in O1 O2; do
    "$cc" -g -"$opt" -ffreestanding -fno-stack-protector -fno-builtin -fno-pie \
      -no-pie -nostdlib -static -o "$out/em-paths.a64.$opt" fixtures/emulate/paths.c \
      2>/dev/null || true
    if [ -n "${lld:-}" ]; then
      "$xcc" --target=x86_64-unknown-linux-gnu -B"$out/ld" -fuse-ld=lld -g -"$opt" \
        -ffreestanding -fno-stack-protector -fno-builtin -fno-pie -nostdlib -static \
        -o "$out/em-paths.x64.$opt" fixtures/emulate/paths.c 2>/dev/null || true
    fi
    if [ -x "$out/em-paths.a64.$opt" ]; then
      "$out/em-paths.a64.$opt" > "$out/em-paths.a64.$opt.out" || true
    fi
    if [ -x "$out/em-paths.x64.$opt" ] && command -v qemu-x86_64 > /dev/null; then
      qemu-x86_64 "$out/em-paths.x64.$opt" > "$out/em-paths.x64.$opt.out" || true
    fi
    # The two architectures computing the same answers is the oracle checking
    # itself before anything is measured against it.
    if [ -s "$out/em-paths.a64.$opt.out" ] && [ -s "$out/em-paths.x64.$opt.out" ]; then
      cmp -s "$out/em-paths.a64.$opt.out" "$out/em-paths.x64.$opt.out" \
        || echo "warning: em-paths.$opt disagrees across architectures" >&2
    fi
  done
fi

# The DecBench corpus, which is real projects rather than the C files above.
#
# Not built here: it fetches upstream sources over the network and takes tens of
# minutes, which is not what `build-fixtures.sh` is for. It is a separate script
# with its own cache outside the checkout, and the G4 boundary gate uses it when
# it is there and the local fixtures when it is not:
#
#   scripts/decbench-fixtures.sh zlib bzip2 gzip   # or --all, or --list
#   scripts/boundary-gate.sh                       # G4, both corpora
#
# See docs/decbench.md.
