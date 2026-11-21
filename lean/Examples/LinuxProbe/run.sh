#!/bin/bash
# Build the probe and run it under qemu-riscv64 (user mode) on a 6-byte file.
# File calls (openat, read, readv, lseek, fstat, close) go to the host Linux
# kernel; brk/mmap/mprotect/munmap are emulated by qemu itself.
# Usage: lean/Examples/LinuxProbe/run.sh [QEMU] [LD.LLD]  -> diff against probe.out
set -euo pipefail
cd "$(dirname "$0")"
QEMU=${1:-qemu-riscv64-static}
LLD=${2:-ld.lld}
w=$(mktemp -d); trap 'rm -rf "$w"' EXIT
clang --target=riscv64-unknown-elf -march=rv64im -mabi=lp64 -mcmodel=medany -O1 -ffreestanding \
  -nostdlib -fno-pic -c probe.c -o "$w/probe.o"
"$LLD" -static -e _start "$w/probe.o" -o "$w/probe.elf"
printf 'abcdef' > "$w/in.txt"
"$QEMU" "$w/probe.elf" "$w/in.txt" | diff - probe.out && echo "probe: matches probe.out"
