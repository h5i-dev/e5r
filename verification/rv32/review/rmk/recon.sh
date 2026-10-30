#!/bin/sh
# RMK feasibility recon (untrusted evidence): build the upstream QEMU Rynk example
# at a pinned commit in /dev/shm, release profile, pinned toolchain, unchanged
# sources and lockfile, then list its instruction mix and panic call sites.
# Original e5r code, Apache-2.0.
set -eu
PIN=71556128fa72881fc35f0bf6c292d5e28ad9568d
S=${S:-/dev/shm/e5r-rmk-recon}
HERE=$(cd "$(dirname "$0")" && pwd)
export RUSTUP_TOOLCHAIN=1.98.1          # never let rust-toolchain.toml (channel=stable) sync a channel
export CARGO_HOME="$S/cargo-home" CARGO_BUILD_JOBS=2
mkdir -p "$S"
if [ ! -d "$S/rmk/.git" ]; then
  git init -q "$S/rmk" && git -C "$S/rmk" remote add origin https://github.com/rmk-rs/rmk
fi
git -C "$S/rmk" fetch -q --depth 1 origin $PIN && git -C "$S/rmk" checkout -q FETCH_HEAD
cd "$S/rmk/examples/use_rust/qemu-riscv-rynk"
cargo build --release --locked
E=target/riscv32imac-unknown-none-elf/release/rmk-qemu-riscv
sha256sum "$E"
T=$(rustc --print sysroot)/lib/rustlib/x86_64-unknown-linux-gnu/bin
"$T/llvm-readobj" -h --arch-specific "$E" | grep -E 'Entry|Value: rv'
"$T/llvm-size" -A "$E"
"$T/llvm-objdump" -d "$E" > "$S/rmk.dis"
grep -P '^[0-9a-f]+:' "$S/rmk.dis" | awk -F'\t' '{print $2}' | sort | uniq -c | sort -rn
python3 -I "$HERE/panic_sites.py" "$S/rmk.dis"
