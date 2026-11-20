#!/bin/bash
# R0: reproducible build of RMK examples/use_rust/qemu-riscv-rynk (release, Rust 1.98.1, --locked,
# unchanged sources and lockfile). Original e5r code, Apache-2.0.
#
# Two things make the build path matter, and this recipe removes both:
#  * panic locations and debug strings embed absolute source paths -> every path is remapped;
#  * Cargo's crate metadata hashes the absolute path of path dependencies, and that hash orders
#    functions in .text (remapping does not change it) -> the checkout path is fixed.
# The toolchain is used read-only (RUSTUP_TOOLCHAIN, no install or sync); CARGO_HOME is private.
#
# usage: build-canonical.sh OUT.elf      (needs network for the pinned commit and crates)
set -euo pipefail
S=/dev/shm/e5r-rmk-canonical
PIN=71556128fa72881fc35f0bf6c292d5e28ad9568d
SRC=${RMK_SRC:-https://github.com/rmk-rs/rmk}
test ! -e "$S" || { echo "$S exists; refusing to touch it" >&2; exit 2; }
trap 'cd /; rm -rf "$S"' EXIT
mkdir -p "$S"
git init -q "$S/rmk"; git -C "$S/rmk" fetch -q --depth 1 "$SRC" "$PIN"; git -C "$S/rmk" checkout -q FETCH_HEAD
test "$(git -C "$S/rmk" rev-parse HEAD)" = "$PIN"; test -z "$(git -C "$S/rmk" status --porcelain)"
export RUSTUP_TOOLCHAIN=1.98.1 CARGO_HOME="$S/cargo-home"
SYSROOT=$(rustc --print sysroot)
export RUSTFLAGS="--remap-path-prefix=$S/rmk=/rmk --remap-path-prefix=$CARGO_HOME=/cargo --remap-path-prefix=$SYSROOT=/rustup-toolchain"
cd "$S/rmk/examples/use_rust/qemu-riscv-rynk"
cargo build --release --locked
E=target/riscv32imac-unknown-none-elf/release/rmk-qemu-riscv
if strings -a "$E" | grep -q "$S\|/home/"; then echo "a build path is still embedded" >&2; exit 1; fi
cp "$E" "$1"; sha256sum "$1"
