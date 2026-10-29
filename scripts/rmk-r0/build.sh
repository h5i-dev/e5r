#!/bin/bash
# One audited build of RMK examples/use_rust/qemu-riscv-rynk for the R0 audit.
# Original e5r code, Apache-2.0. Written independently of
# verification/rv32/rmk/build-canonical.sh, to check its claims.
#
# usage: build.sh CHECKOUT_ROOT remap|plain OUT_DIR
#   CHECKOUT_ROOT  must not exist; it is created, used and removed.
#   remap          --remap-path-prefix for the checkout, CARGO_HOME and the sysroot
#                  (the canonical recipe's flags); plain: none (the recon recipe).
# Writes OUT_DIR/{rmk-qemu-riscv.elf, build-v.log, env.txt}. Rust 1.98.1 via
# RUSTUP_TOOLCHAIN only (no install/sync), --release --locked, private CARGO_HOME
# inside CHECKOUT_ROOT, the upstream pin fetched fresh and checked clean.
set -euo pipefail
S=$1 MODE=$2 OUT=$3
PIN=71556128fa72881fc35f0bf6c292d5e28ad9568d
LOCK=4d994f17ac6ba04b68fee7ab0c00b96f2fd9db348139dce815c956b281bbc49c
test ! -e "$S" || { echo "$S exists; refusing to touch it" >&2; exit 2; }
mkdir -p "$OUT"
trap 'cd /; rm -rf "$S"' EXIT
mkdir -p "$S"
git init -q "$S/rmk"
git -C "$S/rmk" fetch -q --depth 1 https://github.com/rmk-rs/rmk "$PIN"
git -C "$S/rmk" checkout -q FETCH_HEAD
test "$(git -C "$S/rmk" rev-parse HEAD)" = "$PIN"
test -z "$(git -C "$S/rmk" status --porcelain)"
X="$S/rmk/examples/use_rust/qemu-riscv-rynk"
echo "$LOCK  $X/Cargo.lock" | sha256sum -c --quiet
env -i HOME="$HOME" PATH="$PATH" bash -c '
  set -euo pipefail
  export RUSTUP_TOOLCHAIN=1.98.1 CARGO_HOME="$1/cargo-home" CARGO_TERM_COLOR=never
  if [ "$2" = remap ]; then
    SYSROOT=$(rustc --print sysroot)
    export RUSTFLAGS="--remap-path-prefix=$1/rmk=/rmk --remap-path-prefix=$CARGO_HOME=/cargo --remap-path-prefix=$SYSROOT=/rustup-toolchain"
  fi
  { echo "checkout=$1/rmk mode=$2"; env | grep -E "^(RUST|CARGO)" | sort; rustc -vV; cargo -vV; } > "$3/env.txt"
  cd "$1/rmk/examples/use_rust/qemu-riscv-rynk"
  cargo build --release --locked -v > "$3/build-v.log" 2>&1
' _ "$S" "$MODE" "$OUT"
cp "$X/target/riscv32imac-unknown-none-elf/release/rmk-qemu-riscv" "$OUT/rmk-qemu-riscv.elf"
echo "embedded build paths: $(strings -a "$OUT/rmk-qemu-riscv.elf" | grep -c "$S" || true)" >> "$OUT/env.txt"
sha256sum "$OUT/rmk-qemu-riscv.elf"
