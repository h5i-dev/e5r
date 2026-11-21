#!/usr/bin/env bash
# Build a copy of examples/refine/targets (or an edited one) as
# examples/refine/conformance.sh does, but with the paths remapped, so that two
# builds of the same source in different directories give the same bytes.
#
#   scripts/core/bench-scale-build.sh CRATE_DIR OUT.elf
#
# Flags: those of conformance.sh (docs/isa/refine-targets.md) plus
# --remap-path-prefix for the crate and for CARGO_HOME.
set -euo pipefail
crate=$(cd "$1" && pwd); out=$2
TOOLCHAIN=${TOOLCHAIN:-nightly-2026-11-01}
export CARGO_HOME=${CARGO_HOME:?set CARGO_HOME (not on the root disk)}
export CARGO_TARGET_DIR=${CARGO_TARGET_DIR:?set CARGO_TARGET_DIR}
LLD=${LLD:-$(command -v ld.lld || command -v ld.lld-20 || echo ld.lld)}
TARGET=riscv64im-unknown-none-elf
export RUSTFLAGS="-C target-feature=+m,+zba,+zbb -C code-model=medium -C relocation-model=static \
  -C jump-tables=no -Z trap-unreachable=no --remap-path-prefix=$crate=/crate --remap-path-prefix=$CARGO_HOME=/cargo"
(cd "$crate" && cargo "+$TOOLCHAIN" build -q --release --target $TARGET \
  -Zbuild-std=core,compiler_builtins -Zbuild-std-features=compiler-builtins-mem)
"$LLD" -static -e _start --build-id=none -z noseparate-code --whole-archive \
  "$CARGO_TARGET_DIR/$TARGET/release/librefine_targets.a" -o "$out"
