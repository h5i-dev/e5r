#!/usr/bin/env bash
# Item 7 of spec-v1-refine.md: compile the candidate refinement targets with
# rustc into the profile and count their functions per level
# (docs/isa/refine-targets.md).
#
#   examples/refine/conformance.sh [--markdown]
#
# Needs the pinned nightly with rust-src (core is rebuilt with -Zbuild-std),
# network for crates.io the first time, ld.lld and llvm-nm. CARGO_HOME and
# CARGO_TARGET_DIR default to directories under $SCRATCH (default /tmp).
set -euo pipefail
cd "$(dirname "$0")/../.."
TOOLCHAIN=${TOOLCHAIN:-nightly-2026-11-01}
SCRATCH=${SCRATCH:-/tmp}
export CARGO_HOME=${CARGO_HOME:-$SCRATCH/refine-cargo-home}
export CARGO_TARGET_DIR=${CARGO_TARGET_DIR:-$SCRATCH/refine-target}
LLD=${LLD:-$(command -v ld.lld || command -v ld.lld-20 || echo ld.lld)}
NOCOMPILER=${NOCOMPILER:-target/release/nocompiler}
TARGET=riscv64im-unknown-none-elf
# The profile's flags, as nocompiler cc has them for clang:
#   riscv64im + Zba + Zbb, no C, no A        (R1)
#   medany, static                           (relocation, docs/isa/toolchain.md)
#   no jump tables                           (R2)
#   no trap after unreachable code           (R1: `unimp` is not in the profile)
#   panic = abort (Cargo.toml), opt-level 3
# Block placement stays on: unlike clang's C, rustc's IR puts the return
# block early, and without placement the jumps back to it break R3 more often
# than rotated loops do with it (docs/isa/refine-targets.md). EXTRA_RUSTFLAGS
# adds flags (e.g. -C llvm-args=-disable-block-placement to compare).
export RUSTFLAGS="-C target-feature=+m,+zba,+zbb -C code-model=medium -C relocation-model=static \
  -C jump-tables=no -Z trap-unreachable=no ${EXTRA_RUSTFLAGS:-}"
(cd examples/refine/targets && cargo "+$TOOLCHAIN" build -q --release --target $TARGET \
  -Zbuild-std=core,compiler_builtins -Zbuild-std-features=compiler-builtins-mem)
a="$CARGO_TARGET_DIR/$TARGET/release/librefine_targets.a"
out="$CARGO_TARGET_DIR/targets.elf"
"$LLD" -static -e _start --build-id=none -z noseparate-code --whole-archive "$a" -o "$out"
"$NOCOMPILER" check --json "$out" > "$CARGO_TARGET_DIR/check.json" || true
python3 -I examples/refine/conformance.py "$CARGO_TARGET_DIR/check.json" "$a" "$@"
