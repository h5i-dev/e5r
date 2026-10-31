#!/bin/bash
# Build and run the memmove execution audit (MemmoveRun.lean) natively, in a scratch Lake
# package made of copies, so nothing in the repository is built into or edited.
# Needs the runner-generated Projects/rmk/Elf.lean (run jobs/rmk/rmk-memmove-small.json first).
# usage: verification/rv32/rmk-audit/run.sh SCRATCH_DIR   (SCRATCH_DIR must not exist)
set -euo pipefail
R=$(cd "$(dirname "$0")/.." && pwd) A=$1
test ! -e "$A" || { echo "$A exists" >&2; exit 2; }
grep -q "f39d833f520ba4de6c7085423a8dc3ee475ec19bdfb55c10c81c6ae868f43c30" "$R/Projects/rmk/Elf.lean" || {
  echo "Projects/rmk/Elf.lean is not the pinned image" >&2; exit 2; }
mkdir -p "$A/Theories/Board" "$A/Projects/rmk"
cp "$R/lean-toolchain" "$A/"
cp "$R"/Theories/{Hart,Platform,Logic,RamElf,Chunk}.lean "$A/Theories/"
cp "$R/Theories/Board/QemuVirtRv32.lean" "$A/Theories/Board/"
cp "$R/Projects/rmk/Elf.lean" "$A/Projects/rmk/"
cp "$R/rmk-audit/MemmoveRun.lean" "$A/"
cat > "$A/lakefile.lean" <<'L'
import Lake
open Lake DSL
package audit
lean_lib Theories where
  globs := #[.submodules `Theories]
lean_lib Projects where
  globs := #[.submodules `Projects]
@[default_target]
lean_exe memmove_run where
  root := `MemmoveRun
L
(cd "$A" && lake build memmove_run > build.log 2>&1)
"$A/.lake/build/bin/memmove_run" || true
