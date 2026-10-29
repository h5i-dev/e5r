#!/bin/bash
# Build the memmove regression matrix natively in a scratch Lake package of copies and run it:
# SHARDS parallel shards of the main matrix, then the boundary set. Logs and timings go to OUT.
# usage: verification/rv32/rmk-audit/matrix.sh SCRATCH_DIR OUT_DIR [SHARDS]
set -euo pipefail
R=$(cd "$(dirname "$0")/.." && pwd) A=$1 OUT=$2 K=${3:-8}
test ! -e "$A" || { echo "$A exists" >&2; exit 2; }
grep -q "f39d833f520ba4de6c7085423a8dc3ee475ec19bdfb55c10c81c6ae868f43c30" "$R/Projects/rmk/Elf.lean" || {
  echo "Projects/rmk/Elf.lean is not the pinned image" >&2; exit 2; }
mkdir -p "$A/Theories/Board" "$A/Projects/rmk" "$OUT"
A=$(cd "$A" && pwd) OUT=$(cd "$OUT" && pwd)
cp "$R/lean-toolchain" "$A/"
cp "$R"/Theories/{Hart,Platform,Logic,RamElf,Chunk}.lean "$A/Theories/"
cp "$R/Theories/Board/QemuVirtRv32.lean" "$A/Theories/Board/"
cp "$R/Projects/rmk/Elf.lean" "$A/Projects/rmk/"
cp "$R/rmk-audit/MemmoveMatrix.lean" "$A/"
cat > "$A/lakefile.lean" <<'L'
import Lake
open Lake DSL
package audit
lean_lib Theories where
  globs := #[.submodules `Theories]
lean_lib Projects where
  globs := #[.submodules `Projects]
@[default_target]
lean_exe memmove_matrix where
  root := `MemmoveMatrix
L
(cd "$A" && lake build memmove_matrix > "$OUT/build.log" 2>&1)
X="$A/.lake/build/bin/memmove_matrix"
seq 0 $((K - 1)) | xargs -P "$K" -I{} sh -c "/usr/bin/time -f 'shard {}: %e s, %M KB' '$X' main {} $K > '$OUT/shard-{}.log' 2> '$OUT/shard-{}.time'; echo \$? > '$OUT/shard-{}.exit'"
/usr/bin/time -f 'bounds: %e s, %M KB' "$X" bounds > "$OUT/bounds.log" 2> "$OUT/bounds.time" || true
cat "$OUT"/shard-*.time "$OUT/bounds.time"
grep -h "^shard\|^bounds:" "$OUT"/shard-*.log "$OUT/bounds.log"
grep -h "^FAIL" "$OUT"/shard-*.log "$OUT/bounds.log" | head -50 || true
