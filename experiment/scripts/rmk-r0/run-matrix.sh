#!/bin/bash
# The R0 audit build matrix (docs: verification/rv32/rmk-r0-audit/AUDIT.md).
# Original e5r code, Apache-2.0.
# usage: run-matrix.sh OUT_DIR CANONICAL_SCRIPT
#   CANONICAL_SCRIPT: verification/rv32/rmk/build-canonical.sh as committed by main (run verbatim).
# Every build uses its own fresh checkout and CARGO_HOME under /dev/shm and removes it after.
# /dev/shm/e5r-rmk-canonical and /dev/shm/e5r-rmk-recon must be free (the scripts refuse otherwise).
set -u
OUT=$(realpath "$1") CANON=$(realpath "$2") HERE=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$OUT"
for i in 1 2; do echo "== main canonical #$i"; "$CANON" "$OUT/main-canonical-$i.elf" 2>&1 | tail -1; done
b() { echo "== $3 ($1, $2)"; "$HERE/build.sh" "$1" "$2" "$OUT/$3" 2>&1 | tail -1; }
b /dev/shm/e5r-rmk-canonical remap mine-canonical
b /dev/shm/e5r-rmk-recon plain mine-recon
b /dev/shm/e5r-claude-r0x/a/rmkA remap mine-A
b /dev/shm/e5r-claude-r0x/b-longer-name/rmkB remap mine-B
b /dev/shm/e5r-claude-r0x/a/rmkA plain mine-A-plain
rmdir /dev/shm/e5r-claude-r0x/a /dev/shm/e5r-claude-r0x/b-longer-name /dev/shm/e5r-claude-r0x 2>/dev/null || true
