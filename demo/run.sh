#!/usr/bin/env bash
# The A-vs-B demo, end to end (demo/README.md):
#   1. rebuild both binaries from demo/src (A: plain clang rv64gc, B: e5r cc)
#      and compare them with the committed demo/elf/;
#   2. check B against the profile; test cobs_decode on both against a reference
#      under qemu; check the RVC extension (decode against llvm-mc, execution
#      against qemu);
#   3. export the images again and require them equal to the committed ones;
#   4. check the Lean proofs (timed, per file) and run e5r-audit;
#   5. print the proof sizes.
# Needs: cargo, clang, ld.lld, llvm-mc, llvm-nm, qemu-riscv64(-static), lake.
# RVC_EXEC_N (default 500) sets how many buffers the execution check runs.
set -euo pipefail
cd "$(dirname "$0")/.."
export LLD=${LLD:-$(command -v ld.lld || command -v ld.lld-20)}
cargo build --release -q -p e5r
E5R=${CARGO_TARGET_DIR:-target}/release/e5r
export E5R
LAKE=(lake)
if command -v systemd-run >/dev/null && [ -n "${E5R_MEM:-}" ]; then
  LAKE=(systemd-run --user --scope --quiet -p MemoryMax="$E5R_MEM" -p MemorySwapMax=0 --setenv=PATH="$PATH" lake)
fi
step() { printf '\n== %s\n' "$*"; }

step "build (demo/build.sh)"
demo/build.sh

step "the profile, on B"
for f in sum cobs; do "$E5R" check "demo/elf/$f.b.elf" | tail -1; done

step "cobs_decode against a reference, under qemu (A and B)"
for x in a b; do python3 -I demo/test/cobs_test.py "demo/build/cobs_test.$x.elf" "demo/elf/cobs.$x.elf"; done

step "images"
demo_funcs() { llvm-nm --print-size "$1" | awk '$3 == "T" && $4 != "_start" { printf "%s:%d:%d ", $4, strtonum("0x"$1), strtonum("0x"$2) }'; }
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
(cd lean && "${LAKE[@]}" build E5R.Ext.Rvc E5R.Elf rvc-run >/dev/null)
for f in sum cobs; do
  F=$(echo "$f" | sed -E 's/(^|_)([a-z])/\U\2/g')
  "$E5R" export "demo/elf/$f.b.elf" --namespace "Demo.$F.ImageB" -o "$tmp/$F.B.lean"
  (cd lean && lake env lean --run ../demo/tools/ExportC.lean "../demo/elf/$f.a.elf" "Demo.$F.ImageA" \
    $(demo_funcs "../demo/elf/$f.a.elf") > "$tmp/$F.A.lean")
  for S in A B; do
    cmp -s "$tmp/$F.$S.lean" "lean/Demo/$F/Image$S.lean" || { echo "FAIL lean/Demo/$F/Image$S.lean is not the export of demo/elf"; exit 1; }
  done
  echo "ok   lean/Demo/$F/Image{A,B}.lean are the exports of demo/elf/$f.{a,b}.elf"
done

step "the RVC extension: decode against llvm-mc, execution against qemu"
(cd lean && lake env lean --run ../demo/tools/RvcTable.lean > "$tmp/rvc_table.txt")
python3 -I demo/test/rvc_decode.py "$tmp/rvc_table.txt"
python3 -I demo/test/rvc_exec.py lean/.lake/build/bin/rvc-run demo/build/cobs_test.a.elf demo/elf/cobs.a.elf \
  0x$(llvm-nm demo/elf/cobs.a.elf | awk '$3 == "cobs_decode" { print $1 }') "${RVC_EXEC_N:-500}"

step "Lean: dependencies, then each proof file timed"
(cd lean && "${LAKE[@]}" build E5R E5R.Ext.Rvc Demo.SumSpec Demo.CobsSpec Demo.Sum.ImageA Demo.Sum.ImageB \
  Demo.Cobs.ImageA Demo.Cobs.ImageB >/dev/null)
for m in SumB SumA CobsB CobsA; do
  t0=$(date +%s.%N)
  (cd lean && "${LAKE[@]}" env lean "Demo/$m.lean")
  printf 'ok   Demo/%s.lean checks in %.1f s\n' "$m" "$(echo "$(date +%s.%N) - $t0" | bc)"
done
(cd lean && "${LAKE[@]}" build Demo e5r-audit >/dev/null && lake exe e5r-audit)

step "proof sizes"
python3 -I demo/tools/count.py
