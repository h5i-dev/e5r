#!/usr/bin/env bash
# The A-vs-B demo, end to end (examples/demo/README.md):
#   1. rebuild both binaries from examples/demo/src (A: plain clang rv64gc, B: nocompiler cc)
#      and compare them with the committed examples/demo/elf/;
#   2. check B against the profile; test cobs_decode on both against a reference
#      under qemu; check the RVC extension (decode against llvm-mc, execution
#      against qemu);
#   3. export the images again and require them equal to the committed ones;
#   4. check the Lean proofs (timed, per file) and run nocompiler-audit;
#   5. print the proof sizes.
# Needs: cargo, clang, ld.lld, llvm-mc, llvm-nm, qemu-riscv64(-static), lake.
# RVC_EXEC_N (default 500) sets how many buffers the execution check runs.
set -euo pipefail
cd "$(dirname "$0")/../.."
export LLD=${LLD:-$(command -v ld.lld || command -v ld.lld-20)}
cargo build --release -q -p nocompiler-cli --bin nocompiler
NOCOMPILER=${CARGO_TARGET_DIR:-target}/release/nocompiler
export NOCOMPILER
LAKE=(lake)
if command -v systemd-run >/dev/null && [ -n "${NOCOMPILER_MEM:-}" ]; then
  LAKE=(systemd-run --user --scope --quiet -p MemoryMax="$NOCOMPILER_MEM" -p MemorySwapMax=0 --setenv=PATH="$PATH" lake)
fi
step() { printf '\n== %s\n' "$*"; }

step "build (examples/demo/build.sh)"
examples/demo/build.sh

step "the profile, on B"
for f in sum cobs; do "$NOCOMPILER" check "examples/demo/elf/$f.b.elf" | tail -1; done

step "cobs_decode against a reference, under qemu (A and B)"
for x in a b; do python3 -I examples/demo/test/cobs_test.py "examples/demo/build/cobs_test.$x.elf" "examples/demo/elf/cobs.$x.elf"; done

step "images"
demo_funcs() { llvm-nm --print-size "$1" | awk '$3 == "T" && $4 != "_start" { printf "%s:%d:%d ", $4, strtonum("0x"$1), strtonum("0x"$2) }'; }
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
(cd lean && "${LAKE[@]}" build NoCompiler.Ext.Rvc NoCompiler.Elf rvc-run >/dev/null)
for f in sum cobs; do
  F=$(echo "$f" | sed -E 's/(^|_)([a-z])/\U\2/g')
  "$NOCOMPILER" export --lean-level-check "examples/demo/elf/$f.b.elf" --namespace "Demo.$F.ImageB" -o "$tmp/$F.B.lean"
  (cd lean && lake env lean --run ../examples/demo/tools/ExportC.lean "../examples/demo/elf/$f.a.elf" "Demo.$F.ImageA" \
    $(demo_funcs "../examples/demo/elf/$f.a.elf") > "$tmp/$F.A.lean")
  for S in A B; do
    cmp -s "$tmp/$F.$S.lean" "lean/Demo/$F/Image$S.lean" || { echo "FAIL lean/Demo/$F/Image$S.lean is not the export of examples/demo/elf"; exit 1; }
  done
  echo "ok   lean/Demo/$F/Image{A,B}.lean are the exports of examples/demo/elf/$f.{a,b}.elf"
done

step "the RVC extension: decode against llvm-mc, execution against qemu"
(cd lean && lake env lean --run ../examples/demo/tools/RvcTable.lean > "$tmp/rvc_table.txt")
python3 -I examples/demo/test/rvc_decode.py "$tmp/rvc_table.txt"
python3 -I examples/demo/test/rvc_exec.py lean/.lake/build/bin/rvc-run examples/demo/build/cobs_test.a.elf examples/demo/elf/cobs.a.elf \
  0x$(llvm-nm examples/demo/elf/cobs.a.elf | awk '$3 == "cobs_decode" { print $1 }') "${RVC_EXEC_N:-500}"

step "Lean: dependencies, then each proof file timed"
(cd lean && "${LAKE[@]}" build NoCompiler NoCompiler.Ext.Rvc Demo.SumSpec Demo.CobsSpec Demo.Sum.ImageA Demo.Sum.ImageB \
  Demo.Cobs.ImageA Demo.Cobs.ImageB >/dev/null)
for m in SumB SumA Sum2B Sum2A CobsB CobsA; do
  t0=$(date +%s%N)
  (cd lean && "${LAKE[@]}" env lean "Demo/$m.lean")
  python3 -c "import sys; print(f'ok   Demo/{sys.argv[1]}.lean checks in {(int(sys.argv[3]) - int(sys.argv[2])) / 1e9:.1f} s')" \
    "$m" "$t0" "$(date +%s%N)"
done
(cd lean && "${LAKE[@]}" build Demo nocompiler-audit >/dev/null && lake exe nocompiler-audit)

step "proof sizes"
python3 -I examples/demo/tools/count.py
