#!/usr/bin/env bash
# The tree-diff example (docs/isa/refine.md, item 5): `sum` written in the
# structured text (sum_a.s, the disasm of examples/elf/sum.elf's sum), and two
# edits of it: sum_b.s commutes the loop's add (a straight-line region),
# sum_c.s adds an instruction to the loop body (a straight-line region, the
# moved branches jump pairs); sum_d.s counts down by 2 and back up by 1 (the
# changed instruction alone differs; the region grows until both sides agree). Assembles each, links it, exports the images and
# writes what `nocompiler refine` finds, with its proofs
# (lean/Examples/Refine/Diff/).
#
#   examples/refine/diff/build.sh [--update]      (NOCOMPILER, LLD override the tools)
set -euo pipefail
cd "$(dirname "$0")/../../.."
NOCOMPILER=${NOCOMPILER:-target/release/nocompiler}
LLD=${LLD:-$(command -v ld.lld || command -v ld.lld-20 || echo ld.lld)}
out=examples/build/refine-diff
mkdir -p "$out"
status=0
for x in a b c d; do
  "$NOCOMPILER" asm "examples/refine/diff/sum_$x.s" -o "$out/sum_$x.o" >/dev/null
  "$LLD" -static -e _start --build-id=none "$out/sum_$x.o" -o "$out/refine-sum-$x.elf"
  if [ "${1:-}" = --update ]; then
    cp "$out/refine-sum-$x.elf" examples/elf/
    X=$(echo $x | tr a-z A-Z)
    "$NOCOMPILER" export --lean-level-check "examples/elf/refine-sum-$x.elf" --namespace "Examples.Refine.Diff.Img$X" \
      -o "lean/Examples/Refine/Diff/Img$X.lean"
  elif ! cmp -s "$out/refine-sum-$x.elf" "examples/elf/refine-sum-$x.elf"; then
    echo "refine-sum-$x.elf differs from examples/elf/"; status=1
  fi
done
if [ "${1:-}" = --update ]; then
  "$NOCOMPILER" refine examples/elf/refine-sum-a.elf examples/elf/refine-sum-b.elf sum \
    --namespace Examples.Refine.Diff.AB -o lean/Examples/Refine/Diff/AB.lean \
    --images Examples.Refine.Diff.ImgA Examples.Refine.Diff.ImgB
  "$NOCOMPILER" refine examples/elf/refine-sum-a.elf examples/elf/refine-sum-c.elf sum \
    --namespace Examples.Refine.Diff.AC -o lean/Examples/Refine/Diff/AC.lean \
    --images Examples.Refine.Diff.ImgA Examples.Refine.Diff.ImgC
  "$NOCOMPILER" refine examples/elf/refine-sum-a.elf examples/elf/refine-sum-d.elf sum \
    --namespace Examples.Refine.Diff.AD -o lean/Examples/Refine/Diff/AD.lean \
    --images Examples.Refine.Diff.ImgA Examples.Refine.Diff.ImgD
fi
exit $status
