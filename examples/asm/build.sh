#!/usr/bin/env bash
# The structured-assembly example (examples/asm/README.md): assemble
# memset.s, compile memset.c with `nocompiler cc`, and compare both with the
# committed binaries; with --update, replace them, their Lean images and the
# proof skeleton.
#
#   examples/asm/build.sh [--update]       (NOCOMPILER overrides the tool)
set -euo pipefail
cd "$(dirname "$0")/../.."
NOCOMPILER=${NOCOMPILER:-target/release/nocompiler}
out=examples/build/asm
mkdir -p "$out"
"$NOCOMPILER" asm examples/asm/memset.s -o "$out/memset.elf" \
  --skeleton "$out/Memset.skeleton.lean" --namespace Examples.Memset.Image
"$NOCOMPILER" cc -O2 examples/asm/memset.c -o "$out/memset_cc.elf"
status=0
for name in memset memset_cc; do
  mod=$(echo "$name" | sed -E 's/(^|_)([a-z])/\U\2/g')
  if [ "${1:-}" = --update ]; then
    cp "$out/$name.elf" "examples/elf/$name.elf"
    "$NOCOMPILER" export "examples/elf/$name.elf" --namespace "Examples.$mod.Image" \
      -o "lean/Examples/$mod/Image.lean"
  elif ! cmp -s "$out/$name.elf" "examples/elf/$name.elf"; then
    echo "$name: the build differs from examples/elf/$name.elf"; status=1
  fi
done
# The committed proof is the skeleton plus the verification conditions.
if ! head -c "$(wc -c < "$out/Memset.skeleton.lean")" lean/Examples/Memset.lean | cmp -s - "$out/Memset.skeleton.lean"; then
  echo "lean/Examples/Memset.lean does not start with the skeleton nocompiler asm writes ($out/Memset.skeleton.lean)"
  status=1
fi
exit $status
