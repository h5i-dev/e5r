#!/usr/bin/env bash
# Criterion 3 of docs/isa/v1.md: one object, linked two ways.
#
# examples/sum.c is compiled once, with the profile's flags and
# -ffunction-sections, into one object; ld.lld links it twice:
#   examples/elf/sum.link1.elf  the default layout (.text at 0x11190, sum first)
#   examples/elf/sum.link2.elf  .text at 0x40000, the functions in the reverse order
# and `nocompiler module` writes, for each, the relocatable module and the
# layout (lean/Examples/Link/{One,Two}.lean). The two modules are the same
# (lean/Examples/Link.lean proves it by rfl), and one theorem about it covers
# both binaries: nocompiler-audit checks that the module linked at each ELF's
# own layout is that ELF's .text and data.
#
#   examples/link/build.sh [--update]       (CLANG, LLD, NOCOMPILER override the tools)
set -euo pipefail
cd "$(dirname "$0")/../.."
CLANG=${CLANG:-clang}
LLD=${LLD:-$(command -v ld.lld || command -v ld.lld-20 || echo ld.lld)}
NOCOMPILER=${NOCOMPILER:-target/release/nocompiler}
out=examples/build/link
mkdir -p "$out"
cflags=(--target=riscv64-unknown-elf -march=rv64im_zba_zbb -mabi=lp64 -mcmodel=medany -mno-relax -O2
  -ffreestanding -nostdlib -fno-pic -fno-asynchronous-unwind-tables -fno-unwind-tables -fno-ident
  -ffunction-sections)
"$CLANG" "${cflags[@]}" -c examples/sum.c -o "$out/sum.o"
printf '_start\nsum2\nsum\n' > "$out/order.txt"
lflags=(-static -e _start --build-id=none -z noseparate-code)
"$LLD" "${lflags[@]}" "$out/sum.o" -o "$out/sum.link1.raw.elf"
"$LLD" "${lflags[@]}" -Ttext=0x40000 --symbol-ordering-file="$out/order.txt" "$out/sum.o" -o "$out/sum.link2.raw.elf"
status=0
for k in 1 2; do
  "$NOCOMPILER" annotate "$out/sum.link$k.raw.elf" -o "$out/sum.link$k.elf" >/dev/null
  ns=$([ $k = 1 ] && echo One || echo Two)
  if [ "${1:-}" = --update ]; then
    cp "$out/sum.link$k.elf" "examples/elf/sum.link$k.elf"
    "$NOCOMPILER" module "examples/elf/sum.link$k.elf" --namespace "Examples.Link.$ns" -o "lean/Examples/Link/$ns.lean"
  elif ! cmp -s "$out/sum.link$k.elf" "examples/elf/sum.link$k.elf"; then
    echo "sum.link$k.elf: the build differs from examples/elf/"; status=1
  fi
done
if [ "${1:-}" = --update ]; then
  "$NOCOMPILER" ledger examples/elf/sum.link1.elf --proofs examples/link/proofs.tsv > examples/link/ledger.jsonl
fi
exit $status
