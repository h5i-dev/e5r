#!/usr/bin/env bash
# Negative controls for the example proofs: a proof that still checks after
# the code it is about is broken would be no evidence about that code.
#
# For each mutation below, patch one instruction of the committed binary,
# export the patched binary in place of the committed image, in a copy of
# lean/, and require the proof module to FAIL. Then require the unpatched
# copy to pass, so a failure is the mutation's and not the copy's.
#
#   scripts/check-proof-controls.sh        (needs target/release/e5r and lake)
set -euo pipefail
cd "$(dirname "$0")/.."
E5R=${E5R:-$PWD/target/release/e5r}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

# elf  module  address  old  new  what the mutation is
# (elf is a path under the repository; old/new are a 32-bit word, or a
# 16-bit halfword written with 4 hex digits, for compressed code)
mutations=(
  "sum Examples.Sum 0x1119c 0x00c68633 0x40c68633 add-a2-becomes-sub"
  "sum Examples.Sum 0x111a4 0x00850513 0x00450513 stride-8-becomes-4"
  "sum Examples.Sum 0x111a8 0xfe0598e3 0xfe0588e3 bne-becomes-beq"
  "sum Examples.Sum 0x11190 0x00000613 0x00100613 sum-starts-at-1"
  "sum Examples.Sum 0x11198 0x00053683 0x00052683 ld-becomes-lw"
  "sum Examples.Sum2 0x111ec 0x01250533 0x41250533 sum2-add-becomes-sub"
  "sum Examples.Sum2 0x111c8 0x00068413 0x00060413 sum2-keeps-the-wrong-length"
  "sum Examples.Sum2 0x111f4 0x01013403 0x00813403 sum2-restores-s0-from-the-wrong-slot"
  "sum Examples.Sum2 0x11200 0x02010113 0x01010113 sum2-frees-16-of-32-bytes"
  "sum Examples.Sum2 0x111e8 0xfac080e7 0xfb0080e7 sum2-calls-past-the-entry"
  "hello Examples.Hello 0x11180 0xfe0556e3 0xfe0546e3 write_all-loops-on-errors"
  "hello Examples.Hello 0x1117c 0x40a60633 0x00a60633 write_all-adds-to-the-count"
  "hello Examples.Hello 0x11178 0x00a585b3 0x40a585b3 write_all-moves-buf-backwards"
  "hello Examples.Hello 0x111a4 0x00b00613 0x00a00613 hello-writes-10-bytes"
  "hello Examples.Hello 0x111b0 0x03f55513 0x03e55513 hello-exit-status-2-on-error"
  # demo/README.md: the same mutations on the e5r build (B) and the ordinary build (A).
  "demo/elf/sum.b Demo.SumB 0x1119c 0x00c68633 0x40c68633 demo-B-sum-add-becomes-sub"
  "demo/elf/sum.b Demo.SumB 0x111a4 0x00850513 0x00450513 demo-B-sum-stride-8-becomes-4"
  "demo/elf/sum.a Demo.SumA 0x11196 0x9636 0x8e15 demo-A-sum-add-becomes-sub"
  "demo/elf/sum.a Demo.SumA 0x1119a 0x0521 0x0511 demo-A-sum-stride-8-becomes-4"
  "demo/elf/cobs.b Demo.CobsB 0x111c8 0x00158713 0x00258713 demo-B-cobs-copies-from-one-byte-late"
  "demo/elf/cobs.b Demo.CobsB 0x1124c 0x00053023 0x00f53023 demo-B-cobs-success-tag-is-src"
  "demo/elf/cobs.b Demo.CobsB 0x11244 0x00080023 0x00b80023 demo-B-cobs-decodes-nonzero-separator"
  "demo/elf/cobs.a Demo.CobsA 0x111ae 0x00158813 0x00258813 demo-A-cobs-copies-from-one-byte-late"
  "demo/elf/cobs.a Demo.CobsA 0x1121c 0x00053023 0x00553023 demo-A-cobs-success-tag-is-src"
  "demo/elf/cobs.a Demo.CobsA 0x11208 0x00068023 0x00b68023 demo-A-cobs-decodes-nonzero-separator"
)

cp -r lean "$work/lean"
mkdir -p "$work/demo" && cp -r demo/tools "$work/demo/tools"
# The functions of a compressed demo binary that its image lists (as demo/run.sh exports them).
demo_funcs() { llvm-nm --print-size "$1" | awk '$3 == "T" && $4 != "_start" { printf "%s:%d:%d ", $4, strtonum("0x"$1), strtonum("0x"$2) }'; }
fail=0
run() { (cd "$work/lean" && timeout 900 lake build "$1" > "$work/log" 2>&1); }

for m in "${mutations[@]}"; do
  read -r name mod addr old new what <<< "$m"
  case "$name" in */*) src="$name.elf" ;; *) src="examples/elf/$name.elf" ;; esac
  base=$(basename "$name")
  python3 -I - "$src" "$work/$base.elf" "$addr" "$old" "$new" <<'PY'
import struct, sys
src, dst, addr = sys.argv[1], sys.argv[2], int(sys.argv[3], 16)
fmt = '<H' if len(sys.argv[4]) == 6 else '<I'
old, new = int(sys.argv[4], 16), int(sys.argv[5], 16)
b = bytearray(open(src, 'rb').read())
shoff, = struct.unpack_from('<Q', b, 40); shentsize, shnum, shstrndx = struct.unpack_from('<HHH', b, 58)
def sh(i): return struct.unpack_from('<IIQQQQ', b, shoff + i * shentsize)
stroff = sh(shstrndx)[4]
for i in range(shnum):
    nm, _, _, a, off, size = sh(i)
    if b[stroff + nm:].split(b'\0')[0] == b'.text':
        o = off + addr - a
        w, = struct.unpack_from(fmt, b, o)
        assert w == old, f'{addr:#x} holds {w:#x}, not {old:#x}'
        struct.pack_into(fmt, b, o, new)
open(dst, 'wb').write(b)
PY
  case "$mod" in
    Demo.*)  # demo/elf/<f>.<a|b>.elf, image Demo/<F>/Image<A|B>.lean
      f=${base%.*}; side=${base##*.}; F=$(echo "$f" | sed -E 's/(^|_)([a-z])/\U\2/g'); S=${side^^}
      img=Demo/$F/Image$S.lean
      if [ "$side" = a ]; then
        (cd "$work/lean" && lake env lean --run ../demo/tools/ExportC.lean "$work/$base.elf" "Demo.$F.ImageA" \
          $(demo_funcs "$work/$base.elf") > "$img")
      else
        "$E5R" export "$work/$base.elf" --namespace "Demo.$F.ImageB" -o "$work/lean/$img" 2>/dev/null
      fi ;;
    *)
      img=Examples/$(echo "$name" | sed -E 's/(^|_)([a-z])/\U\2/g')/Image.lean
      "$E5R" export "$work/$name.elf" --namespace "$mod.Image" -o "$work/lean/$img" 2>/dev/null ;;
  esac
  # The mutated image must itself build: a proof that fails because its
  # image is broken (a failed export) would be no evidence.
  imgmod=$(echo "${img%.lean}" | tr / .)
  if ! run "$imgmod"; then
    echo "FAIL $what: the mutated image $imgmod does not build"; fail=1
  elif run "$mod"; then
    echo "FAIL $what: $mod still checks"; fail=1
  else
    echo "ok   $what: $mod no longer checks"
  fi
  cp "lean/$img" "$work/lean/$img"
done

if run Examples && run Demo; then echo "ok   unpatched: Examples and Demo check"; else echo "FAIL unpatched copy does not build"; cat "$work/log"; fail=1; fi
exit $fail
