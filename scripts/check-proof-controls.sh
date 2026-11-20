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

# elf  module  address  old-word  new-word  what the mutation is
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
)

cp -r lean "$work/lean"
fail=0
run() { (cd "$work/lean" && timeout 900 lake build "$1" > "$work/log" 2>&1); }

for m in "${mutations[@]}"; do
  read -r name mod addr old new what <<< "$m"
  python3 -I - "examples/elf/$name.elf" "$work/$name.elf" "$addr" "$old" "$new" <<'PY'
import struct, sys
src, dst, addr, old, new = sys.argv[1], sys.argv[2], int(sys.argv[3], 16), int(sys.argv[4], 16), int(sys.argv[5], 16)
b = bytearray(open(src, 'rb').read())
shoff, = struct.unpack_from('<Q', b, 40); shentsize, shnum, shstrndx = struct.unpack_from('<HHH', b, 58)
def sh(i): return struct.unpack_from('<IIQQQQ', b, shoff + i * shentsize)
stroff = sh(shstrndx)[4]
for i in range(shnum):
    nm, _, _, a, off, size = sh(i)
    if b[stroff + nm:].split(b'\0')[0] == b'.text':
        o = off + addr - a
        w, = struct.unpack_from('<I', b, o)
        assert w == old, f'{addr:#x} holds {w:#010x}, not {old:#010x}'
        struct.pack_into('<I', b, o, new)
open(dst, 'wb').write(b)
PY
  img=Examples/$(echo "$name" | sed -E 's/(^|_)([a-z])/\U\2/g')/Image.lean
  "$E5R" export "$work/$name.elf" --namespace "$mod.Image" -o "$work/lean/$img" 2>/dev/null
  if run "$mod"; then
    echo "FAIL $what: $mod still checks"; fail=1
  else
    echo "ok   $what: $mod no longer checks"
  fi
  cp "lean/$img" "$work/lean/$img"
done

if run Examples; then echo "ok   unpatched: Examples checks"; else echo "FAIL unpatched copy does not build"; cat "$work/log"; fail=1; fi
exit $fail
