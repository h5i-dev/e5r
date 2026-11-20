#!/usr/bin/env bash
# Negative controls for the module audit (docs/isa/v1.md, criteria 3 and 6):
# a relinked binary whose bytes are not the module linked at its own layout
# must fail nocompiler-audit. Each mutation patches a copy of one committed
# ELF in a scratch root and requires the audit to fail on it, with the
# expected reason; then the unpatched copy must pass.
#
#   scripts/core/check-audit-controls.sh        (needs lake; builds nocompiler-audit)
set -euo pipefail
cd "$(dirname "$0")/../.."
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
(cd lean && lake build nocompiler-audit >/dev/null)
audit="$PWD/lean/.lake/build/bin/nocompiler-audit"

# elf  kind  where  what it breaks  reason expected in the audit's output
#   word ADDR OLD NEW : a .text word (32-bit, little-endian)
#   sym NAME DELTA    : a function symbol's value
#   data ADDR XOR     : a data byte
mutations=(
  "examples/elf/sum.link2.elf|word 0x4007c 0x038080e7 0x03c080e7|sum2's first call lands 4 bytes past sum|is not its .text"
  "examples/elf/sum.link1.elf|word 0x111d4 0xfc0080e7 0xfc4080e7|sum2's first call lands 4 bytes past sum|is not its .text"
  "examples/elf/sum.link1.elf|word 0x11218 0x00001417 0x00002417|_start's data address is a page off|is not its .text"
  "examples/elf/sum.link2.elf|sym sum 4|the symbol table moves sum by 4|the layout is not the ELF's"
  "examples/elf/sum.link1.elf|data 0x12268 0x01|a byte of .data changes|is not its data sections"
)

fail=0
for m in "${mutations[@]}"; do
  IFS='|' read -r elf what desc reason <<< "$m"
  rm -rf "$work/root"; mkdir -p "$work/root/examples"
  cp -r examples/elf "$work/root/examples/elf"; mkdir -p "$work/root/examples/demo"; cp -r examples/demo/elf "$work/root/examples/demo/elf"
  python3 -I - "$work/root/$elf" $what <<'PY'
import struct, sys
path, kind = sys.argv[1], sys.argv[2]
b = bytearray(open(path, 'rb').read())
shoff, = struct.unpack_from('<Q', b, 40); shentsize, shnum, shstrndx = struct.unpack_from('<HHH', b, 58)
secs = [struct.unpack_from('<IIQQQQIIQQ', b, shoff + i * shentsize) for i in range(shnum)]
stroff = secs[shstrndx][4]
name = lambda s: b[stroff + s[0]:].split(b'\0')[0].decode()
def at(addr):
    for s in secs:
        if s[1] != 8 and s[3] <= addr < s[3] + s[5]: return s[4] + addr - s[3]
    raise SystemExit(f'{addr:#x} is in no section')
if kind == 'word':
    a, old, new = (int(x, 16) for x in sys.argv[3:6]); o = at(a)
    w, = struct.unpack_from('<I', b, o); assert w == old, f'{a:#x} holds {w:#x}, not {old:#x}'
    struct.pack_into('<I', b, o, new)
elif kind == 'sym':
    sym, delta = sys.argv[3], int(sys.argv[4])
    st = next(s for s in secs if s[1] == 2); strtab = secs[st[6]][4]
    for k in range(st[5] // 24):
        o = st[4] + 24 * k; nm, = struct.unpack_from('<I', b, o)
        if b[strtab + nm:].split(b'\0')[0].decode() == sym:
            v, = struct.unpack_from('<Q', b, o + 8); struct.pack_into('<Q', b, o + 8, v + delta); break
    else: raise SystemExit(f'no symbol {sym}')
elif kind == 'data':
    a, x = int(sys.argv[3], 16), int(sys.argv[4], 16); b[at(a)] ^= x
open(path, 'wb').write(b)
PY
  if out=$("$audit" "$work/root" 2>&1); then
    echo "FAIL $desc: the audit still passes"; fail=1
  elif grep -q "FAIL $elf: .*$reason" <<< "$out"; then
    echo "ok   $desc: $(grep "FAIL $elf" <<< "$out" | head -1)"
  else
    echo "FAIL $desc: the audit fails, but not for '$reason':"; grep FAIL <<< "$out"; fail=1
  fi
done
rm -rf "$work/root"; mkdir -p "$work/root/examples"
cp -r examples/elf "$work/root/examples/elf"; mkdir -p "$work/root/examples/demo"; cp -r examples/demo/elf "$work/root/examples/demo/elf"
if "$audit" "$work/root" >/dev/null; then echo "ok   unpatched: the audit passes"; else echo "FAIL unpatched copy"; fail=1; fi
exit $fail
