#!/usr/bin/env bash
# Function recovery measured against Ghidra on the same binary.
#
# Not a test: it needs a JVM, a Ghidra installation and about twenty seconds
# per binary. It is the comparison the roadmap claims to beat, so it is run by
# hand and its numbers are recorded in docs/scorecard.md.
#
# Usage: scripts/compare-ghidra.sh <binary> [more binaries...]
set -euo pipefail

# A fresh project each run: importing into an existing one is a no-op and
# would report the previous analysis as if it were this one.
project=${PROJECT:-r12ecompare-$$}
r12e=${R12E:-target/release/r12e}
ghidra=${GHIDRA:-ghidra}

command -v "$ghidra" > /dev/null || {
  echo "no ghidra CLI on PATH" >&2
  exit 1
}
[ -x "$r12e" ] || {
  echo "build first: cargo build --release" >&2
  exit 1
}

printf '%-28s %8s %8s %8s %8s %9s %9s\n' \
  binary ghidra r12e both only-g only-r12e r12e-time

for binary in "$@"; do
  name=$(basename "$binary")
  start=$(date +%s.%N)
  "$ghidra" import "$binary" --project "$project" > /dev/null 2>&1 || true
  gtime=$(echo "$(date +%s.%N) - $start" | bc)

  # Ghidra puts imported functions in a synthetic block past the end of the
  # file; those are not functions in the binary and are not counted.
  limit=$("$r12e" sections "$binary" --json 2>/dev/null | python3 -c 'import json,sys
data = json.load(sys.stdin)
ends = [int(s["addr"], 16) + int(s["size"], 16) for s in data["items"] if int(s["addr"], 16)]
print(max(ends) if ends else 0)')

  "$ghidra" query functions --project "$project" --program "$name" --json --limit 0 2>/dev/null \
    | python3 -c "import json,sys
try:
    data = json.load(sys.stdin)
except Exception:
    data = []
for f in data:
    a = int(f['entry_point'], 16)
    if a < $limit:
        print(a)" | sort -u > /tmp/ghidra-functions.txt

  start=$(date +%s.%N)
  "$r12e" funcs "$binary" --json 2>/dev/null \
    | python3 -c 'import json,sys
data = json.load(sys.stdin)
for f in data["items"]:
    print(int(f["addr"], 16))' | sort -u > /tmp/r12e-functions.txt
  rtime=$(echo "$(date +%s.%N) - $start" | bc)

  g=$(wc -l < /tmp/ghidra-functions.txt)
  r=$(wc -l < /tmp/r12e-functions.txt)
  both=$(comm -12 /tmp/ghidra-functions.txt /tmp/r12e-functions.txt | wc -l)
  only_g=$(comm -23 /tmp/ghidra-functions.txt /tmp/r12e-functions.txt | wc -l)
  only_r=$(comm -13 /tmp/ghidra-functions.txt /tmp/r12e-functions.txt | wc -l)

  printf '%-28s %8s %8s %8s %8s %9s %8.3fs\n' \
    "$name" "$g" "$r" "$both" "$only_g" "$only_r" "$rtime"
  if [ -n "${VERBOSE:-}" ]; then
    echo "  ghidra analysis took ${gtime}s"
    echo "  only ghidra: $(comm -23 /tmp/ghidra-functions.txt /tmp/r12e-functions.txt | head -5 | tr '\n' ' ')"
    echo "  only r12e:   $(comm -13 /tmp/ghidra-functions.txt /tmp/r12e-functions.txt | head -5 | tr '\n' ' ')"
  fi
done
