#!/usr/bin/env bash
# Measure e5r against what else is on this machine, and print a table.
#
# Wall time and peak RSS from /usr/bin/time, best of three runs, over the
# fixture corpus plus whatever system binaries are present. objdump is the
# comparison that is always available; it only disassembles, which the table
# says, because comparing full analysis against linear disassembly and not
# saying so would be dishonest.
set -euo pipefail
cd "$(dirname "$0")/.."

bin=target/release/e5r
[ -x "$bin" ] || { echo "build first: cargo build --release" >&2; exit 2; }

# Best of three, printed as "seconds KB".
best() {
  local lo="" out
  for _ in 1 2 3; do
    out=$(/usr/bin/time -f "%e %M" "$@" 2>&1 >/dev/null | tail -1)
    if [ -z "$lo" ] || awk "BEGIN{exit !(${out%% *} < ${lo%% *})}"; then lo="$out"; fi
  done
  echo "$lo"
}

targets=()
for f in fixtures/build/hello.a64.O2 fixtures/build/wide.a64.O2.o; do
  [ -f "$f" ] && targets+=("$f")
done
for f in /bin/ls /bin/bash /usr/bin/objdump \
         /usr/lib/aarch64-linux-gnu/libc.so.6 \
         /usr/lib/aarch64-linux-gnu/libstdc++.so.6 \
         /usr/lib/aarch64-linux-gnu/libcrypto.so.3; do
  [ -f "$f" ] && targets+=("$f")
done

printf '%-26s %8s  %18s  %18s  %s\n' \
  "binary" "size" "e5r (analyze)" "objdump (disas)" "functions / complete"
printf '%-26s %8s  %18s  %18s  %s\n' \
  "--------------------------" "--------" "------------------" "------------------" "--------------------"

for f in "${targets[@]}"; do
  size=$(( $(stat -Lc%s "$f") / 1024 ))
  ours=$(best "$bin" stats "$f")
  # objdump aborts on some inputs, which is itself worth recording.
  theirs="crash crash"
  if objdump -d "$f" >/dev/null 2>&1; then
    theirs=$(best objdump -d "$f")
  fi
  counts=$("$bin" stats --json "$f" 2>/dev/null \
    | tr -d ' ",' \
    | awk -F: '/^functions:/{f=$2} /^complete:/{c=$2} END{printf "%s / %s", f, c}')
  if [ "${theirs%% *}" = "crash" ]; then
    printf '%-26s %6sK  %8ss %8sK  %18s  %s\n' \
      "$(basename "$f")" "$size" "${ours%% *}" "${ours##* }" "aborted" "$counts"
  else
    printf '%-26s %6sK  %8ss %8sK  %8ss %8sK  %s\n' \
      "$(basename "$f")" "$size" "${ours%% *}" "${ours##* }" \
      "${theirs%% *}" "${theirs##* }" "$counts"
  fi
done

echo
echo "e5r recovers functions, control flow, cross references and strings."
echo "objdump disassembles linearly and does none of that; it is here because"
echo "it is the one comparison present on every machine."
