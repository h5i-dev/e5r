#!/usr/bin/env bash
# G5: same bytes, same output, any thread count.
#
# Runs the CLI over every fixture at 1, 4 and 10 threads, twice each, and
# compares output hashes. A mismatch means analysis is reading a work-queue
# order it should not be able to see.
set -euo pipefail
cd "$(dirname "$0")/.."

bin=target/release/r12e
[ -x "$bin" ] || { echo "build first: cargo build --release" >&2; exit 2; }

shopt -s nullglob
fixtures=(fixtures/build/*)
[ ${#fixtures[@]} -gt 0 ] || { echo "no fixtures; run scripts/build-fixtures.sh" >&2; exit 2; }

fail=0
for f in "${fixtures[@]}"; do
  [ -f "$f" ] || continue
  ref=""
  for threads in 1 4 10; do
    for _ in 1 2; do
      got=$("$bin" funcs --json --threads "$threads" "$f" 2>/dev/null | sha256sum | cut -d' ' -f1)
      if [ -z "$ref" ]; then
        ref="$got"
      elif [ "$got" != "$ref" ]; then
        echo "FAIL $f: threads=$threads gave $got, expected $ref"
        fail=1
      fi
    done
  done
  [ "$fail" -eq 0 ] && echo "ok   $f  $ref"
done
exit "$fail"
