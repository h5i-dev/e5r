#!/bin/bash
# Fresh, module-by-module build of main's Rx chain (no copied .lake).
cd "${1:?main rv32 dir}" || exit 1
O=.lake/build/lib/lean
for m in $(cat "${2:?module order file}"); do
  f=${m//.//}.lean; mkdir -p $O/$(dirname $f)
  st=$(date +%s)
  lake env lean $f -o $O/${f%.lean}.olean > /dev/shm/build_$$.log 2>&1 || { echo "FAIL $m"; grep error /dev/shm/build_$$.log | head -5; exit 1; }
  grep -q " error" /dev/shm/build_$$.log && { echo "ERR $m"; exit 1; }
  echo "ok $m $(( $(date +%s)-st ))s"
done
echo BUILD-DONE
