#!/usr/bin/env python3
"""Merge the memmove matrix shard logs (matrix.sh OUT_DIR) into one summary.

Usage: python3 -I verification/rv32/rmk-audit/summarize_matrix.py OUT_DIR

Prints, per path class (n<16 / n>=16, src≡dst mod 4 or not, placement), the
number of runs and the distinct sets of changed frame bytes (offsets from
the caller's sp), then the totals, the failures (FAIL lines, with all case
parameters) and the controls. Exit status 0 only if there is no failure and
every control was detected.
"""
import collections
import glob
import os
import re
import sys

out = sys.argv[1]
runs, sets = collections.Counter(), collections.defaultdict(set)
total = steps = fails = 0
failures = []
for path in sorted(glob.glob(os.path.join(out, "shard-*.log"))):
    for line in open(path):
        m = re.match(r"class \[(.*)\] (\d+) runs; changed frame offsets \(distinct sets\): (.*)$", line)
        if m:
            runs[m.group(1)] += int(m.group(2))
            for s in re.findall(r"\[([-\d, ]*)\]", m.group(3)):
                sets[m.group(1)].add(tuple(int(x) for x in s.split(",") if x.strip()))
        m = re.match(r"shard \d+/\d+: (\d+) runs, (\d+) failures, (\d+) model steps", line)
        if m:
            total += int(m.group(1)); fails += int(m.group(2)); steps += int(m.group(3))
        if line.startswith("FAIL"):
            failures.append(line.rstrip())
bounds = open(os.path.join(out, "bounds.log")).read()
controls = open(os.path.join(out, "controls.log")).read()
for line in bounds.splitlines():
    if line.startswith("FAIL"):
        failures.append(line)


def fmt(t):
    if not t:
        return "none"
    out, i = [], 0
    while i < len(t):
        j = i
        while j + 1 < len(t) and t[j + 1] == t[j] + 1:
            j += 1
        out.append(f"{t[i]}" if i == j else f"{t[i]}..{t[j]}")
        i = j + 1
    return ", ".join(out)


print(f"{'class':45} {'runs':>6}  changed frame bytes (offset from caller sp)")
for c in sorted(runs):
    print(f"{c:45} {runs[c]:>6}  " + " | ".join(fmt(s) for s in sorted(sets[c])))
print(f"\nmain matrix: {total} runs, {fails} failures, {steps} model steps")
print(next((l for l in bounds.splitlines() if l.startswith("bounds:")), "bounds: not completed"))
print("\n" + controls.strip())
print(f"\nfailures: {len(failures)}")
for f in failures[:50]:
    print(f)
blind = "NOT DETECTED" in controls
sys.exit(0 if not failures and not blind else 1)
