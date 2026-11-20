#!/usr/bin/env python3
"""Conformance of the candidate refinement targets, per crate and level
(spec-v1-refine.md item 7; docs/isa/refine-targets.md).

    python3 -I examples/refine/conformance.py CHECK.json ARCHIVE [--markdown] [--list]

CHECK.json is `nocompiler check --json` of the binary linked from ARCHIVE
(examples/refine/conformance.sh does both). A function is attributed to the
crate whose object in the archive defines its symbol (`llvm-nm -A`); the
`w_*` entry points of examples/refine/targets are counted as `wrappers`.
For each crate: functions at L2, L1, L0 and below (not decoding), and the
rules behind the misses (for L1 the rules L2 needed, for L0 and below the
violations).
"""
import json, re, subprocess, sys
from collections import Counter, defaultdict

check = json.load(open(sys.argv[1]))
archive = sys.argv[2]
md = "--markdown" in sys.argv

owner = {}
out = subprocess.run(["llvm-nm", "-A", "--defined-only", archive], capture_output=True, text=True).stdout
for line in out.splitlines():
    m = re.match(r"[^:]+:([^:]+):\s+\S+\s+[TtWw]\s+(\S+)$", line)
    if not m:
        continue
    member, sym = m.groups()
    crate = member.split("-")[0]
    owner[sym] = crate

rows = defaultdict(Counter)
reasons = defaultdict(Counter)
names = defaultdict(list)
for f in check["functions"]:
    crate = owner.get(f["name"], "?")
    if f["name"].startswith("w_") or f["name"] == "_start":
        crate = "wrappers"
    if crate == "refine_targets":
        crate = "wrappers"
    lvl = f.get("level") or "none"
    rows[crate][lvl] += 1
    names[crate].append((f["name"], lvl))
    if lvl != "L2":
        rs = {v["rule"] for v in f.get("violations", []) + f.get("missed", [])}
        for r in rs:
            reasons[crate][r] += 1

order = sorted(rows, key=lambda c: (c in ("core", "compiler_builtins", "wrappers"), c))
if md:
    print("| crate | functions | L2 | L1 | L0 | below L0 | rules behind the misses (functions) |")
    print("| --- | --- | --- | --- | --- | --- | --- |")
for c in order:
    r = rows[c]
    n = sum(r.values())
    why = ", ".join(f"{k} ({v})" for k, v in reasons[c].most_common())
    if md:
        print(f"| {c} | {n} | {r['L2']} | {r['L1']} | {r['L0']} | {r['none']} | {why} |")
    else:
        print(f"{c:20} {n:5}  L2 {r['L2']:4}  L1 {r['L1']:3}  L0 {r['L0']:4}  none {r['none']:3}  {why}")

if "--list" in sys.argv:
    for c in order:
        if c in ("core", "compiler_builtins"):
            continue
        dm = subprocess.run(["llvm-cxxfilt"], input="\n".join(n for n, _ in names[c]), capture_output=True, text=True).stdout.split("\n")
        print(f"\n{c}:")
        for (n, l), d in sorted(zip(names[c], dm), key=lambda x: (x[0][1], x[1])):
            print(f"  {l:4} {d}")
