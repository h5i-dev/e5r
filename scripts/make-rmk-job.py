#!/usr/bin/env python3
"""Write a runner job whose module list is the import closure of ROOT_MODULE in dependency order (the
runner checks every module from source; model, board and generated image modules are excluded, as the
runner adds them). Image, board, ELF and pinned symbols as in jobs/rmk/rmk-session-fragments.json.

Usage: python3 -I scripts/make-rmk-job.py JOB_ID ROOT_MODULE THEOREM... [--sym ADDR=NAME]...
"""
import json
import os
import re
import sys

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "verification", "rv32")
RUNNER = {"Theories.Hart", "Theories.Platform", "Theories.Logic", "Theories.FlashElf", "Theories.RamElf",
          "Projects.rmk.Elf", "Projects.rmk.ElfFidelity"}
args = sys.argv[1:]
syms = {}
while "--sym" in args:
    i = args.index("--sym")
    a, n = args[i + 1].split("=", 1)
    syms[a] = n
    del args[i:i + 2]
jid, root, thms = args[0], args[1], args[2:]
assert all(re.fullmatch(r"[A-Za-z0-9_.*']+", t) for t in [root, *thms]), "plain names only"
order = []


def visit(m, stack=()):
    if m in order or m in RUNNER or m.startswith(("Theories.Board.", "Lean", "Std")):
        return
    assert m not in stack, f"import cycle at {m}"
    p = os.path.join(ROOT, m.replace(".", "/") + ".lean")
    assert os.path.exists(p), f"missing module {m} ({p})"
    for i in re.findall(r"^import (\S+)", open(p, encoding="utf-8").read(), re.M):
        visit(i, stack + (m,))
    order.append(m)


visit(root)
base = json.load(open(os.path.join(ROOT, "jobs/rmk/rmk-session-fragments.json")))
job = {k: base[k] for k in ("schema", "root", "board", "elf", "elf_sha256", "image")}
job.update(id=jid, modules=[m.replace(".", "/") + ".lean" for m in order], theorems=thms,
           symbols=syms, limits=base["limits"])
out = os.path.join(ROOT, "jobs/rmk", jid + ".json")
json.dump(job, open(out, "w"), indent=2)
open(out, "a").write("\n")
print(out, len(order), "modules")
