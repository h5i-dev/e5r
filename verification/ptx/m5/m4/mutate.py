#!/usr/bin/env python3
"""Random mechanical mutants of M4 kernels, for bugs nobody chose.

A seeded generator picks a kernel, an instruction and one of four operators
(replace a register operand by another register of the same kind used in
the kernel, flip a comparison, change an integer immediate, delete the
instruction) and keeps the mutant if ptxas assembles it. Nobody looks at a
mutant before it is checked; some are equivalent to the original, which the
GPU test shows. Writes mutants.json for `run4.py --mutants`.

  mutate.py COUNT SEED
"""
import json
import os
import random
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
CUDA = os.environ.get("CUDA_HOME", "/usr/local/cuda")
BASES = ["r_div2", "a_tree", "s_hs"]
CMP = {"ge": "gt", "gt": "ge", "lt": "le", "le": "lt", "eq": "ne", "ne": "eq"}


def body_lines(lines):
    out = []
    inside = False
    for i, l in enumerate(lines):
        if l.strip() == "{":
            inside = True
            continue
        s = l.strip()
        if inside and s and not s.startswith(("//", ".", "$", "}")) and s.endswith(";"):
            out.append(i)
    return out


def mutate(rng, text):
    lines = text.split("\n")
    idx = body_lines(lines)
    regs = sorted(set(re.findall(r"%r\d+", text)))
    rds = sorted(set(re.findall(r"%rd\d+", text)))
    for _ in range(100):
        i = rng.choice(idx)
        l = lines[i]
        op = rng.choice(["reg", "cmp", "imm", "del"])
        if op == "del":
            if "ret;" in l:
                continue
            new, what = None, f"delete `{l.strip()}`"
        elif op == "cmp":
            m = re.search(r"setp\.(\w+)\.", l)
            if not m or m.group(1) not in CMP:
                continue
            new = l.replace(f"setp.{m.group(1)}.", f"setp.{CMP[m.group(1)]}.", 1)
            what = f"`{l.strip()}` -> {CMP[m.group(1)]}"
        elif op == "imm":
            ms = list(re.finditer(r"(?<=[ ,\t])(\d+)(?=[;,\]])", l))
            if not ms or "bar.sync" in l:
                continue
            m = rng.choice(ms)
            v = int(m.group(1))
            nv = rng.choice([v + 1, max(0, v - 1), v * 2])
            if nv == v:
                continue
            new = l[:m.start()] + str(nv) + l[m.end():]
            what = f"`{l.strip()}`: {v} -> {nv}"
        else:
            ms = list(re.finditer(r"%rd?\d+", l))
            if len(ms) < 2:
                continue
            m = rng.choice(ms[1:])  # a source operand
            pool = rds if m.group(0).startswith("%rd") else regs
            r = rng.choice(pool)
            if r == m.group(0):
                continue
            new = l[:m.start()] + r + l[m.end():]
            what = f"`{l.strip()}`: {m.group(0)} -> {r}"
        out = lines[:i] + ([] if new is None else [new]) + lines[i + 1:]
        return "\n".join(out), what
    raise RuntimeError("no mutation found")


def main():
    count, seed = int(sys.argv[1]), int(sys.argv[2])
    rng = random.Random(seed)
    muts, seen = [], set()
    while len(muts) < count:
        base = rng.choice(BASES)
        src = open(os.path.join(HERE, "kernels", base + ".ptx")).read()
        text, what = mutate(rng, src)
        if text in seen or text == src:
            continue
        p = "/tmp/e5r_mut.ptx"
        open(p, "w").write(text)
        r = subprocess.run([f"{CUDA}/bin/ptxas", "-arch=sm_86", p, "-o", "/tmp/e5r_mut.cubin"],
                           capture_output=True)
        if r.returncode != 0:
            continue
        seen.add(text)
        muts.append({"id": f"mut{len(muts):02d}_{base}", "base": base, "change": what, "ptx": text})
        print(muts[-1]["id"], what)
    json.dump(muts, open(os.path.join(HERE, "mutants.json"), "w"), indent=1)


if __name__ == "__main__":
    main()
