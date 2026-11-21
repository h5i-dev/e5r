#!/usr/bin/env python3
"""Proof-checking cost per instruction on fixed functions, against a budget (CI gate).

    python3 -I scripts/core/bench-gate.py [--record] [--budget FILE]

For each entry of FIXED (a committed proof file and the functions it proves),
checks the file with `lake env lean -Dprofiler=true` from lean/ (its
dependencies built first, untimed) and reads Lean's cumulative profile:
  kernel  "type checking" (the kernel checking the declarations);
  total   every category of the profile (elaboration, tactics, simp, kernel, ...).
Instructions are the functions' lengths as their images record them
(`<f>_func : Struct.Func := ⟨entry, LEN, ...⟩`). Reports total and kernel
milliseconds per instruction, and wall-clock seconds.

With --record, writes the measured values times MARGIN as the budget
(scripts/core/bench-budget.json). Without, fails (exit 1) if any entry's total
or kernel ms per instruction is over its budget. The budget is meant to come
down as the proof machinery gets faster: re-record and commit it then.
"""
import json, os, re, subprocess, sys, time

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))
LEAN = os.path.join(ROOT, "lean")
BUDGET = os.path.join(ROOT, "scripts", "core", "bench-budget.json")
MARGIN = 3.0  # measured here x3: CI runners are slower than the development host, and noisy

# file (relative to lean/), module, image file, functions proved
FIXED = [
    ("Demo/SumB.lean", "Demo.SumB", "Demo/Sum/ImageB.lean", ["sum"]),
    ("Demo/CobsB.lean", "Demo.CobsB", "Demo/Cobs/ImageB.lean", ["cobs_decode"]),
    ("Demo/Sum2B.lean", "Demo.Sum2B", "Demo/Sum/ImageB.lean", ["sum2"]),
    ("Examples/Hello.lean", "Examples.Hello", "Examples/Hello/Image.lean", ["write_all", "hello"]),
]

UNIT = {"ns": 1e-6, "us": 1e-3, "μs": 1e-3, "ms": 1.0, "s": 1000.0}


def capped(cmd):
    """`cmd` under a memory cap (6 GB, no swap, 900 s) where systemd-run works
    (the shared development host); as is elsewhere (CI runners)."""
    probe = subprocess.run(["systemd-run", "--user", "--scope", "--quiet", "-p", "MemoryMax=64M", "true"],
                           capture_output=True) if os.path.exists("/usr/bin/systemd-run") else None
    if probe is None or probe.returncode != 0:
        return ["timeout", "900"] + cmd
    env = [f"--setenv=PATH={os.environ.get('PATH', '')}"]
    if "ELAN_HOME" in os.environ:
        env.append(f"--setenv=ELAN_HOME={os.environ['ELAN_HOME']}")
    return ["systemd-run", "--user", "--scope", "--quiet", "-p", "MemoryMax=6G", "-p", "MemorySwapMax=0"] + env + \
        ["timeout", "900"] + cmd


def instrs(image, funcs):
    src = open(os.path.join(LEAN, image)).read()
    n = 0
    for f in funcs:
        m = re.search(rf"def {re.escape(f)}_func : Struct\.Func := ⟨0x[0-9a-f]+#64, (\d+),", src)
        if not m:
            sys.exit(f"bench-gate: no {f}_func in {image}")
        n += int(m.group(1))
    return n


def profile(text):
    """Cumulative profile categories, in milliseconds."""
    out = {}
    block = text.split("cumulative profiling times:")[-1]
    for m in re.finditer(r"^\s+(.+?) ([\d.]+)(ns|us|μs|ms|s)$", block, re.M):
        out[m.group(1)] = float(m.group(2)) * UNIT[m.group(3)]
    return out


def measure(path, module, image, funcs):
    deps = subprocess.run(capped(["lake", "build", module]), cwd=LEAN, capture_output=True, text=True)
    if deps.returncode != 0:
        sys.exit(f"bench-gate: lake build {module} failed:\n{deps.stdout[-2000:]}")
    t0 = time.monotonic()
    r = subprocess.run(capped(["lake", "env", "lean", "-Dprofiler=true", path]), cwd=LEAN, capture_output=True, text=True)
    wall = time.monotonic() - t0
    if r.returncode != 0:
        sys.exit(f"bench-gate: {path} does not check:\n{(r.stdout + r.stderr)[-2000:]}")
    p = profile(r.stdout + r.stderr)
    n = instrs(image, funcs)
    total = sum(p.values())
    kernel = p.get("type checking", 0.0)
    return {"instrs": n, "wall_s": round(wall, 2), "total_ms": round(total, 1), "kernel_ms": round(kernel, 1),
            "total_ms_per_instr": round(total / n, 2), "kernel_ms_per_instr": round(kernel / n, 2)}


def main():
    record = "--record" in sys.argv
    if "--budget" in sys.argv:
        global BUDGET
        BUDGET = sys.argv[sys.argv.index("--budget") + 1]
    rows = {path: measure(path, mod, img, fs) for path, mod, img, fs in FIXED}
    print("| file | instructions | wall (s) | total (ms) | kernel (ms) | total ms/instr | kernel ms/instr |")
    print("| --- | --- | --- | --- | --- | --- | --- |")
    for path, r in rows.items():
        print(f"| {path} | {r['instrs']} | {r['wall_s']} | {r['total_ms']} | {r['kernel_ms']} | "
              f"{r['total_ms_per_instr']} | {r['kernel_ms_per_instr']} |")
    if record:
        budget = {p: {"total_ms_per_instr": round(r["total_ms_per_instr"] * MARGIN, 2),
                      "kernel_ms_per_instr": round(r["kernel_ms_per_instr"] * MARGIN, 2)} for p, r in rows.items()}
        with open(BUDGET, "w") as f:
            json.dump(budget, f, indent=2, sort_keys=True)
            f.write("\n")
        print(f"recorded the budget (x{MARGIN}) in {BUDGET}")
        return 0
    budget = json.load(open(BUDGET))
    bad = []
    for path, r in rows.items():
        b = budget.get(path)
        if b is None:
            bad.append(f"{path}: no budget")
            continue
        for k in ("total_ms_per_instr", "kernel_ms_per_instr"):
            if r[k] > b[k]:
                bad.append(f"{path}: {k} {r[k]} over the budget {b[k]}")
    for b in bad:
        print("FAIL " + b)
    if not bad:
        print("ok   every fixed proof within its budget")
    return 1 if bad else 0


sys.exit(main())
