#!/usr/bin/env python3
"""Proof-checking cost per instruction on fixed functions, against a budget (CI gate).

    python3 -I scripts/core/bench-gate.py [--record | --record-from-ci RUN] [--budget FILE]

For each entry of FIXED (a committed proof file and the functions it proves),
checks the file with `lake env lean -Dprofiler=true` from lean/ (its
dependencies built first, untimed) and reads Lean's cumulative profile:
  kernel  "type checking" (the kernel checking the declarations);
  total   every category of the profile (elaboration, tactics, simp, kernel, ...).
Instructions are the functions' lengths as their images record them
(`<f>_func : Struct.Func := ⟨entry, LEN, ...⟩`). Reports total and kernel
milliseconds per instruction, and wall-clock seconds.

With --record, writes the measured values times MARGIN as the budget
(scripts/core/bench-budget.json); with --record-from-ci RUN, the values a CI
run measured (printed there as annotations), which is how the committed budget
is recorded: CI runners are load-free, the shared development host is not. Without, fails (exit 1) if any entry's total
or kernel ms per instruction is over its budget. The budget is meant to come
down as the proof machinery gets faster: re-record and commit it then.
"""
import json, os, re, subprocess, sys, time

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))
LEAN = os.path.join(ROOT, "lean")
BUDGET = os.path.join(ROOT, "scripts", "core", "bench-budget.json")
MARGIN = 3.0  # measured here x3: CI runners are slower than the development host, and noisy

# file (relative to lean/), module, image file, functions proved. The proofs
# are on images in chunks (`nocompiler export --format chunks`, the format that
# scales to a whole binary): Examples/Chunks/ holds the same proofs as
# Demo/SumB.lean, Demo/CobsB.lean, Demo/Sum2B.lean and Examples/Hello.lean,
# which are on images with a lemma per instruction.
FIXED = [
    ("Examples/Chunks/SumB.lean", "Examples.Chunks.SumB", "Examples/Chunks/SumBImage.lean", ["sum"]),
    ("Examples/Chunks/CobsB.lean", "Examples.Chunks.CobsB", "Examples/Chunks/CobsImage.lean", ["cobs_decode"]),
    ("Examples/Chunks/Sum2B.lean", "Examples.Chunks.Sum2B", "Examples/Chunks/SumBImage.lean", ["sum2"]),
    ("Examples/Chunks/Hello.lean", "Examples.Chunks.Hello", "Examples/Chunks/HelloImage.lean",
     ["write_all", "hello"]),
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


# Generated benchmarks of the reflective VC generator (lean/NoCompiler/VC/Bench/Gen.py):
# name, Gen.py arguments, the module to build first, instructions.
GENERATED = [
    ("VC/MemChk1000", ["memchk", "1000"], "NoCompiler.VC.Ob", 1000),
]


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
    n = funcs if image is None else instrs(image, funcs)
    total = sum(p.values())
    kernel = p.get("type checking", 0.0)
    return {"instrs": n, "wall_s": round(wall, 2), "total_ms": round(total, 1), "kernel_ms": round(kernel, 1),
            "total_ms_per_instr": round(total / n, 2), "kernel_ms_per_instr": round(kernel / n, 2)}


def record_from_ci(run):
    """The budget from CI run RUN's measurements (its `core` job's bench-gate
    annotations), times MARGIN: CI runners are load-free, the shared
    development host is not, so the budget is recorded from CI only."""
    import urllib.request
    url = subprocess.run(["git", "remote", "get-url", "origin"], cwd=ROOT, capture_output=True, text=True,
                         check=True).stdout.strip()
    repo = re.sub(r"(\.git)?$", "", re.split(r"github\.com[:/]", url)[1])
    api = f"https://api.github.com/repos/{repo}"
    get = lambda u: json.load(urllib.request.urlopen(urllib.request.Request(u, headers={"User-Agent": "bench-gate"})))
    jobs = get(f"{api}/actions/runs/{run}/jobs?per_page=100")["jobs"]
    job = next(j for j in jobs if j["name"] == "core")
    if job["conclusion"] != "success":
        sys.exit(f"bench-gate: run {run}'s core job did not succeed ({job['conclusion']})")
    budget = {}
    for a in get(f"{api}/check-runs/{job['id']}/annotations?per_page=100"):
        m = re.match(r"(\S+) total_ms_per_instr=([\d.]+) kernel_ms_per_instr=([\d.]+)$", a["message"])
        if a["title"] == "bench-gate" and m:
            budget[m.group(1)] = {"total_ms_per_instr": round(float(m.group(2)) * MARGIN, 2),
                                  "kernel_ms_per_instr": round(float(m.group(3)) * MARGIN, 2)}
    want = {f for f, _, _, _ in FIXED} | {n for n, _, _, _ in GENERATED}
    if set(budget) != want:
        sys.exit(f"bench-gate: run {run} measured {sorted(budget)}, the gate has {sorted(want)}")
    with open(BUDGET, "w") as f:
        json.dump(budget, f, indent=2, sort_keys=True)
        f.write("\n")
    print(f"recorded the budget (x{MARGIN}) from CI run {run} (job {job['id']}, {job['head_sha']}) in {BUDGET}")
    return 0


def main():
    if "--record-from-ci" in sys.argv:
        return record_from_ci(sys.argv[sys.argv.index("--record-from-ci") + 1])
    record = "--record" in sys.argv
    if "--budget" in sys.argv:
        global BUDGET
        BUDGET = sys.argv[sys.argv.index("--budget") + 1]
    rows = {path: measure(path, mod, img, fs) for path, mod, img, fs in FIXED}
    import tempfile
    gen = tempfile.mkdtemp(prefix="bench-gate-")
    for name, args, mod, n in GENERATED:
        subprocess.run(["python3", "-I", os.path.join(LEAN, "NoCompiler", "VC", "Bench", "Gen.py"), gen] + args,
                       check=True)
        f = os.path.join(gen, os.path.basename(name).replace("VC/", "") + ".lean")
        rows[name] = measure(f, mod, None, n)
    print("| file | instructions | wall (s) | total (ms) | kernel (ms) | total ms/instr | kernel ms/instr |")
    print("| --- | --- | --- | --- | --- | --- | --- |")
    for path, r in rows.items():
        print(f"| {path} | {r['instrs']} | {r['wall_s']} | {r['total_ms']} | {r['kernel_ms']} | "
              f"{r['total_ms_per_instr']} | {r['kernel_ms_per_instr']} |")
    if os.environ.get("GITHUB_ACTIONS") == "true":
        # The measured values as annotations, which the API serves without a
        # token: `--record-from-ci RUN` records the budget from them.
        for path, r in rows.items():
            print(f"::notice title=bench-gate::{path} total_ms_per_instr={r['total_ms_per_instr']} "
                  f"kernel_ms_per_instr={r['kernel_ms_per_instr']}")
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
