#!/usr/bin/env python3
"""The Lean level check over every function of a binary, on its chunk image
(docs/isa/v1-results.md, criterion 7').

    python3 -I scripts/core/bench-chunk-checks.py ELF WORKDIR [--budget N | --largest K] [--json OUT]

Exports ELF with `nocompiler export --format chunks`, then splits the module in
two: the image (everything but the `_checked` theorems), compiled once to an
.olean, and the `_checked` theorems in modules of about N instructions each (default 1000)
that import it. One module holding every check of a large binary does not fit
in the memory cap (6 GB): 685 checks of the 87242-instruction artifact were
OOM-killed after 312 declarations, and memory grows from one check to the next
in a module. Each module is elaborated on its own, one after another, under the
cap (bench-gate.py's `capped`), with -Dprofiler=true; one the cap or the
timeout kills is split in two and retried, down to a single function, whose
kill is then its failure.
Reports per module and in total: wall, peak memory, kernel time, instructions,
and every function whose check fails, with Lean's message.
NOCOMPILER names the binary (default target/release/nocompiler).
"""
import json, os, re, subprocess, sys, time

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))
LEAN = os.path.join(ROOT, "lean")
NOCOMPILER = os.environ.get("NOCOMPILER", os.path.join(ROOT, "target", "release", "nocompiler"))
UNIT = {"ns": 1e-6, "us": 1e-3, "μs": 1e-3, "ms": 1.0, "s": 1000.0}
NS = "Whole.T"


def capped(cmd):
    probe = subprocess.run(["systemd-run", "--user", "--scope", "--quiet", "-p", "MemoryMax=64M", "true"],
                           capture_output=True) if os.path.exists("/usr/bin/systemd-run") else None
    if probe is None or probe.returncode != 0:
        return ["timeout", "900"] + cmd
    env = [f"--setenv={k}={os.environ[k]}" for k in ("PATH", "ELAN_HOME", "LEAN_PATH") if k in os.environ]
    return ["systemd-run", "--user", "--scope", "--quiet", "-p", "MemoryMax=6G", "-p", "MemorySwapMax=0"] + env + \
        ["timeout", "900"] + cmd


def lean(work, args):
    """`lake env lean ARGS` from lean/, capped, timed; with WORK on the module path."""
    out = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=LEAN, capture_output=True, text=True,
                         check=True).stdout.strip()
    os.environ["LEAN_PATH"] = work + ":" + out
    env = dict(os.environ)
    t0 = time.monotonic()
    r = subprocess.run(capped(["/usr/bin/time", "-f", "PEAK %M KB", "lean"] + args), cwd=LEAN, env=env,
                       capture_output=True, text=True)
    wall = time.monotonic() - t0
    text = r.stdout + r.stderr
    m = re.findall(r"PEAK (\d+) KB", text)
    kernel = 0.0
    block = text.split("cumulative profiling times:")[-1] if "cumulative profiling times:" in text else ""
    for mm in re.finditer(r"^\s+type checking ([\d.]+)(ns|us|μs|ms|s)$", block, re.M):
        kernel = float(mm.group(1)) * UNIT[mm.group(2)]
    return {"rc": r.returncode, "wall_s": round(wall, 2), "peak_kb": int(m[-1]) if m else None,
            "kernel_ms": round(kernel, 1), "text": text}


def main():
    elf, work = sys.argv[1], os.path.abspath(sys.argv[2])
    budget = int(sys.argv[sys.argv.index("--budget") + 1]) if "--budget" in sys.argv else 1000
    d = os.path.join(work, *NS.split(".")[:-1])
    os.makedirs(d, exist_ok=True)
    t0 = time.monotonic()
    src = subprocess.run([NOCOMPILER, "export", "--lean-level-check", "--format", "chunks", "--namespace", NS, elf],
                         capture_output=True, text=True, check=True).stdout
    export_s = round(time.monotonic() - t0, 2)
    lines = src.splitlines()
    checked, image = [], []
    for l in lines:
        if re.match(r"theorem \S+_checked :", l):
            doc = image.pop() + "\n" if image and image[-1].startswith("/--") else ""
            checked.append(doc + l)
        else:
            image.append(l)
    sizes = dict(re.findall(r"def (\S+)_func : Struct\.Func := ⟨0x[0-9a-f]+#64, (\d+),", src))
    img = os.path.join(d, NS.split(".")[-1] + ".lean")
    open(img, "w").write("\n".join(image) + "\n")
    rows = {"export_s": export_s, "functions": len(checked),
            "instructions": sum(int(v) for v in sizes.values())}
    r = lean(work, ["-Dprofiler=true", "--root=" + work, "-o", img[:-5] + ".olean", img])
    rows["image"] = {k: v for k, v in r.items() if k != "text"}
    if r["rc"] != 0:
        print(r["text"][-3000:])
        sys.exit(f"bench-chunk-checks: the image does not elaborate (rc {r['rc']})")
    # The `set_option maxRecDepth` the image sets is per file: repeat it.
    rec = next((l for l in lines if l.startswith("set_option maxRecDepth")), "")
    mods, fails, retried = [], [], []
    names = [re.search(r"theorem (\S+)_checked", c).group(1) for c in checked]
    count = [0]

    def run(idx):
        """Check the functions `idx` in one module; a module the cap or the
        timeout kills (no Lean error) is split in two, down to one function."""
        f = os.path.join(work, f"Checks{count[0]}.lean")
        count[0] += 1
        open(f, "w").write(f"import {NS}\n{rec}\nnamespace {NS}\nopen NoCompiler\n\n" +
                           "\n".join(checked[i] for i in idx) + f"\n\nend {NS}\n")
        r = lean(work, ["-Dprofiler=true", f])
        src_lines = open(f).read().splitlines()
        bad = []
        for m in re.finditer(r"Checks\d+\.lean:(\d+):\d+: error: (.*)", r["text"]):
            ln = int(m.group(1))
            nm = re.search(r"theorem (\S+)_checked", src_lines[ln - 1] if ln <= len(src_lines) else "")
            bad.append({"function": nm.group(1) if nm else f"line {ln}", "error": m.group(2)[:300]})
        row = {k: v for k, v in r.items() if k != "text"}
        row.update({"module": os.path.basename(f), "functions": len(idx),
                    "instructions": sum(int(sizes.get(names[i], 0)) for i in idx), "failed": bad})
        killed = r["rc"] != 0 and not bad
        print(f"{row['module']}: {row['functions']} functions, {row['instructions']} instructions, rc {row['rc']}, "
              f"wall {row['wall_s']} s, peak {row['peak_kb']} KB, kernel {row['kernel_ms']} ms, "
              f"failed {len(bad)}{' (killed: split)' if killed and len(idx) > 1 else ''}", flush=True)
        if killed and len(idx) > 1:
            retried.append(row)
            h = len(idx) // 2
            run(idx[:h])
            run(idx[h:])
            return
        if killed:
            row["failed"] = [{"function": names[idx[0]],
                              "error": f"killed (rc {r['rc']}): over the 6 GB cap or the 900 s timeout, "
                                       f"after {row['wall_s']} s"}]
        if len(idx) == 1:
            row["function"] = names[idx[0]]
        mods.append(row)
        fails.extend(row["failed"])

    # Modules of about `budget` instructions; with --largest K, only the K
    # largest functions, each alone (how the cost grows with a function's size).
    group_idx, cur, n = [], [], 0
    if "--largest" in sys.argv:
        k = int(sys.argv[sys.argv.index("--largest") + 1])
        order = sorted(range(len(names)), key=lambda i: -int(sizes.get(names[i], 0)))[:k]
        for i in sorted(order, key=lambda i: int(sizes.get(names[i], 0))):
            run([i])
        names_done = True
    else:
        names_done = False
    for i, nm in enumerate([] if names_done else names):
        k = int(sizes.get(nm, 0))
        if cur and n + k > budget:
            group_idx.append(cur)
            cur, n = [], 0
        cur.append(i)
        n += k
    if cur and not names_done:
        group_idx.append(cur)
    for idx in group_idx:
        run(idx)
    rows["retried"] = retried
    rows["retried_wall_s"] = round(sum(m["wall_s"] for m in retried), 2)
    rows["modules"] = mods
    rows["failed"] = fails
    rows["checks_wall_s"] = round(sum(m["wall_s"] for m in mods), 2)
    rows["checks_kernel_ms"] = round(sum(m["kernel_ms"] for m in mods), 1)
    rows["checks_peak_kb"] = max((m["peak_kb"] or 0) for m in mods) if mods else 0
    i = max(1, sum(m["instructions"] for m in mods))
    print(f"export {export_s} s; image: wall {rows['image']['wall_s']} s, peak {rows['image']['peak_kb']} KB")
    if names_done:
        for m in mods:
            print(f"SIZE {m.get('function')}: {m['instructions']} instructions, rc {m['rc']}, wall {m['wall_s']} s, "
                  f"peak {m['peak_kb']} KB, kernel {m['kernel_ms']} ms")
    print(f"retried: {len(retried)} killed modules, {rows['retried_wall_s']} s (not in the totals below)")
    print(f"checks: {sum(m['functions'] for m in mods)} functions, {i} instructions, {len(mods)} modules; wall "
          f"{rows['checks_wall_s']} s ({round(1000 * rows['checks_wall_s'] / i, 2)} ms/instr), kernel "
          f"{rows['checks_kernel_ms']} ms ({round(rows['checks_kernel_ms'] / i, 2)} ms/instr), max peak "
          f"{rows['checks_peak_kb']} KB; failed {len(fails)}")
    for x in fails:
        print(f"FAIL {x['function']}: {x['error']}")
    if "--json" in sys.argv:
        json.dump(rows, open(sys.argv[sys.argv.index("--json") + 1], "w"), indent=1)
    return 1 if fails else 0


sys.exit(main())
