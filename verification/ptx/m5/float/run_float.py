#!/usr/bin/env python3
"""M5, float part: specification -> PTX -> Lean -> GPU for tasks.json.

For each task (kernels/NAME.ptx, specs/NAME.json from mkspec.py):

  1. ptxas -arch=sm_86 must assemble the PTX;
  2. `e5r-verify ptx check` gives the verdict and the Lean time;
  3. on the GPU: the PTX kernel and a CUDA C baseline written with the
     intrinsic of the same rounding (`__fmaf_rn`, `__fdiv_rn`, ...; `-ftz=true`
     where the task flushes) run on the same inputs (edge values, random bit
     patterns and random normal numbers) at several lengths and launch
     shapes; the outputs must agree bit for bit, any NaN matching any NaN
     (PTX leaves NaN bits unspecified), and the inputs must be unchanged.
     The baseline is compiled by nvcc and is independent of the Lean model;
  4. timing against the baseline at n = 2^24, median of 20 launches.

  run_float.py E5R_VERIFY OUTDIR [NAME ...]
"""
import ctypes
import json
import math
import os
import re
import subprocess
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, ".."))
from run import CUDA, Gpu, params_of, timeit  # noqa: E402

EDGE = np.array([0, 0x80000000, 1, 0x80000001, 0x007FFFFF, 0x807FFFFF, 0x00800000, 0x80800000,
                 0x3F800000, 0xBF800000, 0x3F7FFFFF, 0x3F800001, 0x7F7FFFFF, 0xFF7FFFFF,
                 0x7F800000, 0xFF800000, 0x7FC00000, 0x7FC12345, 0x7F800001, 0x3F000000,
                 0x4B000000, 0x00400000, 0x34000000], dtype=np.uint32)


def values(rng, n):
    k = rng.integers(0, 4, n)
    edge = EDGE[rng.integers(0, len(EDGE), n)]
    bits = rng.integers(0, 2**32, n, dtype=np.uint64).astype(np.uint32)
    e = rng.integers(127 - 20, 127 + 20, n).astype(np.uint32)
    normal = (rng.integers(0, 2, n).astype(np.uint32) << 31) | (e << 23) | \
        rng.integers(0, 1 << 23, n).astype(np.uint32)
    return np.where(k == 0, edge, np.where(k == 1, bits, normal)).astype(np.uint32)


def isnan(a):
    return ((a & 0x7F800000) == 0x7F800000) & ((a & 0x007FFFFF) != 0)


def baseline_cu(t):
    k = t["name"]
    args = [f"{'' if a == t['output'] else 'const '}float* __restrict__ {a}" for a in t["arrays"]]
    args += [f"float {s}" for s in t["scalars"]] + ["unsigned n"]
    e = t["cuda"]
    if e.startswith("ASM "):
        _, op, x, y = e.split()
        e = None
        body = (f'float r; asm("{op} %0, %1, %2;" : "=f"(r) : "f"({x}[i]), "f"({y}[i])); '
                f"{t['output']}[i] = r;")
    else:
        body = f"{t['output']}[i] = {e};"
    if t.get("stride"):
        code = ("for (unsigned long long i = blockIdx.x * (unsigned long long)blockDim.x + threadIdx.x;"
                f" i < n; i += (unsigned long long)gridDim.x * blockDim.x) {{ {body} }}")
    else:
        code = f"unsigned i = blockIdx.x * blockDim.x + threadIdx.x;\n  if (i < n) {{ {body} }}"
    return f'extern "C" __global__ void {k}_base({", ".join(args)}) {{\n  {code}\n}}\n'


def run(gpu, f, t, params, V, S, n, g, b):
    bufs = {a: gpu.alloc(4 * n) for a in t["arrays"]}
    for a in t["arrays"]:
        gpu.put(bufs[a], V[a])
    args = []
    for p, ty in params:
        short = p[len(t["name"]) + 1:] if p.startswith(t["name"] + "_") else p
        if short in bufs:
            args.append(ctypes.c_uint64(bufs[short].value))
        elif short == "n":
            args.append(ctypes.c_uint32(n))
        else:
            args.append(ctypes.c_uint32(int(S[short])))
    r = gpu.launch(f, g, b, args)
    out = {a: gpu.get(bufs[a], n) for a in t["arrays"]} if r == 0 else None
    for x in bufs.values():
        gpu.free(x)
    return r, out


def gpu_one(name, outdir):
    t = next(x for x in json.load(open(os.path.join(HERE, "tasks.json"))) if x["name"] == name)
    ptx = open(os.path.join(HERE, "kernels", name + ".ptx")).read()
    params = params_of(ptx)
    rng = np.random.default_rng(abs(hash(name)) % 2**32)
    row = {}
    gpu = Gpu()
    row["gpu"] = gpu.name
    cuf = os.path.join(outdir, name + "_base.cu")
    open(cuf, "w").write(baseline_cu(t))
    flags = ["-ftz=true"] if t.get("ftz") else ["-ftz=false"]
    subprocess.run([f"{CUDA}/bin/nvcc", "-O3", "-arch=sm_86", "--ptx", *flags, cuf, "-o", cuf + ".ptx"],
                   check=True, capture_output=True)
    try:
        f = gpu.function(gpu.module(ptx), name)
        bf = gpu.function(gpu.module(open(cuf + ".ptx").read()), name + "_base")
    except RuntimeError as e:
        row["gpu_error"] = str(e)
        print(json.dumps(row))
        return
    bparams = params_of(open(cuf + ".ptx").read())
    compared = 0
    mism = None
    for n in (1, 7, 1000, 65539):
        shapes = [(1, 1), (3, 64), (min(math.ceil(n / 128), 40), 128)] if t.get("stride") else \
            [(math.ceil(n / b), b) for b in (256, 96)]
        for (g, b) in shapes:
            V = {a: values(rng, n) for a in t["arrays"]}
            S = {s: values(rng, 1)[0] for s in t["scalars"]}
            r1, o1 = run(gpu, f, t, params, V, S, n, g, b)
            r2, o2 = _run_base(gpu, bf, t, bparams, V, S, n, g, b)
            if r1 != 0 or r2 != 0:
                mism = mism or f"launch error {r1}/{r2} at n={n}"
                continue
            for a in t["arrays"]:
                x, y = o1[a], o2[a]
                if a != t["output"]:
                    bad = np.nonzero(x != V[a])[0]
                else:
                    bad = np.nonzero((x != y) & ~(isnan(x) & isnan(y)))[0]
                if len(bad) and mism is None:
                    i = int(bad[0])
                    ins = {k: hex(int(V[k][i])) for k in t["inputs"]}
                    ins.update({k: hex(int(v)) for k, v in S.items()})
                    mism = (f"n={n} grid={g} block={b}: {a}[{i}] = {hex(int(x[i]))}, baseline "
                            f"{hex(int(y[i]))}, inputs {ins}")
            compared += n
    row["gpu_mismatch"] = mism
    row["gpu_compared"] = compared
    spec = {"arrays": t["arrays"], "length": "n", "schedule": {"kind": "stride" if t.get("stride") else "guarded"}}
    short = [(p[len(name) + 1:], ty) for p, ty in params]
    row["ptx_us"] = timeit(gpu, f, spec, short)
    names = t["arrays"] + t["scalars"] + ["n"]
    row["baseline_us"] = timeit(gpu, bf, spec, [(names[int(p.split("_param_")[-1])], ty) for p, ty in bparams])
    print(json.dumps(row))


def _run_base(gpu, bf, t, bparams, V, S, n, g, b):
    bufs = {a: gpu.alloc(4 * n) for a in t["arrays"]}
    for a in t["arrays"]:
        gpu.put(bufs[a], V[a])
    args = []
    for p, ty in bparams:
        short = p.split("_param_")[-1]
        i = int(short)
        names = t["arrays"] + t["scalars"] + ["n"]
        nm = names[i]
        if nm in bufs:
            args.append(ctypes.c_uint64(bufs[nm].value))
        elif nm == "n":
            args.append(ctypes.c_uint32(n))
        else:
            args.append(ctypes.c_uint32(int(S[nm])))
    r = gpu.launch(bf, g, b, args)
    out = {a: gpu.get(bufs[a], n) for a in t["arrays"]} if r == 0 else None
    for x in bufs.values():
        gpu.free(x)
    return r, out


def main():
    if sys.argv[1] == "--gpu-one":
        return gpu_one(sys.argv[2], sys.argv[3])
    exe, out = sys.argv[1], sys.argv[2]
    only = set(sys.argv[3:])
    os.makedirs(out, exist_ok=True)
    rows = []
    for t in json.load(open(os.path.join(HERE, "tasks.json"))):
        k = t["name"]
        if only and k not in only:
            continue
        ptxf = os.path.join(HERE, "kernels", k + ".ptx")
        specf = os.path.join(HERE, "specs", k + ".json")
        row = {"name": k, "task": t["task"], "seeded": t.get("seeded", False)}
        a = subprocess.run([f"{CUDA}/bin/ptxas", "-arch=sm_86", ptxf, "-o", os.path.join(out, "k.cubin")],
                           capture_output=True, text=True)
        row["ptxas"] = a.returncode == 0
        c = subprocess.run([exe, "ptx", "check", ptxf, "--spec", specf, "--timeout", "600"],
                           capture_output=True, text=True)
        d = json.loads(c.stdout)
        cx = d.get("counterexample") or {}
        row.update(verdict=d["verdict"], check_seconds=d.get("seconds"),
                   lean_seconds=d.get("lean", {}).get("proof_seconds"),
                   counterexample=cx.get("kind"), replayed=cx.get("replayed_in_lean"),
                   reasons=[r[:200] for r in d.get("reasons", [])])
        g = subprocess.run([sys.executable, __file__, "--gpu-one", k, out], capture_output=True, text=True)
        try:
            row.update(json.loads(g.stdout.strip().splitlines()[-1]))
        except (IndexError, json.JSONDecodeError):
            row["gpu_error"] = (g.stderr or g.stdout)[-300:]
        rows.append(row)
        sp = (row.get("ptx_us"), row.get("baseline_us"))
        ratio = f"{sp[1] / sp[0]:.2f}x" if all(sp) else "-"
        gpu = "ERROR" if "gpu_error" in row else ("agrees" if row.get("gpu_mismatch") is None else "DIFFERS")
        print(f"{k:18} {row['verdict']:11} {str(row['counterexample']):12} gpu {gpu:7} "
              f"lean {row['lean_seconds']}s  speed vs nvcc {ratio}", flush=True)
    json.dump({"rows": rows}, open(os.path.join(out, "results.json"), "w"), indent=1)
    by = lambda v: sum(r["verdict"] == v for r in rows)
    print(f"tasks {len(rows)}: proved {by('proved')}, refuted {by('refuted')}, unknown {by('unknown')}, "
          f"unsupported {by('unsupported')}")
    bad = [r["name"] for r in rows if r["verdict"] == "proved" and (r.get("gpu_mismatch") or r.get("gpu_error"))]
    if bad:
        print("PROVED BUT DIFFERENT FROM THE BASELINE ON THE GPU:", bad)
        sys.exit(1)


if __name__ == "__main__":
    main()
