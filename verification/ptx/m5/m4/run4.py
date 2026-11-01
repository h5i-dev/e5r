#!/usr/bin/env python3
"""M5 with the M4 classes: CUDA C -> nvcc PTX -> Lean -> GPU, for every task
in m4/tasks.json, and for random mutants of them (mutate.py).

For each kernel (kernels/NAME.ptx, compiled from kernels/NAME.cu by nvcc 13.2
-O3 -arch=sm_86 --ptx; specs/NAME.json):

  1. ptxas -arch=sm_86 must assemble the PTX;
  2. `e5r-verify ptx check` gives proved / refuted / unknown / unsupported;
  3. on the GPU: the kernel runs on random inputs at several lengths and
     launch shapes inside the class's range, and the output words are
     compared with the class's result (numpy, uint32 wrap-around): `per_block`
     out[b] = sum of block b's segment, `atomic` *out = initial + sum of all,
     scan32 out[i] = inclusive prefix sum of i's block segment. The input
     must be unchanged and the bytes after the output too.

No speed is measured: every kernel here is nvcc's own output, so a baseline
compiled by nvcc would be the same code.

  run4.py E5R_VERIFY OUTDIR [NAME ...]          the corpus
  run4.py --mutants E5R_VERIFY OUTDIR           mutants.json from mutate.py
"""
import ctypes
import json
import os
import subprocess
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, ".."))
from run import Gpu, CUDA  # noqa: E402


def shapes(spec):
    mb = spec["max_block"]
    if spec["class"] == "reduce32":
        bs = [b for b in (1, 2, 32, 256, 1024) if b <= mb]
    else:
        bs = [b for b in (1, 3, 96, 256, 1024) if b <= mb]
    for b in bs:
        for n in (1, 5, 1000, 70001):
            g = max(1, -(-n // b))
            if spec["class"] == "reduce32":
                yield g, b, n
                if g > 1:
                    yield g - 1, b, n  # fewer blocks than elements need
            else:
                yield g, b, n
                yield g, b, max(0, g * b - 1)


def want(spec, x, g, b, n, out0):
    x64 = x.astype(np.uint64)
    if spec["class"] == "scan32":
        y = np.zeros(n, dtype=np.uint64)
        for c in range(g):
            lo, hi = c * b, min(n, (c + 1) * b)
            if lo < hi:
                y[lo:hi] = np.cumsum(x64[lo:hi])
        return (y % 2**32).astype(np.uint32)
    seg = np.zeros(g * b, dtype=np.uint64)
    m = min(n, g * b)
    seg[:m] = x64[:m]
    if spec.get("result") == "atomic":
        return np.array([(int(out0[0]) + int(seg.sum())) % 2**32], dtype=np.uint32)
    return (seg.reshape(g, b).sum(axis=1) % 2**32).astype(np.uint32)


def gpu_test(gpu, f, spec, rng):
    for g, b, n in shapes(spec):
        x = rng.integers(0, 2**32, max(n, 1), dtype=np.uint32)[:n]
        olen = n if spec["class"] == "scan32" else (1 if spec.get("result") == "atomic" else g)
        out0 = rng.integers(0, 2**32, olen + 16, dtype=np.uint32)
        bx, bo = gpu.alloc(4 * max(n, 1)), gpu.alloc(4 * (olen + 16))
        if n:
            gpu.put(bx, x)
        gpu.put(bo, out0)
        r = gpu.launch(f, g, b, [ctypes.c_uint64(bx.value), ctypes.c_uint64(bo.value), ctypes.c_uint32(n)])
        if r != 0:
            return f"launch error {r} at grid={g} block={b} n={n}"
        got = gpu.get(bo, olen + 16)
        gx = gpu.get(bx, n) if n else x
        gpu.free(bx)
        gpu.free(bo)
        w = want(spec, x, g, b, n, out0)
        if not np.array_equal(got[:olen], w):
            i = int(np.nonzero(got[:olen] != w)[0][0])
            return f"grid={g} block={b} n={n}: out[{i}] = {int(got[i])}, want {int(w[i])}"
        if not np.array_equal(got[olen:], out0[olen:]):
            return f"grid={g} block={b} n={n}: wrote past the output"
        if not np.array_equal(gx, x):
            return f"grid={g} block={b} n={n}: changed the input"
    return None


def gpu_one(ptxf, specf):
    ptx = open(ptxf).read()
    spec = json.load(open(specf))
    gpu = Gpu()
    rng = np.random.default_rng(abs(hash(spec["kernel"] + ptx)) % 2**32)
    row = {"gpu": gpu.name}
    try:
        f = gpu.function(gpu.module(ptx), spec["kernel"])
        row["gpu_mismatch"] = gpu_test(gpu, f, spec, rng)
    except RuntimeError as e:
        row["gpu_error"] = str(e)
    print(json.dumps(row))


def one(exe, out, name, ptxf, specf, timeout=600):
    row = {"name": name}
    a = subprocess.run([f"{CUDA}/bin/ptxas", "-arch=sm_86", ptxf, "-o", os.path.join(out, "k.cubin")],
                       capture_output=True, text=True)
    row["ptxas"] = a.returncode == 0
    c = subprocess.run([exe, "ptx", "check", ptxf, "--spec", specf, "--timeout", str(timeout)],
                       capture_output=True, text=True)
    d = json.loads(c.stdout)
    cx = d.get("counterexample") or {}
    row.update(verdict=d["verdict"], check_seconds=d.get("seconds"),
               lean_seconds=d.get("lean", {}).get("proof_seconds"),
               refutation_seconds=d.get("lean", {}).get("refutation_seconds"),
               counterexample=cx.get("kind"), replayed=cx.get("replayed_in_lean"),
               reasons=[r[:240] for r in d.get("reasons", [])])
    try:
        g = subprocess.run([sys.executable, __file__, "--gpu-one", ptxf, specf], capture_output=True,
                           text=True, timeout=180)
        row.update(json.loads(g.stdout.strip().splitlines()[-1]))
    except subprocess.TimeoutExpired:
        row["gpu_error"] = "the kernel did not finish within 180 s"
    except (IndexError, json.JSONDecodeError):
        row["gpu_error"] = (g.stderr or g.stdout)[-300:]
    ok = row.get("gpu_mismatch") is None and "gpu_error" not in row
    print(f"{name:34} {row['verdict']:11} {str(row['counterexample']):12} gpu {'agrees' if ok else 'DISAGREES'}"
          f"  check {row['check_seconds']}s", flush=True)
    return row


def main():
    if sys.argv[1] == "--gpu-one":
        return gpu_one(sys.argv[2], sys.argv[3])
    rows = []
    if sys.argv[1] == "--mutants":
        exe, out = sys.argv[2], sys.argv[3]
        os.makedirs(out, exist_ok=True)
        for m in json.load(open(os.path.join(HERE, "mutants.json"))):
            pf = os.path.join(out, m["id"] + ".ptx")
            open(pf, "w").write(m["ptx"])
            r = one(exe, out, m["id"], pf, os.path.join(HERE, "specs", m["base"] + ".json"), 300)
            r.update(base=m["base"], change=m["change"])
            rows.append(r)
        res = os.path.join(out, "mutants_results.json")
    else:
        exe, out = sys.argv[1], sys.argv[2]
        only = set(sys.argv[3:])
        os.makedirs(out, exist_ok=True)
        for t in json.load(open(os.path.join(HERE, "tasks.json"))):
            k = t["name"]
            if only and k not in only:
                continue
            r = one(exe, out, k, os.path.join(HERE, "kernels", k + ".ptx"),
                    os.path.join(HERE, "specs", k + ".json"))
            r["task"] = t["task"]
            rows.append(r)
        res = os.path.join(out, "results.json")
    json.dump({"rows": rows}, open(res, "w"), indent=1)
    by = lambda v: sum(r["verdict"] == v for r in rows)
    print(f"kernels {len(rows)}: proved {by('proved')}, refuted {by('refuted')}, unknown {by('unknown')}, "
          f"unsupported {by('unsupported')}, error {by('error')}")
    bad = [r["name"] for r in rows if r["verdict"] == "proved" and (r.get("gpu_mismatch") or r.get("gpu_error"))]
    if bad:
        print("PROVED BUT WRONG ON THE GPU:", bad)
        sys.exit(1)


if __name__ == "__main__":
    main()
