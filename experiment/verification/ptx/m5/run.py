#!/usr/bin/env python3
"""M5: specification -> PTX -> Lean -> GPU, for every task in tasks.json.

For each task (kernels/NAME.ptx written by the model, specs/NAME.json from
mkspec.py):

  1. ptxas -arch=sm_86 must assemble the PTX;
  2. `e5r ptx check` gives proved / refuted / unknown / unsupported,
     with the Lean time;
  3. on the GPU (CUDA driver API through ctypes): the kernel runs on random
     inputs at several lengths and launch shapes inside the spec's range, and
     the output is compared with the spec's element function (numpy, uint32
     wrap-around) and every other array must be unchanged;
  4. timing: the PTX kernel against a CUDA C baseline with the same schedule,
     compiled by nvcc -O3, at n = 2^24, median of 20 launches.

  run.py E5R_VERIFY OUTDIR [NAME ...]

Writes OUTDIR/results.json and prints one line per task and a summary.
"""
import ctypes
import json
import math
import os
import re
import subprocess
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
CUDA = os.environ.get("CUDA_HOME", "/usr/local/cuda")

cu = ctypes.CDLL("libcuda.so.1")


def ck(r, what):
    if r != 0:
        s = ctypes.c_char_p()
        cu.cuGetErrorString(r, ctypes.byref(s))
        raise RuntimeError(f"{what}: {s.value.decode() if s.value else r}")


class Gpu:
    def __init__(self):
        ck(cu.cuInit(0), "cuInit")
        self.dev = ctypes.c_int()
        ck(cu.cuDeviceGet(ctypes.byref(self.dev), 0), "cuDeviceGet")
        self.ctx = ctypes.c_void_p()
        ck(cu.cuDevicePrimaryCtxRetain(ctypes.byref(self.ctx), self.dev), "ctx")
        ck(cu.cuCtxSetCurrent(self.ctx), "ctx")
        name = ctypes.create_string_buffer(256)
        cu.cuDeviceGetName(name, 256, self.dev)
        self.name = name.value.decode()

    def module(self, ptx_text):
        m = ctypes.c_void_p()
        data = ctypes.create_string_buffer(ptx_text.encode() + b"\0")
        ck(cu.cuModuleLoadData(ctypes.byref(m), data), "cuModuleLoadData")
        return m

    def function(self, m, name):
        f = ctypes.c_void_p()
        ck(cu.cuModuleGetFunction(ctypes.byref(f), m, name.encode()), f"function {name}")
        return f

    def alloc(self, nbytes):
        p = ctypes.c_uint64()
        ck(cu.cuMemAlloc_v2(ctypes.byref(p), max(nbytes, 4)), "cuMemAlloc")
        return p

    def free(self, p):
        cu.cuMemFree_v2(p)

    def put(self, p, arr):
        ck(cu.cuMemcpyHtoD_v2(p, arr.ctypes.data_as(ctypes.c_void_p), arr.nbytes), "HtoD")

    def get(self, p, n):
        a = np.empty(n, dtype=np.uint32)
        ck(cu.cuMemcpyDtoH_v2(a.ctypes.data_as(ctypes.c_void_p), p, a.nbytes), "DtoH")
        return a

    def launch(self, f, grid, block, args):
        holders = []
        ptrs = (ctypes.c_void_p * len(args))()
        for i, a in enumerate(args):
            holders.append(a)
            ptrs[i] = ctypes.cast(ctypes.byref(a), ctypes.c_void_p)
        r = cu.cuLaunchKernel(f, grid, 1, 1, block, 1, 1, 0, None, ptrs, None)
        if r == 0:
            r = cu.cuCtxSynchronize()
        return r


def np_expr(element, arrays, scalars):
    """The spec's element function as a numpy expression over uint32."""
    e = element
    for name in sorted(arrays + scalars, key=len, reverse=True):
        e = re.sub(rf"\b{re.escape(name)}\b", f"V[{name!r}]", e)
    return e


def c_expr(element, arrays, scalars):
    e = element
    for name in sorted(arrays + scalars, key=len, reverse=True):
        repl = f"{name}[i]" if name in arrays else name
        e = re.sub(rf"\b{re.escape(name)}\b", repl, e)
    e = re.sub(r"\b(0x[0-9a-fA-F]+|\d+)\b", r"\1u", e)
    return e


def baseline_cu(spec, params):
    k = spec["kernel"]
    args = []
    for p, t in params:
        if p in spec["arrays"]:
            q = "" if p == spec["output"] else "const "
            args.append(f"{q}unsigned* __restrict__ {p}")
        else:
            args.append(f"unsigned {p}")
    n = spec["length"]
    body = f"{spec['output']}[i] = {c_expr(spec['element'], spec['arrays'], spec['scalars'])};"
    if spec["schedule"]["kind"] == "guarded":
        code = f"unsigned i = blockIdx.x * blockDim.x + threadIdx.x;\n  if (i < {n}) {body}"
    else:
        code = (f"for (unsigned long long i = blockIdx.x * (unsigned long long)blockDim.x + threadIdx.x;"
                f" i < {n}; i += (unsigned long long)gridDim.x * blockDim.x) {body}")
    return f'extern "C" __global__ void {k}_base({", ".join(args)}) {{\n  {code}\n}}\n'


def params_of(ptx):
    m = re.search(r"\.entry\s+\w+\s*\((.*?)\)", ptx, re.S)
    return re.findall(r"\.param\s+\.(\w+)\s+(\w+)", m.group(1)) and [
        (n, t) for t, n in re.findall(r"\.param\s+\.(\w+)\s+(\w+)", m.group(1))]


def shapes(spec, n):
    sc = spec["schedule"]
    if sc["kind"] == "guarded":
        return [(math.ceil(n / b), b) for b in (256, 96, 1)] if n <= 4096 else [(math.ceil(n / 256), 256), (math.ceil(n / 1000), 1000)]
    return [(1, 1), (3, 64), (min(math.ceil(n / 128), 40), 128)]


def gpu_test(gpu, f, spec, params, rng):
    """None if every run matches the spec, else a description of the first mismatch."""
    for n in (1, 7, 1000, 65539):
        for (g, b) in shapes(spec, n):
            V = {a: rng.integers(0, 2**32, n, dtype=np.uint32) for a in spec["arrays"]}
            S = {s: np.uint32(rng.integers(0, 2**32)) for s in spec["scalars"]}
            want = eval(np_expr(spec["element"], spec["arrays"], spec["scalars"]),
                        {"V": {**V, **S}, "np": np})
            want = np.asarray(want, dtype=np.uint32) * np.ones(n, dtype=np.uint32)
            bufs = {a: gpu.alloc(4 * n) for a in spec["arrays"]}
            for a in spec["arrays"]:
                gpu.put(bufs[a], V[a])
            args = []
            for p, t in params:
                if p in bufs:
                    args.append(ctypes.c_uint64(bufs[p].value))
                elif p == spec["length"]:
                    args.append(ctypes.c_uint32(n))
                else:
                    args.append(ctypes.c_uint32(int(S[p])))
            r = gpu.launch(f, g, b, args)
            if r != 0:
                return f"launch error {r} at n={n} grid={g} block={b}"
            for a in spec["arrays"]:
                got = gpu.get(bufs[a], n)
                ref = want if a == spec["output"] else V[a]
                if not np.array_equal(got, ref):
                    i = int(np.nonzero(got != ref)[0][0])
                    for x in bufs.values():
                        gpu.free(x)
                    return (f"n={n} grid={g} block={b}: {a}[{i}] = {int(got[i])}, "
                            f"want {int(ref[i])}")
            for x in bufs.values():
                gpu.free(x)
    return None


def timeit(gpu, f, spec, params, n=1 << 24, reps=20):
    sc = spec["schedule"]
    g, b = (math.ceil(n / 256), 256) if sc["kind"] == "guarded" else (640, 256)
    bufs = {a: gpu.alloc(4 * n) for a in spec["arrays"]}
    args = []
    for p, t in params:
        if p in bufs:
            args.append(ctypes.c_uint64(bufs[p].value))
        elif p == spec["length"]:
            args.append(ctypes.c_uint32(n))
        else:
            args.append(ctypes.c_uint32(3))
    for _ in range(3):
        gpu.launch(f, g, b, args)
    ts = []
    for _ in range(reps):
        t = time.perf_counter()
        r = gpu.launch(f, g, b, args)
        ts.append(time.perf_counter() - t)
        if r != 0:
            return None
    for x in bufs.values():
        gpu.free(x)
    return float(np.median(ts)) * 1e6


def gpu_one(name, out):
    """GPU half of one task, in its own process: a kernel that faults leaves
    the CUDA context unusable, so each task gets a fresh one."""
    ptx = open(os.path.join(HERE, "kernels", name + ".ptx")).read()
    spec = json.load(open(os.path.join(HERE, "specs", name + ".json")))
    params = params_of(ptx)
    gpu = Gpu()
    rng = np.random.default_rng(abs(hash(name)) % 2**32)
    row = {"gpu": gpu.name}
    try:
        f = gpu.function(gpu.module(ptx), name)
        row["gpu_mismatch"] = gpu_test(gpu, f, spec, params, rng)
        row["ptx_us"] = timeit(gpu, f, spec, params) if row["gpu_mismatch"] is None else None
    except RuntimeError as e:
        row["gpu_error"] = str(e)
    try:
        gpu = Gpu()
        cuf = os.path.join(out, name + "_base.cu")
        open(cuf, "w").write(baseline_cu(spec, params))
        subprocess.run([f"{CUDA}/bin/nvcc", "-O3", "-arch=sm_86", "--ptx", cuf, "-o", cuf + ".ptx"],
                       check=True, capture_output=True)
        bf = gpu.function(gpu.module(open(cuf + ".ptx").read()), name + "_base")
        row["baseline_mismatch"] = gpu_test(gpu, bf, spec, params, rng)
        row["baseline_us"] = timeit(gpu, bf, spec, params)
    except (RuntimeError, subprocess.CalledProcessError) as e:
        row["baseline_error"] = str(e)
    print(json.dumps(row))


def main():
    if sys.argv[1] == "--gpu-one":
        return gpu_one(sys.argv[2], sys.argv[3])
    exe, out = sys.argv[1], sys.argv[2]
    only = set(sys.argv[3:])
    os.makedirs(out, exist_ok=True)
    tasks = json.load(open(os.path.join(HERE, "tasks.json")))
    rows = []
    for t in tasks:
        k = t["name"]
        if only and k not in only:
            continue
        ptxf = os.path.join(HERE, "kernels", k + ".ptx")
        specf = os.path.join(HERE, "specs", k + ".json")
        ptx = open(ptxf).read()
        spec = json.load(open(specf))
        row = {"name": k, "task": t["task"], "schedule": spec["schedule"]["kind"]}
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
        print(f"{k:14} {row['verdict']:11} {str(row['counterexample']):12} "
              f"gpu {'ok' if row.get('gpu_mismatch') is None and 'gpu_error' not in row else 'MISMATCH'} "
              f"lean {row['lean_seconds']}s  speed vs nvcc {ratio}", flush=True)
    json.dump({"gpu": rows[0].get("gpu") if rows else None, "rows": rows}, open(os.path.join(out, "results.json"), "w"), indent=1)
    by = lambda v: sum(r["verdict"] == v for r in rows)
    print(f"tasks {len(rows)}: proved {by('proved')}, refuted {by('refuted')}, unknown {by('unknown')}, "
          f"unsupported {by('unsupported')}, error {by('error')}")
    bad = [r["name"] for r in rows if r["verdict"] == "proved" and (r.get("gpu_mismatch") or r.get("gpu_error"))]
    if bad:
        print("PROVED BUT WRONG ON THE GPU:", bad)
        sys.exit(1)


if __name__ == "__main__":
    main()
