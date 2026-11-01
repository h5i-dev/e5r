#!/usr/bin/env python3
"""Mutation controls for every property `e5r-verify ptx check` proves.

Each proved benchmark is mutated, one change at a time, in the PTX or in the
spec. Every mutant changes what the kernel does on some launch inside the
spec's range (none is an equivalent rewrite), so a `proved` verdict on any of
them would mean the checker proves something false. The run fails if any
mutant is proved. It also records how many were refuted with a counterexample
the Lean kernel replayed and how many were left `unknown` (fail-closed but
not refuted), per targeted property, and writes results.json.

  run.py E5R_VERIFY OUTDIR
"""
import json
import os
import re
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
BENCH = os.path.join(HERE, "..", "benchmarks")


def sub(pattern, repl):
    def f(text):
        new, n = re.subn(pattern, repl, text, count=1, flags=re.M)
        assert n == 1, f"mutation pattern not found: {pattern}"
        return new
    return f


def spec_set(key, value):
    def f(spec):
        d = json.loads(spec)
        cur = d
        *path, last = key.split(".")
        for p in path:
            cur = cur[p]
        cur[last] = value
        return json.dumps(d, indent=2)
    return f


# (name, property it breaks, benchmark, spec, PTX mutation or None, spec mutation or None)
MUTANTS = [
    # vadd (nvcc 13.2, guarded)
    ("vadd: ge -> gt in the bound check", "memory_safety", "correct/vadd_nvcc.ptx", "vadd.json",
     sub(r"setp\.ge\.s32", "setp.gt.s32"), None),
    ("vadd: bound check branch removed", "memory_safety", "correct/vadd_nvcc.ptx", "vadd.json",
     sub(r"^\s*@%p1 bra\s+\$L__BB0_2;\n", ""), None),
    ("vadd: element size 8 in the offset", "memory_safety", "correct/vadd_nvcc.ptx", "vadd.json",
     sub(r"mul\.wide\.s32 \t%rd5, %r1, 4;", "mul.wide.s32 \t%rd5, %r1, 8;"), None),
    ("vadd: load b[i+1]", "memory_safety", "correct/vadd_nvcc.ptx", "vadd.json",
     sub(r"\[%rd8\]", "[%rd8+4]"), None),
    ("vadd: index from %tid.x only", "race_freedom", "correct/vadd_nvcc.ptx", "vadd.json",
     sub(r"mad\.lo\.s32 \t%r1, %r3, %r4, %r5;", "mov.u32 \t%r1, %r5;"), None),
    ("vadd: index from %ctaid.x only", "race_freedom", "correct/vadd_nvcc.ptx", "vadd.json",
     sub(r"mad\.lo\.s32 \t%r1, %r3, %r4, %r5;", "mov.u32 \t%r1, %r3;"), None),
    ("vadd: add -> sub", "functional_correctness", "correct/vadd_nvcc.ptx", "vadd.json",
     sub(r"add\.s32 \t%r8, %r6, %r7;", "sub.s32 \t%r8, %r6, %r7;"), None),
    ("vadd: b + b", "functional_correctness", "correct/vadd_nvcc.ptx", "vadd.json",
     sub(r"add\.s32 \t%r8, %r6, %r7;", "add.s32 \t%r8, %r6, %r6;"), None),
    ("vadd: store a[i]", "functional_correctness", "correct/vadd_nvcc.ptx", "vadd.json",
     sub(r"st\.global\.u32 \t\[%rd10\], %r8;", "st.global.u32 \t[%rd10], %r7;"), None),
    ("vadd: store removed", "functional_correctness", "correct/vadd_nvcc.ptx", "vadd.json",
     sub(r"^\s*st\.global\.u32 \t\[%rd10\], %r8;\n", ""), None),
    ("vadd: spec says a - b", "functional_correctness", "correct/vadd_nvcc.ptx", "vadd.json",
     None, spec_set("element", "vadd_param_0 - vadd_param_1")),
    ("vadd: spec says a + b + 1", "functional_correctness", "correct/vadd_nvcc.ptx", "vadd.json",
     None, spec_set("element", "vadd_param_0 + vadd_param_1 + 1")),
    ("vadd: spec claims 2^32 - 1 threads", "memory_safety", "correct/vadd_nvcc.ptx", "vadd.json",
     None, spec_set("schedule.max_threads", "4294967295")),
    # saxpy (grid-stride)
    ("saxpy: ge -> gt in the loop test", "memory_safety", "correct/saxpy.ptx", "saxpy.json",
     sub(r"setp\.ge\.u64", "setp.gt.u64"), None),
    ("saxpy: shift by 3", "memory_safety", "correct/saxpy.ptx", "saxpy.json",
     sub(r"shl\.b64 \t%rd7, %rd3, 2;", "shl.b64 \t%rd7, %rd3, 3;"), None),
    ("saxpy: loop bound from a, not n", "memory_safety", "correct/saxpy.ptx", "saxpy.json",
     sub(r"cvt\.u64\.u32 \t%rd6, %r2;", "cvt.u64.u32 \t%rd6, %r1;"), None),
    ("saxpy: stride 1", "race_freedom", "correct/saxpy.ptx", "saxpy.json",
     sub(r"add\.u64 \t%rd3, %rd3, %rd5;", "add.u64 \t%rd3, %rd3, 1;"), None),
    ("saxpy: a*y + x", "functional_correctness", "correct/saxpy.ptx", "saxpy.json",
     sub(r"mad\.lo\.u32 \t%r9, %r1, %r7, %r8;", "mad.lo.u32 \t%r9, %r1, %r8, %r7;"), None),
    ("saxpy: also clears x[i]", "functional_correctness", "correct/saxpy.ptx", "saxpy.json",
     sub(r"(st\.global\.u32 \t\[%rd9\], %r9;)", r"\1\n\tst.global.u32 \t[%rd8], 0;"), None),
    ("saxpy: spec says a*x", "functional_correctness", "correct/saxpy.ptx", "saxpy.json",
     None, spec_set("element", "saxpy_a * saxpy_x")),
    ("saxpy: index never advances", "termination", "correct/saxpy.ptx", "saxpy.json",
     sub(r"^\s*add\.u64 \t%rd3, %rd3, %rd5;\n", ""), None),
]


def main():
    exe, out = sys.argv[1], sys.argv[2]
    os.makedirs(out, exist_ok=True)
    rows, proved = [], []
    for i, (name, prop, ptx, spec, pm, sm) in enumerate(MUTANTS):
        src = open(os.path.join(BENCH, ptx)).read()
        sp = open(os.path.join(BENCH, "specs", spec)).read()
        src2 = pm(src) if pm else src
        sp2 = sm(sp) if sm else sp
        assert src2 != src or sp2 != sp
        pf, sf = os.path.join(out, f"m{i}.ptx"), os.path.join(out, f"m{i}.json")
        open(pf, "w").write(src2)
        open(sf, "w").write(sp2)
        t = time.time()
        r = subprocess.run([exe, "ptx", "check", pf, "--spec", sf, "--timeout", "300"],
                           capture_output=True, text=True)
        d = json.loads(r.stdout)
        cx = d.get("counterexample") or {}
        row = {"mutant": name, "targets": prop, "verdict": d["verdict"], "exit": r.returncode,
               "counterexample": cx.get("kind"), "replayed": cx.get("replayed_in_lean"),
               "seconds": round(time.time() - t, 1), "reasons": d.get("reasons", [])[:2]}
        rows.append(row)
        print(f"{d['verdict']:11} {str(cx.get('kind')):12} {row['seconds']:6}s  {name}", flush=True)
        if d["verdict"] == "proved" or r.returncode == 0:
            proved.append(name)
    refuted = sum(r["verdict"] == "refuted" for r in rows)
    summary = {"mutants": len(rows), "proved": len(proved), "refuted": refuted,
               "not_refuted": len(rows) - refuted - len(proved), "rows": rows}
    json.dump(summary, open(os.path.join(out, "results.json"), "w"), indent=2)
    print(f"mutants: {len(rows)}, proved {len(proved)}, refuted {refuted}, "
          f"unknown/unsupported {len(rows) - refuted - len(proved)}")
    if proved:
        print("PROVED MUTANTS (the checker accepted a wrong kernel):", proved)
        sys.exit(1)


if __name__ == "__main__":
    main()
