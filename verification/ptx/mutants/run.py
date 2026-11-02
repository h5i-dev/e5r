#!/usr/bin/env python3
"""Mutation controls for every property `e5r-verify ptx check` proves.

Each proved benchmark is mutated, one change at a time, in the PTX or in the
spec. Every mutant changes what the kernel does on some launch inside the
spec's range (none is an equivalent rewrite), so a `proved` verdict on any of
them would mean the checker proves something false. The run fails if any
mutant is proved. It also records how many were refuted with a counterexample
the Lean kernel replayed and how many were left `unknown` (fail-closed but
not refuted), per targeted property, and writes results.json.

  run.py E5R_VERIFY OUTDIR [PREFIX ...]

With prefixes, only the mutants whose name starts with one of them run.
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
    # reduce (nvcc 13.2, reduce32 per_block)
    ("reduce: loop bar.sync removed", "race_freedom", "correct/reduce_nvcc.ptx", "reduce.json",
     sub(r"(\$L__BB0_5:\n)\tbar\.sync \t0;\n", r"\1"), None),
    ("reduce: load bound ge -> gt", "memory_safety", "correct/reduce_nvcc.ptx", "reduce.json",
     sub(r"setp\.ge\.u32 \t%p1, %r4, %r12;", "setp.gt.u32 \t%p1, %r4, %r12;"), None),
    ("reduce: tree test ge -> gt", "race_freedom", "correct/reduce_nvcc.ptx", "reduce.json",
     sub(r"setp\.ge\.u32 \t%p3, %r3, %r22;", "setp.gt.u32 \t%p3, %r3, %r22;"), None),
    ("reduce: first stride B/4", "functional_correctness", "correct/reduce_nvcc.ptx", "reduce.json",
     sub(r"shr\.u32 \t%r22, %r1, 1;", "shr.u32 \t%r22, %r1, 2;"), None),
    ("reduce: every thread stores out[ctaid]", "race_freedom", "correct/reduce_nvcc.ptx", "reduce.json",
     sub(r"^\s*@%p5 bra \t\$L__BB0_8;\n", "\n"), None),
    ("reduce: stores tid, not s[0]", "functional_correctness", "correct/reduce_nvcc.ptx", "reduce.json",
     sub(r"st\.global\.u32 \t\[%rd8\], %r20;", "st.global.u32 \t[%rd8], %r3;"), None),
    ("reduce: spec says atomic", "functional_correctness", "correct/reduce_nvcc.ptx", "reduce.json",
     None, spec_set("result", "atomic")),
    # reduce_atomic (reduce32 atomic)
    ("reduce_atomic: atom.add -> st", "functional_correctness", "correct/reduce_atomic_nvcc.ptx",
     "reduce_atomic.json",
     sub(r"atom\.global\.add\.u32 \t%r21, \[%rd6\], %r20;", "st.global.u32 \t[%rd6], %r20;"), None),
    ("reduce_atomic: atom.add -> atom.max", "functional_correctness", "correct/reduce_atomic_nvcc.ptx",
     "reduce_atomic.json",
     sub(r"atom\.global\.add\.u32", "atom.global.max.u32"), None),
    ("reduce_atomic: loop bar.sync removed", "race_freedom", "correct/reduce_atomic_nvcc.ptx",
     "reduce_atomic.json", sub(r"(\$L__BB0_5:\n)\tbar\.sync \t0;\n", r"\1"), None),
    # scan (scan32)
    ("scan: read barrier removed", "race_freedom", "correct/scan_nvcc.ptx", "scan.json",
     sub(r"(\$L__BB0_6:\n)\tbar\.sync \t0;\n", r"\1"), None),
    ("scan: read test lt -> le", "functional_correctness", "correct/scan_nvcc.ptx", "scan.json",
     sub(r"setp\.lt\.u32 \t%p3, %r2, %r26;", "setp.le.u32 \t%p3, %r2, %r26;"), None),
    ("scan: offset times 4", "functional_correctness", "correct/scan_nvcc.ptx", "scan.json",
     sub(r"shl\.b32 \t%r26, %r26, 1;", "shl.b32 \t%r26, %r26, 2;"), None),
    ("scan: store guard removed", "memory_safety", "correct/scan_nvcc.ptx", "scan.json",
     sub(r"(\$L__BB0_7:\n)\t@%p1 bra \t\$L__BB0_9;\n", r"\1"), None),
    # accum (one atomic per element into out[0])
    ("acc_min_s32: min -> max", "functional_correctness", "correct/accum/acc_min_s32.ptx",
     "acc_min_s32.json", sub(r"atom\.global\.min\.s32", "atom.global.max.s32"), None),
    ("acc_min_s32: s32 -> u32", "functional_correctness", "correct/accum/acc_min_s32.ptx",
     "acc_min_s32.json", sub(r"atom\.global\.min\.s32", "atom.global.min.u32"), None),
    ("acc_min_s32: spec says u32", "functional_correctness", "correct/accum/acc_min_s32.ptx",
     "acc_min_s32.json", None, spec_set("type", "u32")),
    ("acc_min_s32: bound check removed", "memory_safety", "correct/accum/acc_min_s32.ptx",
     "acc_min_s32.json", sub(r"^\s*@%p1 bra \t\$L__BB0_2;\n", "\n"), None),
    ("acc_min_s32: load x[i+1]", "memory_safety", "correct/accum/acc_min_s32.ptx",
     "acc_min_s32.json", sub(r"\[%rd5\]", "[%rd5+4]"), None),
    ("acc_min_s32: atom -> plain store", "race_freedom", "correct/accum/acc_min_s32.ptx",
     "acc_min_s32.json",
     sub(r"atom\.global\.min\.s32 \t%r7, \[%rd6\], %r6;", "st.global.u32 \t[%rd6], %r6;"), None),
    ("acc_add_u32: spec says xor", "functional_correctness", "correct/accum/acc_add_u32.ptx",
     "acc_add_u32.json", None, spec_set("op", "xor")),
    ("acc_and_b32: and -> or", "functional_correctness", "correct/accum/acc_and_b32.ptx",
     "acc_and_b32.json", sub(r"atom\.global\.and\.b32", "atom.global.or.b32"), None),
    ("acc_xor_b64: element size 4", "functional_correctness", "correct/accum/acc_xor_b64.ptx",
     "acc_xor_b64.json", sub(r"mul\.wide\.u32 \t%rd4, %r1, 8;", "mul.wide.u32 \t%rd4, %r1, 4;"), None),
    ("acc_max_u64: u64 -> s64", "functional_correctness", "correct/accum/acc_max_u64.ptx",
     "acc_max_u64.json", sub(r"atom\.global\.max\.u64", "atom.global.max.s64"), None),
    ("acc_add_u64: add.u64 -> add.u32 on the low word", "functional_correctness",
     "correct/accum/acc_add_u64.ptx", "acc_add_u64.json",
     sub(r"atom\.global\.add\.u64 \t%rd(\d+), \[%rd(\d+)\], %rd(\d+);",
         r"cvt.u32.u64 \t%r3, %rd\3;\n\tatom.global.add.u32 \t%r4, [%rd\2], %r3;"), None),
    # float maps (bit-exact f32 specs)
    ("saxpy_f32: fma.rn -> fma.rz", "functional_correctness", "correct/float/saxpy_f32.ptx",
     "saxpy_f32.json", sub(r"fma\.rn\.f32", "fma.rz.f32"), None),
    ("saxpy_f32: fma -> mul.rn + add.rn", "functional_correctness", "correct/float/saxpy_f32.ptx",
     "saxpy_f32.json", sub(r"fma\.rn\.f32 \t%f4, %f1, %f3, %f2;",
                           "mul.rn.f32 \t%f4, %f1, %f3;\n\tadd.rn.f32 \t%f4, %f4, %f2;"), None),
    ("saxpy_f32: a*y + x", "functional_correctness", "correct/float/saxpy_f32.ptx",
     "saxpy_f32.json", sub(r"fma\.rn\.f32 \t%f4, %f1, %f3, %f2;", "fma.rn.f32 \t%f4, %f1, %f2, %f3;"), None),
    ("saxpy_f32: .ftz added", "functional_correctness", "correct/float/saxpy_f32.ptx",
     "saxpy_f32.json", sub(r"fma\.rn\.f32", "fma.rn.ftz.f32"), None),
    ("saxpy_f32: .sat added", "functional_correctness", "correct/float/saxpy_f32.ptx",
     "saxpy_f32.json", sub(r"fma\.rn\.f32", "fma.rn.sat.f32"), None),
    ("saxpy_f32: bound check removed", "memory_safety", "correct/float/saxpy_f32.ptx",
     "saxpy_f32.json", sub(r"^\s*@%p1 bra \t\$L__BB0_2;\n", "\n"), None),
    ("saxpy_f32: load x[i+1]", "memory_safety", "correct/float/saxpy_f32.ptx",
     "saxpy_f32.json", sub(r"\[%rd6\]", "[%rd6+4]"), None),
    ("saxpy_f32: spec says fma.rm", "functional_correctness", "correct/float/saxpy_f32.ptx",
     "saxpy_f32.json", None,
     spec_set("element", "fma.rm(saxpy_f32_param_0, saxpy_f32_param_1, saxpy_f32_param_2)")),
    ("saxpy_f32: spec says the product is rounded first", "functional_correctness",
     "correct/float/saxpy_f32.ptx", "saxpy_f32.json", None,
     spec_set("element", "add.rn(mul.rn(saxpy_f32_param_0, saxpy_f32_param_1), saxpy_f32_param_2)")),
    ("f_div_default: div.rn -> div.rz", "functional_correctness", "correct/float/fdefault.ptx",
     "f_div_default.json", sub(r"div\.rn\.f32", "div.rz.f32"), None),
    ("f_div_default: y / x", "functional_correctness", "correct/float/fdefault.ptx",
     "f_div_default.json", sub(r"div\.rn\.f32 \t%f3, %f2, %f1;", "div.rn.f32 \t%f3, %f1, %f2;"), None),
    ("f_relu_default: max -> min", "functional_correctness", "correct/float/fdefault.ptx",
     "f_relu_default.json", sub(r"max\.f32", "min.f32"), None),
    ("f_sqrt_default: sqrt.rn -> sqrt.rp", "functional_correctness", "correct/float/fdefault.ptx",
     "f_sqrt_default.json", sub(r"sqrt\.rn\.f32", "sqrt.rp.f32"), None),
]


def main():
    exe, out = sys.argv[1], sys.argv[2]
    os.makedirs(out, exist_ok=True)
    rows, proved = [], []
    only = sys.argv[3:]
    for i, (name, prop, ptx, spec, pm, sm) in enumerate(MUTANTS):
        if only and not any(name.startswith(p) for p in only):
            continue
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
