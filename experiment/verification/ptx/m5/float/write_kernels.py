#!/usr/bin/env python3
"""Writes kernels/NAME.ptx for the guarded float tasks of tasks.json from
one skeleton (index, bound check, one load per input array, the task's
instruction lines, one store). The skeleton and the instruction lines were
written by the agent in one pass before any kernel was checked
(RESULTS.md); f_saxpy_stride.ptx is written by hand."""
import json, os
HERE = os.path.dirname(os.path.abspath(__file__))

def kernel(t):
    k = t["name"]
    ins = [a for a in t["arrays"] if a != t["output"] or a in t.get("reads", [])]
    params = [(f"{k}_{a}", "u64") for a in t["arrays"]] + [(f"{k}_{s}", "f32") for s in t["scalars"]] + [(f"{k}_n", "u32")]
    L = [".version 8.0", ".target sm_86", ".address_size 64", "", f".visible .entry {k}("]
    L += [f"\t.param .{ty} {p}{',' if i + 1 < len(params) else ''}" for i, (p, ty) in enumerate(params)]
    L += [")", "{", "\t.reg .pred \t%p<2>;", "\t.reg .f32 \t%f<16>;", "\t.reg .b32 \t%r<8>;", "\t.reg .b64 \t%rd<16>;", ""]
    for j, a in enumerate(t["arrays"]):
        L.append(f"\tld.param.u64 \t%rd{j + 1}, [{k}_{a}];")
    for j, s in enumerate(t["scalars"]):
        L.append(f"\tld.param.f32 \t%f{10 + j}, [{k}_{s}];")
    L += [f"\tld.param.u32 \t%r1, [{k}_n];", "\tmov.u32 \t%r2, %ctaid.x;", "\tmov.u32 \t%r3, %ntid.x;",
          "\tmov.u32 \t%r4, %tid.x;", "\tmad.lo.u32 \t%r5, %r2, %r3, %r4;", "\tsetp.ge.u32 \t%p1, %r5, %r1;",
          "\t@%p1 bra \t$L_done;", "\tmul.wide.u32 \t%rd8, %r5, 4;"]
    for j, a in enumerate(t["arrays"]):
        L.append(f"\tadd.u64 \t%rd{9 + j}, %rd{j + 1}, %rd8;")
    for j, a in enumerate(t["arrays"]):
        if a in t["inputs"]:
            L.append(f"\tld.global.f32 \t%f{1 + t['inputs'].index(a)}, [%rd{9 + j}];")
    regs = {a: f"%f{1 + t['inputs'].index(a)}" for a in t["inputs"]}
    regs.update({s: f"%f{10 + j}" for j, s in enumerate(t["scalars"])})
    for line in t["ptx"]:
        for n, r in sorted(regs.items(), key=lambda x: -len(x[0])):
            line = line.replace("{" + n + "}", r)
        L.append("\t" + line)
    o = t["arrays"].index(t["output"])
    L += [f"\tst.global.f32 \t[%rd{9 + o}], %f9;", "$L_done:", "\tret;", "}", ""]
    return "\n".join(L)

for t in json.load(open(os.path.join(HERE, "tasks.json"))):
    if "ptx" in t:
        open(os.path.join(HERE, "kernels", t["name"] + ".ptx"), "w").write(kernel(t))
