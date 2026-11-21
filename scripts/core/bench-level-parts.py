#!/usr/bin/env python3
"""The parts of the Lean level check (NoCompiler/Frame.lean `Struct.level`), each
alone, on functions of growing size: where its time and memory go.

    python3 -I scripts/core/bench-level-parts.py ELF WORKDIR SIZE...

WORKDIR is a directory `bench-chunk-checks.py ELF WORKDIR --largest 0` left
(Whole/T.lean and its .olean: ELF's chunk image without its `_checked`
theorems, built against the current NoCompiler). For each SIZE, the
function whose length is closest to it; for each part, one module with one
theorem proved by `decide +kernel` on the function's chunk, elaborated alone
under the cap (bench-chunk-checks.py's `lean`):
  decode   every word of the function decodes (level's first test)
  check    Struct.check (R1 to R3)
  checkL2  Struct.checkL2 (R4 to R6)
  level    the whole `_checked` theorem
  fast     the same statement through `Struct.levelFast` (Frame.lean: decoded once)
Reports wall, peak memory and kernel time per part and size. PARTS=a,b runs
only those parts; FUNCS=f,g names the functions instead of SIZE.
"""
import os, re, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
src = open(os.path.join(HERE, "bench-chunk-checks.py")).read().replace("sys.exit(main())", "")
bcc = {"__name__": "bcc", "__file__": os.path.join(HERE, "bench-chunk-checks.py")}
exec(compile(src, "bench-chunk-checks.py", "exec"), bcc)

FI = "(Struct.instrFast {c} {f}_func (Struct.ITree.ofList (Struct.decoded {c} {f}_func)))"
FA = "(Struct.certFast {f}_func (Struct.ITree.ofList {f}_cert))"
FE = "(Struct.entriesFast entries (Struct.ITree.ofList entries))"
PARTS = {
    "ftree": "((Struct.ITree.ofList (Struct.decoded {c} {f}_func)).get? ({f}_func.len - 1)).isSome = true",
    "fdecode": "(List.range {f}_func.len).all (fun i => (" + FI + " ({f}_func.entry + BitVec.ofNat 64 (4 * i))).isSome) = true",
    "fcheck": "Struct.checkW " + FI + " " + FE + " {f}_func = true",
    "fcheckL2": "Struct.checkL2W " + FI + " " + FA + " {f}_func {f}_frame {f}_cert = true",
    "decode": "(List.range {f}_func.len).all (fun i => ({c}.instr ({f}_func.entry + BitVec.ofNat 64 (4 * i))).isSome) = true",
    "check": "Struct.check {c} {f}_func entries = true",
    "checkL2": "Struct.checkL2 {c} {f}_func {f}_frame {f}_cert = true",
}


def main():
    elf, work = sys.argv[1], os.path.abspath(sys.argv[2])
    sizes = [int(x) for x in sys.argv[3:]]
    img = open(os.path.join(work, "Whole", "T.lean")).read()
    lens = {f: int(n) for f, n in re.findall(r"def (\S+)_func : Struct\.Func := ⟨0x[0-9a-f]+#64, (\d+),", img)}
    out = subprocess.run([bcc["NOCOMPILER"], "export", "--lean-level-check", "--format", "chunks", "--namespace", bcc["NS"], elf],
                         capture_output=True, text=True, check=True).stdout
    checked = {}
    for m in re.finditer(r"theorem (\S+)_checked : Struct\.level \((chunk_\d+\.code \S+)\) .* = some \.(l\d)", out):
        checked[m.group(1)] = (m.group(2), m.group(3), m.group(0).split(" := ")[0])
    rec = next((l for l in img.splitlines() if l.startswith("set_option maxRecDepth")), "")
    print("| function | instructions | part | rc | wall (s) | peak (KB) | kernel (ms) |")
    print("| --- | --- | --- | --- | --- | --- | --- |")
    named = [g for g in os.environ.get("FUNCS", "").split(",") if g]
    for n in (named or sizes):
        f = n if named else min((g for g in checked if g in lens), key=lambda g: abs(lens[g] - n))
        c, lv, full = checked[f]
        stmts = {p: f"theorem part_{p} : {t.format(f=f, c='(' + c + ')')} := by decide +kernel"
                 for p, t in PARTS.items()}
        if lv != "l2":
            stmts.pop("checkL2")
            stmts.pop("fcheckL2")
        stmts["level"] = full.replace(f"theorem {f}_checked", "theorem part_level") + " := by decide +kernel"
        stmts["fast"] = (full.replace(f"theorem {f}_checked", "theorem part_fast") +
                         " := Struct.level_of_fast (by decide +kernel)")
        only = os.environ.get("PARTS")
        for p, t in stmts.items():
            if only and p not in only.split(","):
                continue
            path = os.path.join(work, f"Part_{lens[f]}_{p}.lean")
            open(path, "w").write(f"import {bcc['NS']}\n{rec}\nnamespace {bcc['NS']}\nopen NoCompiler\n\n{t}\n\n"
                                  f"end {bcc['NS']}\n")
            r = bcc["lean"](work, ["-Dprofiler=true", path])
            err = re.search(r"error: (.*)", r["text"])
            print(f"| {f[-40:]} | {lens[f]} | {p} | {r['rc']}{' ' + err.group(1)[:60] if err else ''} | "
                  f"{r['wall_s']} | {r['peak_kb']} | {r['kernel_ms']} |", flush=True)


main()
