#!/usr/bin/env python3
"""Criterion 7'(b): Lean cost per instruction on a real artifact's own functions.

    python3 -I scripts/core/bench-prove.py IMAGE.lean OUTDIR [--max N] [--only NAME]

IMAGE.lean is `nocompiler export --lean-level-check A.elf --namespace Bench.Image -o IMAGE.lean`
of the whole artifact (examples/refine/targets). That file does not elaborate
as one module (docs/isa/v1-results.md, 7'), so for each exported function
this writes OUTDIR/F_<k>.lean, a slice of it: `code` cut to the function's
code region (itself and its callees), the `instr_` lemmas there, the entries
there, and the function's definitions (a function whose region spans more
than MAX_SPAN words of .text is reported and skipped). Two variants per function:
  checked   the slice with `<f>_checked` (the level, decided by the kernel);
  safe      plus, for a function the current tactic can take as it stands
            (no callees, no blocks or loops, no ecall, memory only through
            sp), a proof by `nocompiler_auto` of `VerifiedImg` at the
            safety-only specification (any entry; it returns, preserving the
            ABI, touching only its frame).
Each is checked with Lean's profiler under the memory cap; cost = the
variant's total and kernel ("type checking") time minus the slice alone's,
per instruction of the function. Prints one row per function and a summary.
"""
import json, os, re, subprocess, sys, time

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))
LEAN = os.path.join(ROOT, "lean")
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
UNIT = {"ns": 1e-6, "us": 1e-3, "μs": 1e-3, "ms": 1.0, "s": 1000.0}


def capped(cmd):
    probe = subprocess.run(["systemd-run", "--user", "--scope", "--quiet", "-p", "MemoryMax=64M", "true"],
                           capture_output=True) if os.path.exists("/usr/bin/systemd-run") else None
    if probe is None or probe.returncode != 0:
        return ["timeout", "900"] + cmd
    env = [f"--setenv=PATH={os.environ.get('PATH', '')}"]
    if "ELAN_HOME" in os.environ:
        env.append(f"--setenv=ELAN_HOME={os.environ['ELAN_HOME']}")
    return ["systemd-run", "--user", "--scope", "--quiet", "-p", "MemoryMax=6G", "-p", "MemorySwapMax=0"] + env + \
        ["timeout", "900"] + cmd


def profile(text):
    out = {}
    block = text.split("cumulative profiling times:")[-1]
    for m in re.finditer(r"^\s+(.+?) ([\d.]+)(ns|us|μs|ms|s)$", block, re.M):
        out[m.group(1)] = float(m.group(2)) * UNIT[m.group(3)]
    return out


def parse(path):
    src = open(path).read()
    head, rest = src.split("\ndef code : Code := ", 1)
    arr, rest = rest.split("]⟩\n", 1)
    base = int(re.match(r"⟨0x([0-9a-f]+)#64", arr).group(1), 16)
    words = re.findall(r"0x([0-9a-f]{8})#32", arr)
    instrs = {}
    for m in re.finditer(r"/-- `(.*)` -/\n(@\[nocompiler_image\] theorem instr_([0-9a-f]+) .*)\n", rest):
        instrs[int(m.group(3), 16)] = (m.group(1), m.group(2))
    entries = [int(x, 16) for x in re.search(r"def entries : List Word := \[(.*)\]", rest).group(1)
               .replace("#64", "").split(", ") if x]
    funcs = []
    parts = re.split(r"\n(?=/-- `[^`]*`'s block/loop structure)", rest)
    for p in parts[1:]:
        p = p.split("\nend ")[0]
        name = re.match(r"/-- `([^`]*)`", p).group(1)
        ident = re.search(r"\ndef (\S+)_func : Struct\.Func := ⟨0x([0-9a-f]+)#64, (\d+), (.*)⟩", p)
        dom = [(int(a, 16), int(n)) for a, n in re.findall(r"\(0x([0-9a-f]+)#64, (\d+)\)",
                                                             re.search(r"_dom : Dom := \[(.*)\]", p).group(1))]
        frame = int(re.search(r"_frame : Struct\.Frame := ⟨(\d+),", p).group(1))
        funcs.append({"name": name, "id": ident.group(1), "entry": int(ident.group(2), 16),
                      "n": int(ident.group(3)), "nodes": ident.group(4), "dom": dom, "frame": frame, "text": p})
    return base, words, instrs, entries, funcs


# `code` is one array: a region whose functions lie far apart in .text gives a
# slice as long as the distance between them.
MAX_SPAN = 2048

MEM = re.compile(r"^(lb|lbu|lh|lhu|lw|lwu|ld|sb|sh|sw|sd)\s+\w+,\s*-?\d+\((\w+)\)")


def provable(f, instrs):
    if len(f["dom"]) != 1 or f["nodes"] != "[]":
        return False
    for pc in range(f["entry"], f["entry"] + 4 * f["n"], 4):
        asm = instrs.get(pc, ("?",))[0]
        if asm.startswith("ecall") or asm == "?":
            return False
        m = MEM.match(asm)
        if m and m.group(2) != "sp":
            return False
    return True


def slice_file(f, base, words, instrs, entries, variant):
    lo = min(a for a, _ in f["dom"])
    hi = max(a + n for a, n in f["dom"])
    w = words[(lo - base) // 4:(hi - base) // 4]
    o = ["import NoCompiler", "import NoCompiler.Auto", ""]
    if len(w) > 128:
        o.append(f"set_option maxRecDepth {64 * len(w)}\n")
    o += ["namespace Bench.Slice", "open NoCompiler", ""]
    o.append(f"def code : Code := ⟨0x{lo:x}#64, #[" + ", ".join(f"0x{x}#32" for x in w) + "]⟩")
    for pc in range(lo, hi, 4):
        if pc in instrs:
            o.append(instrs[pc][1])
    o.append("def entries : List Word := [" + ", ".join(f"0x{e:x}#64" for e in entries if lo <= e < hi) + "]")
    text = f["text"]
    if variant == "base":
        text = re.sub(r"\n/-- `[^\n]*` is at level [^\n]*-/\ntheorem \S+_checked :.*", "", text)
    o.append(text)
    if variant == "safe":
        o.append(f"""
def specSafe : Spec Unit where
  pre := fun _ _ => True
  post := fun _ _ _ => True
  stack := {f["frame"]}

theorem {f["id"]}_safe : VerifiedImg code {f["id"]}_dom {f["id"]}_entry specSafe := by
  rintro _ s he _
  nocompiler_auto {f["id"]}_func s he""")
    o.append("\nend Bench.Slice\n")
    return "\n".join(o)


def check(path):
    t0 = time.monotonic()
    r = subprocess.run(capped(["lake", "env", "lean", "-Dprofiler=true", path]), cwd=LEAN, capture_output=True,
                       text=True)
    wall = time.monotonic() - t0
    p = profile(r.stdout + r.stderr)
    err = None
    if r.returncode != 0:
        err = next((l for l in (r.stdout + r.stderr).splitlines() if "error" in l), "rc %d" % r.returncode)
    return {"rc": r.returncode, "wall_s": round(wall, 2), "total_ms": round(sum(p.values()), 1),
            "kernel_ms": round(p.get("type checking", 0.0), 1), "error": err}


def main():
    image, out = sys.argv[1], sys.argv[2]
    mx = int(sys.argv[sys.argv.index("--max") + 1]) if "--max" in sys.argv else None
    only = sys.argv[sys.argv.index("--only") + 1] if "--only" in sys.argv else None
    os.makedirs(out, exist_ok=True)
    base, words, instrs, entries, funcs = parse(image)
    if only:
        funcs = [f for f in funcs if f["name"] == only]
    rows = []
    for k, f in enumerate(funcs[:mx] if mx else funcs):
        span = (max(a + n for a, n in f["dom"]) - min(a for a, _ in f["dom"])) // 4
        row = {"name": f["name"], "instrs": f["n"], "region_instrs": sum(n for _, n in f["dom"]) // 4,
               "span": span, "provable": provable(f, instrs)}
        if span > MAX_SPAN:
            row["skipped"] = f"its code region spans {span} words (> {MAX_SPAN}): one array literal that long does not elaborate"
            rows.append(row)
            print(json.dumps(row), flush=True)
            continue
        for v in ["base", "checked"] + (["safe"] if row["provable"] else []):
            p = os.path.join(out, f"F{k}_{v}.lean")
            open(p, "w").write(slice_file(f, base, words, instrs, entries, v))
            row[v] = check(p)
        b = row["base"]
        for v in ("checked", "safe"):
            if v in row and row[v]["rc"] == 0 and b["rc"] == 0:
                ref = row["checked"] if v == "safe" else b
                row[v]["total_ms_per_instr"] = round((row[v]["total_ms"] - ref["total_ms"]) / f["n"], 2)
                row[v]["kernel_ms_per_instr"] = round((row[v]["kernel_ms"] - ref["kernel_ms"]) / f["n"], 2)
        rows.append(row)
        print(json.dumps(row), flush=True)
    json.dump(rows, open(os.path.join(out, "rows.json"), "w"), indent=1)
    return 0


sys.exit(main())
