# Usage: python3 -I Prove.py WORKDIR [N]
# The whole nocompiler_auto proof (explore and the goals after it) on a binary's N largest functions
# (default 20) that the safety-only specification can take: a `_dom` (every callee passed the profile
# check), no loops (an invariant and a measure would be the function's own), no callees.
# Specification: any entry; returns, preserving the ABI; reads only .rodata; writes only its frame.
# WORKDIR is Art.py's (Art.lean, ArtImg.olean). One module per function, each capped (6 GB, no
# swap, 900 s); cost = every profile category but import and initialization, per instruction.
import os, re, subprocess, sys

work = sys.argv[1]
top = int(sys.argv[2]) if len(sys.argv) > 2 else 20
here = os.path.dirname(os.path.abspath(__file__))
lean_dir = os.path.abspath(os.path.join(here, "..", "..", ".."))
lean_path = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=lean_dir, capture_output=True,
                           text=True, check=True).stdout.strip() + ":" + work
unit = {"ns": 1e-6, "us": 1e-3, "μs": 1e-3, "ms": 1.0, "s": 1000.0}

src = open(os.path.join(work, "Art.lean")).read()
funcs = {}
for m in re.finditer(r"def (\w+)_func : Struct.Func := ⟨0x[0-9a-f]+#64, (\d+), (\[.*?\])⟩", src):
    funcs[m.group(1)] = (int(m.group(2)), ".loop" in m.group(3))
frame = {m[0]: int(m[1]) for m in re.findall(r"def (\w+)_frame : Struct.Frame := ⟨(\d+),", src)}
doms = dict(re.findall(r"def (\w+)_dom : Dom := (\[.*?\])\n", src))
rodata = "seg_rodata" in src
cands = [n for n in funcs if n in doms and not funcs[n][1] and doms[n].count("(") == 1]
cands.sort(key=lambda n: -funcs[n][0])
rows = []
for j, n in enumerate(cands[:top]):
    path = os.path.join(work, f"P{j}.lean")
    reads = "[seg_rodata.region]" if rodata else "[]"
    open(path, "w").write(f"""import ArtImg
import NoCompiler.Auto
namespace Art.P{j}
open NoCompiler Art.T

def specSafe : Spec Unit where
  pre := fun _ _ => True
  post := fun _ _ _ => True
  reads := fun _ _ => {reads}
  stack := {frame.get(n, 0)}

theorem safe : VerifiedImg code {n}_dom {n}_entry specSafe := by
  rintro _ s he _
  nocompiler_auto {n}_func s he

end Art.P{j}
""")
    cmd = ["systemd-run", "--user", "--scope", "--quiet", "-p", "MemoryMax=6G", "-p", "MemorySwapMax=0",
           f"--setenv=PATH={os.environ['PATH']}", f"--setenv=LEAN_PATH={lean_path}", "timeout", "900",
           "lean", "-Dprofiler=true", path]
    r = subprocess.run(cmd, cwd=lean_dir, capture_output=True, text=True)
    out = r.stdout + r.stderr
    open(path[:-5] + ".out", "w").write(out)
    prof = {}
    for m in re.finditer(r"^\s+(.+?) ([\d.]+)(ns|us|μs|ms|s)$", out.split("cumulative profiling times:")[-1], re.M):
        prof[m.group(1)] = float(m.group(2)) * unit[m.group(3)]
    total = sum(v for k, v in prof.items() if k not in ("import", "initialization"))
    kern = prof.get("type checking", 0.0)
    err = next((l for l in out.splitlines() if "error" in l), None) if r.returncode else None
    ln = funcs[n][0]
    rows.append((n, ln, r.returncode, total, kern, err))
    print(f"{n[-40:]:40s} {ln:4d} instr  rc {r.returncode}  total {total:8.0f} ms {total / ln:7.2f} ms/instr  "
          f"kernel {kern / ln:6.2f} ms/instr" + (f"  ERROR {err[:120]}" if err else ""), flush=True)
ok = [r for r in rows if r[2] == 0]
ti = sum(r[1] for r in ok)
tt = sum(r[3] for r in ok)
tk = sum(r[4] for r in ok)
print(f"PROVED {len(ok)} of {len(rows)}: {ti} instr, total {tt:.0f} ms, {tt / max(ti, 1):.2f} ms/instr, "
      f"kernel {tk / max(ti, 1):.2f} ms/instr")
