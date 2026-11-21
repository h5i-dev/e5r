# Usage: python3 -I Art.py ELF WORKDIR [N] [suffix|drop]
# The explore path's kernel cost on a real binary's largest functions, on its chunk image.
#   1. `nocompiler export --format chunks` (NOCOMPILER, default target/release/nocompiler) of ELF;
#   2. the image without its `_checked` theorems (WORKDIR/ArtImg.lean), compiled once to an .olean;
#   3. for the N largest functions (default 20), by compiled evaluation: the stop points their paths
#      reach (callee entries) and the starts (entry, loop heads, every return address after a call,
#      to a fixed point), as nocompiler_auto's explore path runs them;
#   4. one theorem per start, `(exploreR ...).isSome = true` by `vc_run; rfl` (the kernel evaluates
#      explore and checks the equation), and the kernel time per instruction of each function.
# Every Lean run is capped (6 GB, no swap, 900 s). Not part of the build; results go to WORKDIR.
import os, re, subprocess, sys

elf, work = sys.argv[1], sys.argv[2]
top = int(sys.argv[3]) if len(sys.argv) > 3 else 20
mode = sys.argv[4] if len(sys.argv) > 4 else "suffix"  # how explore reads the words (VC/Chunk.lean)
here = os.path.dirname(os.path.abspath(__file__))
lean_dir = os.path.abspath(os.path.join(here, "..", "..", ".."))
root = os.path.abspath(os.path.join(lean_dir, ".."))
nc = os.environ.get("NOCOMPILER", os.path.join(root, "target", "release", "nocompiler"))
os.makedirs(work, exist_ok=True)
lean_path = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=lean_dir, capture_output=True,
                           text=True, check=True).stdout.strip() + ":" + work


def lean(args, out):
    cmd = ["systemd-run", "--user", "--scope", "--quiet", "-p", "MemoryMax=6G", "-p", "MemorySwapMax=0",
           f"--setenv=PATH={os.environ['PATH']}", f"--setenv=LEAN_PATH={lean_path}", "timeout", "900",
           "lean"] + args
    with open(out, "w") as f:
        r = subprocess.run(cmd, cwd=lean_dir, stdout=f, stderr=subprocess.STDOUT)
    return r.returncode


art = os.path.join(work, "Art.lean")
subprocess.run([nc, "export", "--namespace", "Art.T", "--format", "chunks", "-o", art, elf], check=True)
src = open(art).read()
lines, out, i = src.split("\n"), [], 0
while i < len(lines):
    # The level checks go (685 of them do not fit one module); the chunk theorems stay
    # (nocompiler_auto's explore path runs over a function's chunk through them).
    if lines[i].startswith("theorem ") and "_checked :" in lines[i]:
        if out and out[-1].startswith("/--") and out[-1].rstrip().endswith("-/"):
            out.pop()
        i += 1
        while i < len(lines) and lines[i].startswith("  "):
            i += 1
        continue
    out.append(lines[i])
    i += 1
open(os.path.join(work, "ArtImg.lean"), "w").write("\n".join(out))
if lean(["--root=" + work, "-o", os.path.join(work, "ArtImg.olean"), os.path.join(work, "ArtImg.lean")],
        os.path.join(work, "img.out")) != 0:
    sys.exit("ArtImg did not compile: " + os.path.join(work, "img.out"))

text = re.search(r"def code : Code := Code.ofChunks (0x[0-9a-f]+)#64 chunks", src).group(1)
ck = dict(re.findall(r"theorem (\w+)_checked : Struct.level \(chunk_(\d+)\.code " + text + r"#64\)", src))
size = {m[0]: int(m[1]) for m in re.findall(r"def (\w+)_func : Struct.Func := ⟨0x[0-9a-f]+#64, (\d+),", src)}
chunk = {a: (int(b), int(c)) for a, b, c in re.findall(r"def chunk_(\d+) : Chunk := ⟨(\d+), (\d+),", src)}
names = sorted(ck, key=lambda n: -size[n])[:top]
hdr = ["import ArtImg", "import NoCompiler.Auto", "open NoCompiler NoCompiler.VC.M Art.T", ""]

stops_lean = hdr + ['''def stops (name : String) (c : Code) (f : Struct.Func) : IO Unit := do
  let heads := (Auto.loopHeads f).map (BitVec.ofNat 64)
  let D : Dom := [(c.base, 4 * c.words.size)]
  let mut ss : List Nat := []
  let mut starts : List Nat := (f.entry :: heads).map (·.toNat)
  let mut todo : List Nat := starts
  while !todo.isEmpty do
    let p :: rest := todo | break
    todo := rest
    match exploreR c D (heads ++ entries) (fun k => c.words.toList.drop k) (f.len + 2) ((p - c.base.toNat) / 4)
        (BitVec.ofNat 64 p) [] with
    | some (ends, _) => for e in ends do
        match e with
        | .cut S _ =>
          if !(heads.contains S.pc) then
            if !(ss.contains S.pc.toNat) then ss := ss ++ [S.pc.toNat]
            match S.reg 1 with
            | .const r => if !(starts.contains r.toNat) then
                starts := starts ++ [r.toNat]; todo := todo ++ [r.toNat]
            | _ => pure ()
        | _ => pure ()
    | none => IO.println s!"NONE {name} {p}"
  IO.println s!"STOPS {name} {ss} STARTS {starts}"
''']
for n in names:
    stops_lean.append(f'#eval stops "{n}" (Chunk.code {text}#64 chunk_{ck[n]}) {n}_func')
open(os.path.join(work, "Stops.lean"), "w").write("\n".join(stops_lean) + "\n")
lean([os.path.join(work, "Stops.lean")], os.path.join(work, "stops.out"))

kern = hdr + ["set_option maxRecDepth 100000", ""]
for j, l in enumerate(open(os.path.join(work, "stops.out"))):
    m = re.match(r"STOPS (\S+) \[(.*?)\] STARTS \[(.*?)\]", l)
    if not m:
        continue
    n = m.group(1)
    stops = [x.strip() for x in m.group(2).split(",") if x.strip()]
    starts = [x.strip() for x in m.group(3).split(",") if x.strip()]
    off, ln = chunk[ck[n]]
    base = int(text, 16) + 4 * off
    c = f"(Chunk.code {text}#64 chunk_{ck[n]})"
    cuts = f"((Auto.loopHeads {n}_func).map (BitVec.ofNat 64) ++ [{', '.join(stops)}].map (BitVec.ofNat 64))"
    fetch = (f"(NoCompiler.VC.M.Chunk.suffix chunk_{ck[n]})" if mode == "suffix"
             else f"(fun k => {c}.words.toList.drop k)")
    kern.append(f'#eval IO.eprintln "== {n} {size[n]} starts={len(starts)}"')
    for i, p in enumerate(starts):
        kern.append(f"theorem t{j}_{i} : (exploreR {c} [(0x{base:x}#64, {4 * ln})] {cuts} {fetch} {size[n] + 2} "
                    f"{(int(p) - base) // 4} {p}#64 []).isSome = true := by\n  vc_run; rfl")
open(os.path.join(work, "Kern.lean"), "w").write("\n".join(kern) + "\n")
lean(["--profile", "-Dprofiler.threshold=1", os.path.join(work, "Kern.lean")], os.path.join(work, "kern.out"))

unit = {"ms": 1, "s": 1000, "us": 1e-3, "μs": 1e-3, "ns": 1e-6}
rows, cur, k = [], None, 0.0
for l in open(os.path.join(work, "kern.out")):
    # The marker may be printed inside a profiler line (output interleaves).
    m = re.search(r"== (\S+) (\d+) starts=(\d+)", l)
    if m:
        if cur:
            rows.append((cur, k))
        cur, k = (m.group(1), int(m.group(2)), int(m.group(3))), 0.0
        continue
    m = re.match(r"type checking took ([\d.]+)(ms|s|us|μs|ns)", l)
    if m and cur:
        k += float(m.group(1)) * unit[m.group(2)]
if cur:
    rows.append((cur, k))
total_i = sum(r[0][1] for r in rows)
total_k = sum(r[1] for r in rows)
for (n, ln, st), k in rows:
    print(f"{n[-40:]:40s} {ln:5d} instr  starts {st:3d}  kernel {k:8.0f} ms  {k / ln:6.2f} ms/instr")
print(f"TOTAL {total_i} instr, kernel {total_k:.0f} ms, {total_k / max(total_i, 1):.2f} ms/instr")
