# Usage: python3 -I Gen.py OUTDIR N...
# Writes OUTDIR/StraightN.lean: a chain of N `addi a0, a0, 1` (0x00150513) checked by kernel
# evaluation of the symbolic run over the words in order (`runW`, NoCompiler/VC/Straight.lean). Check each, from lean/, ALWAYS capped:
#   /usr/bin/time -v systemd-run --user --scope --quiet -p MemoryMax=6G -p MemorySwapMax=0 \
#     --setenv=PATH="$PATH" timeout 900 lake env lean OUTDIR/StraightN.lean
# Not part of the build.
#        python3 -I Gen.py OUTDIR mem N...
# The `mem` form writes OUTDIR/MemN.lean: N instructions alternating `ld a3, 0(a0)` (0x00053683) and
# `sd a3, 8(a0)` (0x00d53423), run by NoCompiler.VC.M.runW inside the code's region: the run succeeds,
# ends at the right pc, and emits two obligations (alignment, permission) per instruction.
import sys, os
out = sys.argv[1]
# The `memchk` form writes OUTDIR/MemChkN.lean: the same run, with every obligation discharged by
# Ob.check from the facts "a0 is 8-aligned" and "a0 starts a 16-byte writable region".
# The `seg` form writes OUTDIR/SegN_K.lean: the memchk chain of N instructions as Code.ofSegs with
# segments of K, and one theorem per segment (the segment's run, every obligation checked).
if len(sys.argv) > 2 and sys.argv[2] == "seg":
    os.makedirs(out, exist_ok=True)
    n, k = int(sys.argv[3]), int(sys.argv[4])
    with open(os.path.join(out, f"Seg{n}_{k}.lean"), "w") as f:
        f.write(f"""import NoCompiler.VC.Seg
namespace NoCompiler.VC.M.Bench
def seg : List (BitVec 32) := (List.range {k}).map fun i => if i % 2 = 0 then 0x00053683#32 else 0x00d53423#32
def segs : List (List (BitVec 32)) := List.replicate {n // k} seg
def D : Dom := [(0x10000#64, 4 * {n})]
def facts : List Fact := [.aligned 10 8, .region 10 16 true]
""")
        for i in range(n // k):
            f.write(f"""set_option maxRecDepth 200000 in
theorem seg_{i} : (runW D (segs.getD {i} []) (SState.init (0x10000#64 + BitVec.ofNat 64 {4 * k * i}))).map
    (fun p => p.2.all (Ob.check facts)) = some true := by decide +kernel
""")
        f.write("end NoCompiler.VC.M.Bench\n")
    sys.exit(0)
if len(sys.argv) > 2 and sys.argv[2] == "memchk":
    os.makedirs(out, exist_ok=True)
    for n in map(int, sys.argv[3:]):
        with open(os.path.join(out, f"MemChk{n}.lean"), "w") as f:
            f.write(f"""import NoCompiler.VC.Ob
namespace NoCompiler.VC.M.Bench
def chain : Code := ⟨0x10000#64, ((List.range {n}).map fun i => if i % 2 = 0 then 0x00053683#32 else 0x00d53423#32).toArray⟩
def facts : List Fact := [.aligned 10 8, .region 10 16 true]
set_option maxRecDepth 200000 in
theorem chain_checked : (runW [(0x10000#64, 4 * {n})] chain.words.toList (SState.init 0x10000#64)).map
    (fun p => p.2.all (Ob.check facts)) = some true := by decide +kernel
end NoCompiler.VC.M.Bench
""")
    sys.exit(0)
if len(sys.argv) > 2 and sys.argv[2] == "mem":
    os.makedirs(out, exist_ok=True)
    for n in map(int, sys.argv[3:]):
        with open(os.path.join(out, f"Mem{n}.lean"), "w") as f:
            f.write(f"""import NoCompiler.VC.Mem
namespace NoCompiler.VC.M.Bench
def chain : Code := ⟨0x10000#64, ((List.range {n}).map fun i => if i % 2 = 0 then 0x00053683#32 else 0x00d53423#32).toArray⟩
set_option maxRecDepth 200000 in
theorem chain_run : (runW [(0x10000#64, 4 * {n})] chain.words.toList (SState.init 0x10000#64)).map
    (fun p => (p.1.pc, p.2.length)) = some (0x10000#64 + BitVec.ofNat 64 (4 * {n}), {2 * n}) := by decide +kernel
end NoCompiler.VC.M.Bench
""")
    sys.exit(0)
os.makedirs(out, exist_ok=True)
for n in map(int, sys.argv[2:]):
    with open(os.path.join(out, f"Straight{n}.lean"), "w") as f:
        f.write(f"""import NoCompiler.VC.Straight
namespace NoCompiler.VC.Bench
def _root_.NoCompiler.VC.Sym.size : Sym → Nat
  | .var _ | .const _ => 1
  | .iop _ a _ => a.size + 1
  | .rop _ a b => a.size + b.size + 1
def chain : Code := ⟨0x10000#64, (List.replicate {n} 0x00150513#32).toArray⟩
-- the run succeeds, ends at the right pc, and a0 is N additions deep
theorem chain_run : (runW chain.words.toList (SState.init 0x10000#64)).map (fun S => (S.pc, (S.reg 10).size)) =
    some (0x10000#64 + BitVec.ofNat 64 (4 * {n}), {n + 1}) := by decide +kernel
end NoCompiler.VC.Bench
""")
