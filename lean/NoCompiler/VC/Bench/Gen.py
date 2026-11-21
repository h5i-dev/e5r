# Usage: python3 -I Gen.py OUTDIR N...
# Writes OUTDIR/StraightN.lean: a chain of N `addi a0, a0, 1` (0x00150513) checked by kernel
# evaluation of the symbolic run over the words in order (`runW`, NoCompiler/VC/Straight.lean). Check each, from lean/, ALWAYS capped:
#   /usr/bin/time -v systemd-run --user --scope --quiet -p MemoryMax=6G -p MemorySwapMax=0 \
#     --setenv=PATH="$PATH" timeout 900 lake env lean OUTDIR/StraightN.lean
# Not part of the build.
import sys, os
out = sys.argv[1]
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
