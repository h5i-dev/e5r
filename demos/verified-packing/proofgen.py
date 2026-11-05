"""Create reviewable proof scripts and development statement exports.
The production check always regenerates its own E5rSpec from PTX and JSON.
"""
from pathlib import Path
import subprocess, hashlib, os
D=Path(__file__).resolve().parent
W=Path('/mnt/scratch/e5r-ptx-demo/proofs'); W.mkdir(parents=True,exist_ok=True)
exe=os.environ.get('E5R_VERIFY','/mnt/scratch/e5r-ptx-demo/cargo/release/e5r')
for op in ['unpack','pack','threshold']:
    dest=W/op;dest.mkdir(exist_ok=True)
    s=subprocess.check_output([exe,'ptx','export','--namespace','E5rSpec',str(D/f'{op}.ptx')],text=True)
    s=s.replace('import Ptx.Syntax','import Ptx.Auto.Packing').replace('end E5rSpec',f'''open Ptx.Auto
 def spec : Packing.Spec := ⟨.{op}, "input", "output", "n"⟩
 def statement : Prop := Packing.Spec.Correct spec «{op}»
end E5rSpec''')
    (dest/'E5rSpec.lean').write_text(s)
    manifest='/- e5r-proof '+ ' '.join(f'{x}={hashlib.sha256((D/f"{op}.{ext}").read_bytes()).hexdigest()}' for x,ext in [('ptx','ptx'),('spec','json')])+' toolchain=leanprover/lean4:v4.35.0 -/'
    indices=[f'8*(t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)+{j}' for j in range(8)] + ['t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat', '(t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)/8']
    if op=='unpack': indices=['t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat', '(t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)/8']
    proof=f'''{manifest}
import E5rSpec
import Ptx.Auto.Tactic
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option linter.unusedSimpArgs false
namespace E5rProof
open Ptx Ptx.Auto Ptx.Auto.Packing Ptx.Auto.Packing.Spec
abbrev S := E5rSpec.spec
abbrev K := E5rSpec.«{op}»

theorem thread : S.ThreadOk K := by
  intro A hp m₀ t ht r p
  have hd := S.oneD A
  obtain ⟨hc,htt,hy,hz,hty,htz⟩ := hd.thread ht
  have hg := hd.gid_lt ht
  obtain ⟨fi,fo,ai,ao,sep,htail,hn,hmax⟩ := hp
  have hp : S.Pre A := ⟨fi,fo,ai,ao,sep,htail,hn,hmax⟩
  simp only [S, E5rSpec.spec, Op.iw, Op.count, reduceIte, Nat.one_mul, true_implies] at fi fo htail
  have hBc : A.B.toNat * t.ctaid.x.toNat = t.ctaid.x.toNat * A.B.toNat := Nat.mul_comm _ _
  have hg32 := hd.gid_bv ht hmax
  have hprod : t.ctaid.x.toNat * A.B.toNat % 4294967296 = t.ctaid.x.toNat * A.B.toNat :=
    Nat.mod_eq_of_lt (by unfold gid at hg; omega)
  have hsum : (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat) % 4294967296 = t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat :=
    Nat.mod_eq_of_lt (by unfold gid at hg; omega)
  unfold gid at *
  refine (wp_sound (f := {40 if op == 'unpack' else 200}) (cut := fun _ => false) ?_).weaken
    fun s m h => ⟨h.2.resolve_left (by simp),h.1⟩
  simp only [ptx_eval, K, E5rSpec.«{op}», launch, S, E5rSpec.spec]
  ptx_addrs [A.base "input", A.base "output"] [{', '.join(indices)}]
  ptx_branches
  all_goals simp only [hprod,hsum] at *
  all_goals (try and_intros)
  all_goals (first
    | trivial
    | (with_reducible exact access_input hp (by simp [S,E5rSpec.spec,Op.count]; omega))
    | (with_reducible exact access_output hp (by omega))
    | (apply load_foot (S := S) (j := 0) (by omega) (by decide))
    | (exact store_foot (S := S) (by omega))
    | (simp only [Post]; intro hi; exfalso; omega)
    | skip)
  all_goals trace_state

theorem correct : E5rSpec.statement := Spec.correct_of rfl thread
end E5rProof
'''
    # Don't overwrite manually developed proof bodies.
    pf=D/f'{op}.lean'
    if not pf.exists(): pf.write_text(proof)
    (dest/'E5rProof.lean').write_text(pf.read_text())
