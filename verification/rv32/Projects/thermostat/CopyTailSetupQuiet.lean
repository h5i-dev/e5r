-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.CopyTailSetup
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
open E5R E5R.Thermostat
namespace E5R.Thermostat.CopyTailSetup
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (src finish : Word) (n bulk rem : Nat)
    (hp : c.pc=0x80005222#32) (h11 : c.get 11=src) (h12 : c.get 12=BitVec.ofNat 32 n)
    (h13 : c.get 13=finish) (h15 : c.get 15=BitVec.ofNat 32 bulk)
    (hm : BitVec.ofNat 32 n &&& 3#32=BitVec.ofNat 32 rem) (hw : finish.toNat+rem<2^32) :
    ∃ d, Quiet.Steps B img 5 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=(if rem=0 then 0x8000530c#32 else 0x800052fc#32) ∧
      d.get 11=src+BitVec.ofNat 32 bulk ∧ d.get 12=BitVec.ofNat 32 rem ∧
      (∀ r : Reg, r≠11 → r≠12 → r≠14 → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.goto 0x800052f0#32
  let b := a.wr 11 (src+BitVec.ofNat 32 bulk) 0x800052f2#32
  let z := b.wr 12 (BitVec.ofNat 32 rem) 0x800052f4#32
  let u := z.wr 14 (finish+BitVec.ofNat 32 rem) 0x800052f8#32
  let d := u.goto (if rem=0 then 0x8000530c#32 else 0x800052fc#32)
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact cp2147504674) fun o => ?_
    rw [exec_jal,hp]
    change interp B img o (jump c 0x800052f0#32) ram 0 [] = _
    rw [jump_ok _ _ (by decide)];rfl
  have t1 : Quiet.Step B img ⟨a,ram⟩ ⟨b,ram⟩ := by
    refine QuietDet.step_of (by change (0x800052f0#32).getLsbD 0=false;decide) cp2147504880 fun o => ?_
    have a11 : a.get 11=src := h11
    have a15 : a.get 15=BitVec.ofNat 32 bulk := h15
    rw [exec_op,a11,a15];rfl
  have t2 : Quiet.Step B img ⟨b,ram⟩ ⟨z,ram⟩ := by
    refine QuietDet.step_of (by change (0x800052f2#32).getLsbD 0=false;decide) cp2147504882 fun o => ?_
    have b12 : b.get 12=BitVec.ofNat 32 n := by simp [b,a,Core.wr_get_ne,h12]
    rw [exec_opimm,b12]
    change interp B img o (.done (b.wr 12 (BitVec.ofNat 32 n &&& 3#32) 0x800052f4#32)) ram 0 [] = _
    rw [hm];rfl
  have t3 : Quiet.Step B img ⟨z,ram⟩ ⟨u,ram⟩ := by
    refine QuietDet.step_of (by change (0x800052f4#32).getLsbD 0=false;decide) cp2147504884 fun o => ?_
    have z13 : z.get 13=finish := by simp [z,b,a,Core.wr_get_ne,h13]
    have z12 : z.get 12=BitVec.ofNat 32 rem := by simp [z,Core.wr_get]
    rw [exec_op,z13,z12];rfl
  have t4 : Quiet.Step B img ⟨u,ram⟩ ⟨d,ram⟩ := by
    refine QuietDet.step_of (by change (0x800052f8#32).getLsbD 0=false;decide) cp2147504888 fun o => ?_
    have u13 : u.get 13=finish := by simp [u,z,b,a,Core.wr_get_ne,h13]
    have u14 : u.get 14=finish+BitVec.ofNat 32 rem := by simp [u,Core.wr_get]
    have ht : taken .geu finish (finish+BitVec.ofNat 32 rem)=decide (rem=0) := by
      change (!decide (finish.toNat<(finish+BitVec.ofNat 32 rem).toNat))=decide (rem=0)
      rw [WordZero.add_nat finish rem hw]
      by_cases hr : rem=0
      · simp only [hr,Nat.add_zero,Nat.lt_irrefl,decide_false,Bool.not_false,decide_true]
      · rw [decide_eq_true (show finish.toNat<finish.toNat+rem by omega),decide_eq_false hr];rfl
    rw [exec_branch,u13,u14,ht]
    by_cases hr : rem=0
    · simp only [d,hr,decide_true,ite_true]
      change interp B img o (jump u 0x8000530c#32) ram 0 [] = _
      rw [jump_ok _ _ (by decide)];rfl
    · simp only [d,decide_eq_false hr,ite_false,ite_eq_right hr];rfl
  refine ⟨d,.step t0 (.step t1 (.step t2 (.step t3 (.single t4)))),rfl,?_,?_,?_,by rfl⟩
  · simp [d,u,z,b,Core.wr_get_ne,Core.wr_get]
  · simp [d,u,z,Core.wr_get_ne,Core.wr_get]
  · intro reg h11 h12 h14
    simp [d,u,z,b,a,Core.wr_get_ne,h11,h12,h14]

end E5R.Thermostat.CopyTailSetup
