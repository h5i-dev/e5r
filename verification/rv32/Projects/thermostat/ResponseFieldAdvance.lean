import Projects.thermostat.ResponseHeadCode
import Projects.thermostat.QuietRam
import Projects.thermostat.ResponseFieldMath
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ResponseFieldAdvance
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (src : Word) (n : Nat) (hpos : 0<n) (hn : n≤16) (h29 : c.get 29=src) (h30 : c.get 30=BitVec.ofNat 32 n)
    (hp : c.pc=0x80003ea8#32) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=(if n=1 then 0x80003ec2#32 else 0x80003eb0#32) ∧
      d.get 30=BitVec.ofNat 32 (n-1) ∧ d.get 29=src+1#32 ∧ (∀ r : Reg, r≠30 → r≠29 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 30 (BitVec.ofNat 32 (n-1)) 0x80003eaa#32
  let c2 := c1.wr 29 (src+1#32) 0x80003eac#32
  let c3 := c2.goto (if n=1 then 0x80003ec2#32 else 0x80003eb0#32)
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rh2147499688) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,h30]
    change Observed.interp B img o (.done (c.wr 30 ((BitVec.ofNat 32 n)+0xffffffff#32) (c.pc+2#32))) ram 0 [] [] = _
    rw [ParamMath.decrement n hpos,hp];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80003eaa#32).getLsbD 0=false;decide) rh2147499690 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v29 : c1.get 29=src := by simp [c1,Core.wr_get_ne,Core.wr_get,h29,h30]
    rw [exec_opimm,v29];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80003eac#32).getLsbD 0=false;decide) rh2147499692 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v30 : c2.get 30=BitVec.ofNat 32 (n-1) := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h29,h30]
    rw [exec_branch,v30,Core.get_zero,ResponseFieldMath.counter n hpos hn]
    by_cases he : n=1
    · simp only [decide_eq_true he,ite_true]
      rw [show c2.pc=0x80003eac#32 by rfl,show 0x80003eac#32+22#32=0x80003ec2#32 by decide +kernel,jump_ok _ _ (by decide)]
      simp only [c3,he,ite_true];first | rfl | (rw [hp];rfl)
    · simp only [decide_eq_false he,Bool.false_eq_true,ite_false]
      simp only [c3,he,ite_false];first | rfl | (rw [hp];rfl)
  refine ⟨c3,.step t0 (.step t1 (.single t2)),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h29,h30]
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h29,h30]
  · intro reg h30 h29;simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h29,h30,h30,h29]
end E5R.Thermostat.ResponseFieldAdvance
