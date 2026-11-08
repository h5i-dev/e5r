import Projects.thermostat.ResponseHeadCode
import Projects.thermostat.QuietRam
import Projects.thermostat.ResponseHeadBodyMath
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ResponseHeadBodyNo
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)  (h25 : c.get 25=0#32) (h11 : c.get 11=192#32)
    (hp : c.pc=0x80003f02#32) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80003f26#32 ∧
      d.get 19=1#32 ∧ d.get 17=9#32 ∧ (∀ r : Reg, r≠19 → r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x80003f06#32
  let c2 := c1.wr 19 (1#32) 0x80003f08#32
  let c3 := c2.wr 17 (9#32) 0x80003f0a#32
  let c4 := c3.goto 0x80003f26#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rh2147499778) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v25 : c.get 25=0#32 := by simp [Core.wr_get_ne,Core.wr_get,h25,h11]
    rw [exec_branch,v25,Core.get_zero,show taken .ne 0#32 (0 : Word)=false by decide]
    simp only [Bool.false_eq_true,ite_false];rw [hp];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80003f06#32).getLsbD 0=false;decide) rh2147499782 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80003f08#32).getLsbD 0=false;decide) rh2147499784 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80003f0a#32).getLsbD 0=false;decide) rh2147499786 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v11 : c3.get 11=192#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h25,h11]
    have v17 : c3.get 17=9#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h25,h11]
    rw [exec_branch,v11,v17,show taken .geu 192#32 9#32=true by decide]
    simp only [ite_true]
    rw [show c3.pc=0x80003f0a#32 by rfl,show 0x80003f0a#32+28#32=0x80003f26#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c4,.step t0 (.step t1 (.step t2 (.single t3))),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h25,h11]
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h25,h11]
  · intro reg h19 h17;simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h25,h11,h19,h17]
end E5R.Thermostat.ResponseHeadBodyNo
