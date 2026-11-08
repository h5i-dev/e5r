import Projects.thermostat.ResponseHeadCode
import Projects.thermostat.QuietRam
import Projects.thermostat.ResponseHeadBodyMath
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ResponseHeadBodyYes
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)  (h25 : c.get 25=1#32) (h11 : c.get 11=192#32)
    (hp : c.pc=0x80003f02#32) :
    ∃ d, Quiet.Steps B img 7 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80003f26#32 ∧
      d.get 9=0x800056b8#32 ∧ d.get 19=0x80005d19#32 ∧ d.get 17=9#32 ∧ (∀ r : Reg, r≠9 → r≠19 → r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x80003f10#32
  let c2 := c1.wr 9 (0x80005000#32) 0x80003f14#32
  let c3 := c2.wr 9 (0x800056b8#32) 0x80003f18#32
  let c4 := c3.wr 19 (0x80006000#32) 0x80003f1c#32
  let c5 := c4.wr 19 (0x80005d19#32) 0x80003f20#32
  let c6 := c5.wr 17 (9#32) 0x80003f22#32
  let c7 := c6.goto 0x80003f26#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rh2147499778) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v25 : c.get 25=1#32 := by simp [Core.wr_get_ne,Core.wr_get,h25,h11]
    rw [exec_branch,v25,Core.get_zero,show taken .ne 1#32 (0 : Word)=true by decide]
    simp only [ite_true]
    rw [hp,show 0x80003f02#32+14#32=0x80003f10#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80003f10#32).getLsbD 0=false;decide) rh2147499792 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    rw [exec_lui];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80003f14#32).getLsbD 0=false;decide) rh2147499796 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v9 : c2.get 9=0x80005000#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h25,h11]
    rw [exec_opimm,v9];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80003f18#32).getLsbD 0=false;decide) rh2147499800 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    rw [exec_lui];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80003f1c#32).getLsbD 0=false;decide) rh2147499804 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v19 : c4.get 19=0x80006000#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h25,h11]
    rw [exec_opimm,v19];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80003f20#32).getLsbD 0=false;decide) rh2147499808 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x80003f22#32).getLsbD 0=false;decide) rh2147499810 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v11 : c6.get 11=192#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h25,h11]
    have v17 : c6.get 17=9#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h25,h11]
    rw [exec_branch,v11,v17,show taken .ltu 192#32 9#32=false by decide]
    simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  refine ⟨c7,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.single t6)))))),rfl,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h25,h11]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h25,h11]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h25,h11]
  · intro reg h9 h19 h17;simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h25,h11,h9,h19,h17]
end E5R.Thermostat.ResponseHeadBodyYes
