import Projects.thermostat.ResponseHeadCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ResponseHeadCTSomeClose
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)  (h16 : c.get 16=1#32)
    (hp : c.pc=0x80003ec2#32) :
    ∃ d, Quiet.Steps B img 5 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80003ee2#32 ∧
      d.get 20=2#32 ∧ d.get 24=14#32 ∧ d.get 8=0x80005d1b#32 ∧ (∀ r : Reg, r≠20 → r≠24 → r≠8 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 20 (2#32) 0x80003ec4#32
  let c2 := c1.wr 24 (14#32) 0x80003ec6#32
  let c3 := c2.goto 0x80003eda#32
  let c4 := c3.wr 8 (0x80006000#32) 0x80003ede#32
  let c5 := c4.wr 8 (0x80005d1b#32) 0x80003ee2#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rh2147499714) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80003ec4#32).getLsbD 0=false;decide) rh2147499716 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80003ec6#32).getLsbD 0=false;decide) rh2147499718 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v16 : c2.get 16=1#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h16]
    rw [exec_branch,v16,Core.get_zero,show taken .ne 1#32 (0 : Word)=true by decide]
    simp only [ite_true]
    rw [show c2.pc=2147499718#32 by rfl,show 2147499718#32+20#32=2147499738#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80003eda#32).getLsbD 0=false;decide) rh2147499738 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    rw [exec_lui];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80003ede#32).getLsbD 0=false;decide) rh2147499742 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v8 : c4.get 8=0x80006000#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h16]
    rw [exec_opimm,v8];first | rfl | (rw [hp];rfl)
  refine ⟨c5,.step t0 (.step t1 (.step t2 (.step t3 (.single t4)))),rfl,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h16]
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h16]
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h16]
  · intro reg h20 h24 h8;simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h16,h20,h24,h8]
end E5R.Thermostat.ResponseHeadCTSomeClose
