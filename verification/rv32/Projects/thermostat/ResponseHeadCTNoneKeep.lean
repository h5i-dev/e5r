import Projects.thermostat.ResponseHeadCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ResponseHeadCTNoneKeep
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)  (h16 : c.get 16=0#32)
    (hp : c.pc=0x80003ece#32) :
    ∃ d, Quiet.Steps B img 7 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80003ee2#32 ∧
      d.get 24=0#32 ∧ d.get 20=0#32 ∧ d.get 21=1#32 ∧ d.get 18=1#32 ∧ d.get 8=1#32 ∧ (∀ r : Reg, r≠24 → r≠20 → r≠21 → r≠18 → r≠8 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 24 (0#32) 0x80003ed0#32
  let c2 := c1.wr 20 (0#32) 0x80003ed2#32
  let c3 := c2.wr 21 (1#32) 0x80003ed4#32
  let c4 := c3.wr 18 (1#32) 0x80003ed6#32
  let c5 := c4.goto 0x80003eca#32
  let c6 := c5.wr 8 (1#32) 0x80003ecc#32
  let c7 := c6.goto 0x80003ee2#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rh2147499726) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80003ed0#32).getLsbD 0=false;decide) rh2147499728 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80003ed2#32).getLsbD 0=false;decide) rh2147499730 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80003ed4#32).getLsbD 0=false;decide) rh2147499732 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80003ed6#32).getLsbD 0=false;decide) rh2147499734 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v16 : c4.get 16=0#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h16]
    rw [exec_branch,v16,Core.get_zero,show taken .eq 0#32 (0 : Word)=true by decide]
    simp only [ite_true]
    rw [show c4.pc=2147499734#32 by rfl,show 2147499734#32+4294967284#32=2147499722#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80003eca#32).getLsbD 0=false;decide) rh2147499722 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x80003ecc#32).getLsbD 0=false;decide) rh2147499724 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    rw [exec_jal]
    change Observed.interp B img o (jump c6 (0x80003ecc#32+22#32)) ram 0 [] [] = _
    rw [show 0x80003ecc#32+22#32=0x80003ee2#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c7,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.single t6)))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h16]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h16]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h16]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h16]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h16]
  · intro reg h24 h20 h21 h18 h8;simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h16,h24,h20,h21,h18,h8]
end E5R.Thermostat.ResponseHeadCTNoneKeep
