import Projects.thermostat.MainMethodDecodeCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainMethodSelectDelete
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) 

    (hp : c.pc=0x80000dec#32) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80001154#32 ∧
      d.get 17=5#32 ∧ d.get 16=69#32 ∧ d.get 14=5#32 ∧ d.get 0=0#32 ∧ (∀ r : Reg, r≠17 → r≠16 → r≠14 → r≠0 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 17 (5#32) 0x80000dee#32
  let c2 := c1.wr 16 (69#32) 0x80000df2#32
  let c3 := c2.wr 14 (5#32) 0x80000df4#32
  let c4 := c3.wr 0 (0#32) 0x80001154#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact re2147487212) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80000dee#32).getLsbD 0=false;decide) re2147487214 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80000df2#32).getLsbD 0=false;decide) re2147487218 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80000df4#32).getLsbD 0=false;decide) re2147487220 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    rw [exec_jal,Core.set_zero];change Observed.interp B img o (jump _ 0x80001154#32) ram 0 [] [] = _;rw [jump_ok _ _ (by decide)];rfl
  refine ⟨c4,.step t0 (.step t1 (.step t2 (.single t3))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · intro reg h17 h16 h14 h0;simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h17,h16,h14,h0]
end E5R.Thermostat.MainMethodSelectDelete
