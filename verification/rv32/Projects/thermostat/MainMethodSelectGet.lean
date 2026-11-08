import Projects.thermostat.MainMethodDecodeCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainMethodSelectGet
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) 

    (hp : c.pc=0x80000e16#32) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x8000114e#32 ∧
      d.get 14=0#32 ∧ d.get 0=0#32 ∧ (∀ r : Reg, r≠14 → r≠0 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 14 (0#32) 0x80000e18#32
  let c2 := c1.wr 0 (0#32) 0x8000114e#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact re2147487254) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80000e18#32).getLsbD 0=false;decide) re2147487256 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    rw [exec_jal,Core.set_zero];change Observed.interp B img o (jump _ 0x8000114e#32) ram 0 [] [] = _;rw [jump_ok _ _ (by decide)];rfl
  refine ⟨c2,.step t0 (.single t1),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c2,c1,Core.wr_get_ne,Core.wr_get]
  · simp [c2,c1,Core.wr_get_ne,Core.wr_get]
  · intro reg h14 h0;simp [c2,c1,Core.wr_get_ne,Core.wr_get,h14,h0]
end E5R.Thermostat.MainMethodSelectGet
