import Projects.thermostat.ResponseHeadCode
import Projects.thermostat.QuietRam
import Projects.thermostat.HttpPutMath
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ResponseHeadFieldEmpty
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)  (h14 : c.get 14=0#32)
    (hp : c.pc=0x80003e82#32) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80003ece#32 ∧
      d.get 9=1#32 ∧ (∀ r : Reg, r≠9 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 9 (1#32) 0x80003e84#32
  let c2 := c1.goto 0x80003ece#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rh2147499650) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,Core.get_zero,hp];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80003e84#32).getLsbD 0=false;decide) rh2147499652 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v14 : c1.get 14=0#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h14]
    rw [exec_branch,v14,Core.get_zero,show taken .eq 0#32 (0 : Word)=true by decide]
    simp only [ite_true]
    rw [show c1.pc=0x80003e84#32 by rfl,show 0x80003e84#32+74#32=0x80003ece#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c2,.step t0 (.single t1),rfl,?_ ,?_ ,by rfl⟩
  · simp [c2,c1,Core.wr_get_ne,Core.wr_get,h14]
  · intro reg h9;simp [c2,c1,Core.wr_get_ne,Core.wr_get,h14,h9]
end E5R.Thermostat.ResponseHeadFieldEmpty
