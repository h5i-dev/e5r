import Projects.thermostat.MainMethodDecodeCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainMethodSmallSetup
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) 

    (hp : c.pc=0x80000d6c#32) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80000d6e#32 ∧
      d.get 17=4#32 ∧ (∀ r : Reg, r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 17 (4#32) 0x80000d6e#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact re2147487084) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,Core.get_zero,hp];rfl
  refine ⟨c1,.single t0,rfl,?_ ,?_ ,by rfl⟩
  · simp [c1,Core.wr_get_ne,Core.wr_get]
  · intro reg h17;simp [c1,Core.wr_get_ne,Core.wr_get,h17]
end E5R.Thermostat.MainMethodSmallSetup
