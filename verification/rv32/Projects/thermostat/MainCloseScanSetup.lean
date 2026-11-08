import Projects.thermostat.MainCloseCode
import Projects.thermostat.QuietRam
set_option autoImplicit false
namespace E5R.Thermostat.MainCloseScanSetup
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (hp : c.pc=0x80002584#32) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80002586#32 ∧ d.get 23=0#32 ∧
      (∀ r : Reg, r≠23 → d.get r=c.get r) ∧ d.sameCsr c := by
  let d := c.wr 23 0#32 0x80002586#32
  have step : Quiet.Step B img ⟨c,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact re2147493252) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok d ram [],[]⟩
    rw [exec_opimm,Core.get_zero,hp];rfl
  refine ⟨d,.single step,rfl,?_,?_,Core.sameCsr_wr c _ _ _⟩
  · simp [d,Core.wr_get]
  · intro r ne
    exact Core.wr_get_ne _ _ _ _ _ ne
end E5R.Thermostat.MainCloseScanSetup
