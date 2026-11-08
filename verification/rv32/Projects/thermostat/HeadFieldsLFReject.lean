import Projects.thermostat.HttpParseCode
import Projects.thermostat.Quiet
namespace E5R.Thermostat.HeadFieldsLFReject
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (hp : c.pc=0x80003428#32) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x8000342c#32 ∧ d.get 1=400#32 ∧
      (∀ r : Reg, r≠1 → d.get r=c.get r) ∧ d.sameCsr c := by
  let d := c.wr 1 400#32 0x8000342c#32
  have step : Quiet.Step B img ⟨c,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147497000) fun o => ?_
    rw [exec_opimm,Core.get_zero,hp];rfl
  exact ⟨d,.single step,rfl,by simp [d,Core.wr_get],fun r h => by simp [d,Core.wr_get_ne,h],rfl⟩
end E5R.Thermostat.HeadFieldsLFReject
