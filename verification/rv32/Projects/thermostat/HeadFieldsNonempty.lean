import Projects.thermostat.HttpParseCode
import Projects.thermostat.Quiet
namespace E5R.Thermostat.HeadFieldsNonempty
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (start last : Word)
    (hp : c.pc=0x80002fb8#32) (h24 : c.get 24=start) (h26 : c.get 26=last)
    (ht : taken .geu start last=false) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80002fbc#32 ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  let d := c.goto 0x80002fbc#32
  have step : Quiet.Step B img ⟨c,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495864) fun o => ?_
    rw [exec_branch,h24,h26,ht,hp];rfl
  exact ⟨d,.single step,rfl,fun _ => rfl,rfl⟩
end E5R.Thermostat.HeadFieldsNonempty
