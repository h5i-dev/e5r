import Projects.thermostat.HttpPutCode
import Projects.thermostat.Quiet
namespace E5R.Thermostat.HttpPutEmpty
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc=0x8000413a#32) (h14 : c.get 14=0#32) :
    Quiet.Steps B img 1 ⟨c,ram⟩ ⟨c.goto 0x80004166#32,ram⟩ := by
  apply Quiet.Steps.single
  refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hp2147500346) fun o => ?_
  rw [exec_branch,h14,Core.get_zero,show taken .eq 0#32 (0 : Word)=true by decide]
  simp only [ite_true]
  rw [hp,show 0x8000413a#32+44#32=0x80004166#32 by decide +kernel,jump_ok _ _ (by decide)]
  rfl
end E5R.Thermostat.HttpPutEmpty
