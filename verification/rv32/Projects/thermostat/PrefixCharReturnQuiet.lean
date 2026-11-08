-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.PrefixCharReturn
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.PrefixCharReturn
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (h10 : c.get 10 = 0#32)
    (hp : c.pc = 0x80004e28#32) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80004e2e#32 ∧
      (∀ r : Reg, d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x80004e2e#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact wp2147503656) fun o => ?_
    have hv : c.get 10 = 0#32 := by simp [Core.wr_get_ne,Core.wr_get,h10]
    rw [exec_branch,hv,Core.get_zero,show E5R.taken .eq (0#32) (0 : Word) = true by decide]
    simp only [ite_true,ite_false]
    try simp only [hp]
    rw [jump_ok _ _ (by change (0x80004e2e#32).getLsbD 0 = false;decide)];first | rfl | (rw [hp]; rfl)
  refine ⟨c1,.single s0,rfl,?_ ,by rfl⟩
  · intro r 
    simp [c1,Core.wr_get_ne,Core.wr_get,h10]

end E5R.Thermostat.PrefixCharReturn
