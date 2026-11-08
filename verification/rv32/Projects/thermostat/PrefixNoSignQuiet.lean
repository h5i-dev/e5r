-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.PrefixNoSign
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.PrefixNoSign
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (h12 : c.get 12 = 0xffffffff#32) (h11 : c.get 11 = 0xffffffff#32)
    (hp : c.pc = 0x80004e1a#32) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80004e2e#32 ∧
      (∀ r : Reg, d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x80004e2e#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact wp2147503642) fun o => ?_
    rw [exec_branch,h12,h11,show taken .eq 0xffffffff#32 0xffffffff#32 = true by decide,hp]
    simp only [ite_true]
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp]; rfl)
  refine ⟨c1,.single s0,rfl,?_ ,by rfl⟩
  · intro r 
    simp [c1,Core.wr_get_ne,Core.wr_get,h12,h11]

end E5R.Thermostat.PrefixNoSign
