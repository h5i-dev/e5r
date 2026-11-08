-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.I16SmallIndex
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.I16SmallIndex
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) 
    (hp : c.pc = 0x80004f3a#32) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80004f3c#32 ∧
      d.get 14 = 3#32 ∧ (∀ r : Reg, r ≠ 14 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 14 (3#32) 0x80004f3c#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact di2147503930) fun o => ?_
    rw [exec_opimm,Core.get_zero,hp];first | rfl | (rw [hp]; rfl)
  refine ⟨c1,.single s0,rfl,?_ ,?_ ,by rfl⟩
  · simp [c1,Core.wr_get_ne,Core.wr_get]
  · intro r h14
    simp [c1,Core.wr_get_ne,Core.wr_get,h14]

end E5R.Thermostat.I16SmallIndex
