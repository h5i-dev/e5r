-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.FormatEngineEnd
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.FormatEngineEnd
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) 
    (hp : c.pc = 0x80004b12#32) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80004b18#32 ∧
      d.get 10 = 0#32 ∧ (∀ r : Reg, r ≠ 10 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (0#32) 0x80004b14#32
  let c2 := c1.goto 0x80004b18#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact fe2147502866) fun o => ?_
    rw [exec_opimm,Core.get_zero,hp];first | rfl | (rw [hp]; rfl)
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004b14#32).getLsbD 0 = false;decide) fe2147502868 fun o => ?_
    rw [exec_jal]
    change interp B img o (jump c1 0x80004b18#32) ram 0 [] = _
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp]; rfl)
  refine ⟨c2,.step s0 (.single s1),rfl,?_ ,?_ ,by rfl⟩
  · simp [c2,c1,Core.wr_get_ne,Core.wr_get]
  · intro r h10
    simp [c2,c1,Core.wr_get_ne,Core.wr_get,h10]

end E5R.Thermostat.FormatEngineEnd
