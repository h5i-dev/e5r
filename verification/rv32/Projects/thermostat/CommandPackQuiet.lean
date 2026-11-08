-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.CommandPack
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.CommandPack
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (hp : c.pc = 0x8000220c#32) :
    Quiet.Steps B img 3 ⟨c,ram⟩ ⟨execute c,ram⟩ := by
  let c1 := c.wr 11 (c.get 11 <<< 16) 0x8000220e#32
  let c2 := c1.wr 10 (c.get 10 ||| c.get 12) 0x80002210#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact wd2147492364) fun o => ?_
    rw [exec_opimm,hp];rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000220e#32).getLsbD 0 = false;decide) wd2147492366 fun o => ?_
    have h10 : c1.get 10 = c.get 10 := by simp [c1,Core.wr_get_ne]
    have h12 : c1.get 12 = c.get 12 := by simp [c1,Core.wr_get_ne]
    rw [exec_op,h10,h12];rfl
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨execute c,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002210#32).getLsbD 0 = false;decide) wd2147492368 fun o => ?_
    have h10 : c2.get 10 = c.get 10 ||| c.get 12 := by simp [c2,Core.wr_get]
    have h11 : c2.get 11 = c.get 11 <<< 16 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_op,h10,h11];rfl
  exact .step s0 (.step s1 (.single s2))

end E5R.Thermostat.CommandPack
