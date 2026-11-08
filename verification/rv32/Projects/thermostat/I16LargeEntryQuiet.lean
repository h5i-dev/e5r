-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.I16LargeEntry
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.I16LargeEntry
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (n : Nat) (hn : 1000 ≤ n) (hb : n ≤ 32768)
    (h14 : c.get 14 = BitVec.ofNat 32 n) (h16 : c.get 16 = 1000#32)
    (hp : c.pc = 0x80004e8a#32) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80004e8e#32 ∧
      (∀ r : Reg, d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x80004e8e#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact di2147503754) fun o => ?_
    rw [exec_branch,h14,h16,ParamMath.ult n 1000 (by omega) (by decide),decide_eq_false (show ¬n < 1000 by omega),hp]
    simp only [ite_false];first | rfl | (rw [hp]; rfl)
  refine ⟨c1,.single s0,rfl,?_ ,by rfl⟩
  · intro r 
    simp [c1,Core.wr_get_ne,Core.wr_get,h14,h16]

end E5R.Thermostat.I16LargeEntry
