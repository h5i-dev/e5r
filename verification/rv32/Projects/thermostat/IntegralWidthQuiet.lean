-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.IntegralWidth
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.IntegralWidth
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (fmt : Word) (h19 : c.get 19 = fmt)
    (hm : Memory.Block B fmt 14) (ha : fmt.toNat%4 = 0)
    (hz : ramRead ram (fmt+12#32) .h = 0#32)
    (hp : c.pc = 0x800045c6#32) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x800045d0#32 ∧
      d.get 21 = 0#32 ∧ d.get 27 = 0#32 ∧ (∀ r : Reg, r ≠ 21 → r ≠ 27 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 21 (0#32) 0x800045c8#32
  let c2 := c1.wr 27 (0#32) 0x800045cc#32
  let c3 := c2.goto 0x800045d0#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact pi2147501510) fun o => ?_
    rw [exec_opimm,Core.get_zero,hp];first | rfl | (rw [hp]; rfl)
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x800045c8#32).getLsbD 0 = false;decide) pi2147501512 fun o => ?_
    have hv : c1.get 19 = fmt := by simp [c1,Core.wr_get_ne,Core.wr_get,h19]
    rw [exec_load,hv,interp_load_ram (B := B) (img := img) (w := .h) o
      (Memory.half_aligned fmt 6 (by omega)) (Memory.block_access hm (off := 12) (by decide) (by decide)),hz];first | rfl | (rw [hp]; rfl)
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x800045cc#32).getLsbD 0 = false;decide) pi2147501516 fun o => ?_
    have hv : c2.get 27 = 0#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h19]
    rw [exec_branch,hv]
    simp only [taken,show (0#32).toNat = 0 from rfl,Nat.not_lt_zero,decide_false,ite_false];first | rfl | (rw [hp]; rfl)
  refine ⟨c3,.step s0 (.step s1 (.single s2)),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19]
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19]
  · intro r h21 h27
    simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h21,h27]

end E5R.Thermostat.IntegralWidth
