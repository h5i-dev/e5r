-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.IntegralSetup
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.IntegralSetup
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (sp fmt src len litPrefix prefixLen : Word)
    (hs : c.get 2 = sp) (h10 : c.get 10 = fmt) (h12 : c.get 12 = litPrefix)
    (h13 : c.get 13 = prefixLen) (h14 : c.get 14 = src) (h15 : c.get 15 = len)
    (hp : c.pc = 0x80004530#32) :
    ∃ d, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x8000453c#32 ∧
      d.get 8 = sp+64#32 ∧ d.get 9 = len ∧ d.get 18 = src ∧ d.get 20 = prefixLen ∧ d.get 21 = litPrefix ∧ d.get 19 = fmt ∧ (∀ r : Reg, r ≠ 8 → r ≠ 9 → r ≠ 18 → r ≠ 20 → r ≠ 21 → r ≠ 19 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 8 (sp+64#32) 0x80004532#32
  let c2 := c1.wr 9 (len) 0x80004534#32
  let c3 := c2.wr 18 (src) 0x80004536#32
  let c4 := c3.wr 20 (prefixLen) 0x80004538#32
  let c5 := c4.wr 21 (litPrefix) 0x8000453a#32
  let c6 := c5.wr 19 (fmt) 0x8000453c#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact pi2147501360) fun o => ?_
    rw [exec_opimm,hs,hp];first | rfl | (rw [hp]; rfl)
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004532#32).getLsbD 0 = false;decide) pi2147501362 fun o => ?_
    have hv : c1.get 15 = len := by simp [c1,Core.wr_get_ne,Core.wr_get,hs,h10,h12,h13,h14,h15]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004534#32).getLsbD 0 = false;decide) pi2147501364 fun o => ?_
    have hv : c2.get 14 = src := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h12,h13,h14,h15]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004536#32).getLsbD 0 = false;decide) pi2147501366 fun o => ?_
    have hv : c3.get 13 = prefixLen := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h12,h13,h14,h15]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004538#32).getLsbD 0 = false;decide) pi2147501368 fun o => ?_
    have hv : c4.get 12 = litPrefix := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h12,h13,h14,h15]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  have s5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000453a#32).getLsbD 0 = false;decide) pi2147501370 fun o => ?_
    have hv : c5.get 10 = fmt := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h12,h13,h14,h15]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  refine ⟨c6,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.single s5))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h12,h13,h14,h15]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h12,h13,h14,h15]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h12,h13,h14,h15]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h12,h13,h14,h15]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h12,h13,h14,h15]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h12,h13,h14,h15]
  · intro r h8 h9 h18 h20 h21 h19
    simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h12,h13,h14,h15,h8,h9,h18,h20,h21,h19]

end E5R.Thermostat.IntegralSetup
