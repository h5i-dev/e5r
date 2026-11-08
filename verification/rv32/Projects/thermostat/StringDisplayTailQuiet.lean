-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.StringDisplayTail
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.StringDisplayTail
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (src len fmt : Word) (h10 : c.get 10 = src) (h11 : c.get 11 = len) (h12 : c.get 12 = fmt)
    (hp : c.pc = 0x8000513e#32) :
    ∃ d, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80004790#32 ∧
      d.get 13 = len ∧ d.get 11 = src ∧ d.get 10 = fmt ∧ d.get 12 = len ∧ d.get 6 = 0x80004146#32 ∧ (∀ r : Reg, r ≠ 13 → r ≠ 11 → r ≠ 10 → r ≠ 12 → r ≠ 6 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 13 (len) 0x80005140#32
  let c2 := c1.wr 11 (src) 0x80005142#32
  let c3 := c2.wr 10 (fmt) 0x80005144#32
  let c4 := c3.wr 12 (len) 0x80005146#32
  let c5 := c4.wr 6 (0x80004146#32) 0x8000514a#32
  let c6 := c5.goto 0x80004790#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact sf2147504446) fun o => ?_
    have hv : c.get 11 = len := by simp [Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x80005140#32).getLsbD 0 = false;decide) sf2147504448 fun o => ?_
    have hv : c1.get 10 = src := by simp [c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x80005142#32).getLsbD 0 = false;decide) sf2147504450 fun o => ?_
    have hv : c2.get 12 = fmt := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (0x80005144#32).getLsbD 0 = false;decide) sf2147504452 fun o => ?_
    have hv : c3.get 13 = len := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine QuietDet.step_of (by change (0x80005146#32).getLsbD 0 = false;decide) sf2147504454 fun o => ?_
    rw [exec_auipc]
    change interp B img o (.done (c4.wr 6 (0x80005146#32+0xfffff000#32) 0x8000514a#32)) ram 0 [] = _
    rw [show 0x80005146#32+0xfffff000#32 = 0x80004146#32 by decide +kernel];first | rfl | (rw [hp]; rfl)
  have s5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000514a#32).getLsbD 0 = false;decide) sf2147504458 fun o => ?_
    have hv : c5.get 6 = 0x80004146#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    rw [exec_jalr,hv]
    change interp B img o (jump c5 ((0x80004146#32+1610#32) &&& ~~~1)) ram 0 [] = _
    rw [show (0x80004146#32+1610#32) &&& ~~~1 = 0x80004790#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp]; rfl)
  refine ⟨c6,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.single s5))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
  · intro r h13 h11 h10 h12 h6
    simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h11,h10,h12,h6]

end E5R.Thermostat.StringDisplayTail
