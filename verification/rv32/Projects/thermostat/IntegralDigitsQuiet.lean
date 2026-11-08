-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.IntegralDigits
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.IntegralDigits
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (writer src len : Word) (h19 : c.get 19 = 0x80005c04#32)
    (h23 : c.get 23 = writer) (h18 : c.get 18 = src) (h9 : c.get 9 = len)
    (h10 : c.get 10 = 0#32) (hrom : B.inRam 0x80005c10#32 4 = false)
    (hp : c.pc = 0x800045ea#32) :
    ∃ d, Quiet.Steps B img 5 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x800046a4#32 ∧
      d.get 6 = 0x800022a0#32 ∧ d.get 10 = writer ∧ d.get 11 = src ∧ d.get 12 = len ∧ (∀ r : Reg, r ≠ 6 → r ≠ 10 → r ≠ 11 → r ≠ 12 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x8000469a#32
  let c2 := c1.wr 6 (0x800022a0#32) 0x8000469e#32
  let c3 := c2.wr 10 (writer) 0x800046a0#32
  let c4 := c3.wr 11 (src) 0x800046a2#32
  let c5 := c4.wr 12 (len) 0x800046a4#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact pi2147501546) fun o => ?_
    have hv : c.get 10 = 0#32 := by simp [Core.wr_get_ne,Core.wr_get,h19,h23,h18,h9,h10]
    rw [exec_branch,hv,Core.get_zero,show E5R.taken .eq (0#32) (0 : Word) = true by decide]
    simp only [ite_true,ite_false]
    try simp only [hp]
    rw [jump_ok _ _ (by change (0x8000469a#32).getLsbD 0 = false;decide)];first | rfl | (rw [hp]; rfl)
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000469a#32).getLsbD 0 = false;decide) pi2147501722 fun o => ?_
    have hv : c1.get 19 = 0x80005c04#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h19,h23,h18,h9,h10]
    rw [exec_load,hv,show 0x80005c04#32+12#32 = 0x80005c10#32 by decide +kernel,
      interp_load_rom (B := B) (img := img) (w := .w) o (by decide) hrom rfl FormatLiterals.cursor_method_word];first | rfl | (rw [hp]; rfl)
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000469e#32).getLsbD 0 = false;decide) pi2147501726 fun o => ?_
    have hv : c2.get 23 = writer := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h19,h23,h18,h9,h10]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (0x800046a0#32).getLsbD 0 = false;decide) pi2147501728 fun o => ?_
    have hv : c3.get 18 = src := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h23,h18,h9,h10]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine QuietDet.step_of (by change (0x800046a2#32).getLsbD 0 = false;decide) pi2147501730 fun o => ?_
    have hv : c4.get 9 = len := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h23,h18,h9,h10]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  refine ⟨c5,.step s0 (.step s1 (.step s2 (.step s3 (.single s4)))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h23,h18,h9,h10]
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h23,h18,h9,h10]
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h23,h18,h9,h10]
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h23,h18,h9,h10]
  · intro r h6 h10 h11 h12
    simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h23,h18,h9,h10,h6,h10,h11,h12]

end E5R.Thermostat.IntegralDigits
