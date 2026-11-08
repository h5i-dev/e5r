import Projects.thermostat.EncodeReplyCode
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.EncodeModeOff
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (h13 : c.get 13 = 0#32)
    (hp : c.pc = 0x80001ec6#32) :
    ∃ d, DetSteps B img 5 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80001ef0#32 ∧
      d.get 11 = 3#32 ∧ d.get 12 = 0x80005bf5#32 ∧ (∀ r : Reg, r ≠ 11 → r ≠ 12 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x80001eda#32
  let c2 := c1.wr 11 (3#32) 0x80001edc#32
  let c3 := c2.wr 12 (0x80006000#32) 0x80001ee0#32
  let c4 := c3.wr 12 (0x80005bf5#32) 0x80001ee4#32
  let c5 := c4.goto 0x80001ef0#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact ej2147491526) fun o => ?_
    have hv : c.get 13 = 0#32 := by simp [Core.wr_get_ne,Core.wr_get,h13]
    rw [exec_branch,hv,Core.get_zero,show E5R.taken .eq (0#32) (0 : Word) = true by decide]
    simp only [ite_true,ite_false]
    try simp only [hp]
    rw [jump_ok _ _ (by change (0x80001eda#32).getLsbD 0 = false;decide)];first | rfl | (rw [hp]; rfl)
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x80001eda#32).getLsbD 0 = false;decide) ej2147491546 fun o => ?_
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp]; rfl)
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x80001edc#32).getLsbD 0 = false;decide) ej2147491548 fun o => ?_
    rw [exec_lui];first | rfl | (rw [hp]; rfl)
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine detStep_of (by change (0x80001ee0#32).getLsbD 0 = false;decide) ej2147491552 fun o => ?_
    have hv : c3.get 12 = 0x80006000#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13]
    rw [exec_opimm,hv];first | rfl | (rw [hp]; rfl)
  have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine detStep_of (by change (0x80001ee4#32).getLsbD 0 = false;decide) ej2147491556 fun o => ?_
    rw [exec_jal]
    change interp B img o (jump c4 0x80001ef0#32) ram 0 [] = _
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp]; rfl)
  refine ⟨c5,.step s0 (.step s1 (.step s2 (.step s3 (.single s4)))),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13]
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13]
  · intro r h11 h12
    simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h11,h12]
end E5R.Thermostat.EncodeModeOff
