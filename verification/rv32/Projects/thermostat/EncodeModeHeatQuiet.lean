-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.EncodeModeHeat
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.EncodeModeHeat
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (h13 : c.get 13 = 1#32)
    (hp : c.pc = 0x80001ec6#32) :
    ∃ d, Quiet.Steps B img 7 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80001ef0#32 ∧
      d.get 11 = 4#32 ∧ d.get 12 = 0x80005c00#32 ∧ (∀ r : Reg, r ≠ 11 → r ≠ 12 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x80001ec8#32
  let c2 := c1.wr 11 (1#32) 0x80001eca#32
  let c3 := c2.goto 0x80001ece#32
  let c4 := c3.wr 11 (4#32) 0x80001ed0#32
  let c5 := c4.wr 12 (0x80006000#32) 0x80001ed4#32
  let c6 := c5.wr 12 (0x80005c00#32) 0x80001ed8#32
  let c7 := c6.goto 0x80001ef0#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact ej2147491526) fun o => ?_
    have hv : c.get 13 = 1#32 := by simp [Core.wr_get_ne,Core.wr_get,h13]
    rw [exec_branch,hv,Core.get_zero,show E5R.taken .eq (1#32) (0 : Word) = false by decide]
    simp only [ite_true,ite_false]
    first | rfl | (rw [hp]; rfl)
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001ec8#32).getLsbD 0 = false;decide) ej2147491528 fun o => ?_
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp]; rfl)
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001eca#32).getLsbD 0 = false;decide) ej2147491530 fun o => ?_
    have hv : c2.get 13 = 1#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h13]
    have h11 : c2.get 11 = 1#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h13]
    rw [exec_branch,hv,h11,show E5R.taken .ne (1#32) 1#32 = false by decide]
    simp only [ite_true,ite_false]
    first | rfl | (rw [hp]; rfl)
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001ece#32).getLsbD 0 = false;decide) ej2147491534 fun o => ?_
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp]; rfl)
  have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001ed0#32).getLsbD 0 = false;decide) ej2147491536 fun o => ?_
    rw [exec_lui];first | rfl | (rw [hp]; rfl)
  have s5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001ed4#32).getLsbD 0 = false;decide) ej2147491540 fun o => ?_
    have hv : c5.get 12 = 0x80006000#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13]
    rw [exec_opimm,hv];first | rfl | (rw [hp]; rfl)
  have s6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001ed8#32).getLsbD 0 = false;decide) ej2147491544 fun o => ?_
    rw [exec_jal]
    change interp B img o (jump c6 0x80001ef0#32) ram 0 [] = _
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp]; rfl)
  refine ⟨c7,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.single s6)))))),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13]
  · intro r h11 h12
    simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h11,h12]

end E5R.Thermostat.EncodeModeHeat
