-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.CopyTwoAfter
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.CopyTwoAfter
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (dst finish : Word) (h14 : c.get 14=dst) (h13 : c.get 13=finish) (h5 : c.get 5=2#32)
    (h11 : c.get 11=0x80005ba6#32) (hlt : E5R.taken .ltu (dst+4#32) finish=true)
    (hp : c.pc = 0x80005246#32) :
    ∃ d, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x8000525e#32 ∧
      d.get 7 = 16#32 ∧ d.get 16 = 16#32 ∧ d.get 6 = 0x80005ba4#32 ∧ (∀ r : Reg, r ≠ 7 → r ≠ 16 → r ≠ 6 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 7 (dst+4#32) 0x8000524a#32
  let c2 := c1.wr 16 (16#32) 0x8000524e#32
  let c3 := c2.wr 6 (0x80005ba4#32) 0x80005252#32
  let c4 := c3.goto 0x80005256#32
  let c5 := c4.wr 7 (0xfffffff0#32) 0x8000525a#32
  let c6 := c5.wr 7 (16#32) 0x8000525e#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact cp2147504710) fun o => ?_
    rw [exec_opimm,h14,hp];first | rfl | (rw [hp]; rfl)
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000524a#32).getLsbD 0 = false;decide) cp2147504714 fun o => ?_
    have hv : c1.get 5=2#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h14,h13,h5,h11]
    rw [exec_opimm,hv];first | rfl | (rw [hp]; rfl)
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000524e#32).getLsbD 0 = false;decide) cp2147504718 fun o => ?_
    have hv11 : c2.get 11=0x80005ba6#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h14,h13,h5,h11]
    have hv5 : c2.get 5=2#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h14,h13,h5,h11]
    rw [exec_op,hv11,hv5];first | rfl | (rw [hp]; rfl)
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (0x80005252#32).getLsbD 0 = false;decide) cp2147504722 fun o => ?_
    have hv7 : c3.get 7=dst+4#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h14,h13,h5,h11]
    have hv13 : c3.get 13=finish := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h14,h13,h5,h11]
    rw [exec_branch,hv7,hv13,show E5R.taken .geu (dst+4#32) finish=false from by change (!E5R.taken .ltu (dst+4#32) finish)=false;rw [hlt];first | rfl | (rw [hp]; rfl)]
    simp only [ite_false];first | rfl | (rw [hp]; rfl)
  have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine QuietDet.step_of (by change (0x80005256#32).getLsbD 0 = false;decide) cp2147504726 fun o => ?_
    have hv : c4.get 16=16#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h14,h13,h5,h11]
    rw [exec_op,Core.get_zero,hv];first | rfl | (rw [hp]; rfl)
  have s5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000525a#32).getLsbD 0 = false;decide) cp2147504730 fun o => ?_
    have hv : c5.get 7=0xfffffff0#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h14,h13,h5,h11]
    rw [exec_opimm,hv];first | rfl | (rw [hp]; rfl)
  refine ⟨c6,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.single s5))))),rfl,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h14,h13,h5,h11]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h14,h13,h5,h11]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h14,h13,h5,h11]
  · intro r h7 h16 h6
    simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h14,h13,h5,h11,h7,h16,h6]

end E5R.Thermostat.CopyTwoAfter
