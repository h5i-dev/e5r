import Projects.thermostat.WritePrefixCode
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.PrefixSetup
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp writer vtable litPrefix prefixLen : Word)
    (hs : c.get 2 = sp) (h10 : c.get 10 = writer) (h11 : c.get 11 = vtable)
    (h13 : c.get 13 = litPrefix) (h14 : c.get 14 = prefixLen)
    (hp : c.pc = 0x80004e0e#32) :
    ∃ d, DetSteps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80004e1a#32 ∧
      d.get 8 = sp+32#32 ∧ d.get 9 = prefixLen ∧ d.get 18 = litPrefix ∧ d.get 19 = vtable ∧ d.get 11 = 0xffffffff#32 ∧ d.get 20 = writer ∧ (∀ r : Reg, r ≠ 8 → r ≠ 9 → r ≠ 18 → r ≠ 19 → r ≠ 11 → r ≠ 20 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 8 (sp+32#32) 0x80004e10#32
  let c2 := c1.wr 9 (prefixLen) 0x80004e12#32
  let c3 := c2.wr 18 (litPrefix) 0x80004e14#32
  let c4 := c3.wr 19 (vtable) 0x80004e16#32
  let c5 := c4.wr 11 (0xffffffff#32) 0x80004e18#32
  let c6 := c5.wr 20 (writer) 0x80004e1a#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact wp2147503630) fun o => ?_
    rw [exec_opimm,hs,hp];first | rfl | (rw [hp]; rfl)
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x80004e10#32).getLsbD 0 = false;decide) wp2147503632 fun o => ?_
    have hv : c1.get 14 = prefixLen := by simp [c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h13,h14]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x80004e12#32).getLsbD 0 = false;decide) wp2147503634 fun o => ?_
    have hv : c2.get 13 = litPrefix := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h13,h14]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine detStep_of (by change (0x80004e14#32).getLsbD 0 = false;decide) wp2147503636 fun o => ?_
    have hv : c3.get 11 = vtable := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h13,h14]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine detStep_of (by change (0x80004e16#32).getLsbD 0 = false;decide) wp2147503638 fun o => ?_
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp]; rfl)
  have s5 : DetStep B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine detStep_of (by change (0x80004e18#32).getLsbD 0 = false;decide) wp2147503640 fun o => ?_
    have hv : c5.get 10 = writer := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h13,h14]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  refine ⟨c6,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.single s5))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h13,h14]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h13,h14]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h13,h14]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h13,h14]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h13,h14]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h13,h14]
  · intro r h8 h9 h18 h19 h11 h20
    simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h13,h14,h8,h9,h18,h19,h11,h20]
end E5R.Thermostat.PrefixSetup
