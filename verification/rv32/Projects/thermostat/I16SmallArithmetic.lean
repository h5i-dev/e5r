import Projects.thermostat.I16Code
import Projects.thermostat.DigitSmallMath
import Projects.thermostat.ParamTurn
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.I16SmallArithmetic
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (n : Nat) (hn : n < 10000)
    (h12 : c.get 12 = (BitVec.ofNat 32 n) <<< 16) (h11 : c.get 11 = BitVec.ofNat 32 n)
    (hp : c.pc = 0x80004f04#32) :
    ∃ d, DetSteps B img 13 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80004f2a#32 ∧
      d.get 14 = 0x80005e10#32 ∧ d.get 12 = BitVec.ofNat 32 (n/100) ∧ d.get 11 = 0x80005e10#32+BitVec.ofNat 32 (2*(n%100)) ∧ (∀ r : Reg, r ≠ 14 → r ≠ 12 → r ≠ 11 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 14 (4096#32) 0x80004f06#32
  let c2 := c1.wr 12 (BitVec.ofNat 32 (n/4)) 0x80004f08#32
  let c3 := c2.wr 14 (5243#32) 0x80004f0c#32
  let c4 := c3.wr 12 ((BitVec.ofNat 32 (n/4))*5243#32) 0x80004f10#32
  let c5 := c4.wr 14 (100#32) 0x80004f14#32
  let c6 := c5.wr 12 (BitVec.ofNat 32 (n/100)) 0x80004f16#32
  let c7 := c6.wr 14 ((BitVec.ofNat 32 (n/100))*100#32) 0x80004f1a#32
  let c8 := c7.wr 11 (BitVec.ofNat 32 (n%100)) 0x80004f1c#32
  let c9 := c8.wr 11 ((BitVec.ofNat 32 (n%100)) <<< 17) 0x80004f1e#32
  let c10 := c9.wr 14 (0x80006000#32) 0x80004f22#32
  let c11 := c10.wr 14 (0x80005e10#32) 0x80004f26#32
  let c12 := c11.wr 11 (BitVec.ofNat 32 (2*(n%100))) 0x80004f28#32
  let c13 := c12.wr 11 (0x80005e10#32+BitVec.ofNat 32 (2*(n%100))) 0x80004f2a#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact di2147503876) fun o => ?_
    rw [exec_lui,hp];first | rfl | (rw [hp]; rfl)
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x80004f06#32).getLsbD 0 = false;decide) di2147503878 fun o => ?_
    have hv : c1.get 12 = (BitVec.ofNat 32 n) <<< 16 := by simp [c1,Core.wr_get_ne,Core.wr_get,h12,h11]
    rw [exec_opimm,hv]
    change interp B img o (.done (c1.wr 12 (((BitVec.ofNat 32 n) <<< 16) >>> 18) 0x80004f08#32)) ram 0 [] = _
    rw [DigitWordMath.shifted4 n (by omega)];first | rfl | (rw [hp]; rfl)
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x80004f08#32).getLsbD 0 = false;decide) di2147503880 fun o => ?_
    have hv : c2.get 14 = 4096#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h12,h11]
    rw [exec_opimm,hv];first | rfl | (rw [hp]; rfl)
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine detStep_of (by change (0x80004f0c#32).getLsbD 0 = false;decide) di2147503884 fun o => ?_
    have hv0 : c3.get 12 = BitVec.ofNat 32 (n/4) := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h11]
    have hv1 : c3.get 14 = 5243#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h11]
    rw [ParamTurn.exec_muldiv,hv0,hv1];first | rfl | (rw [hp]; rfl)
  have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine detStep_of (by change (0x80004f10#32).getLsbD 0 = false;decide) di2147503888 fun o => ?_
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp]; rfl)
  have s5 : DetStep B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine detStep_of (by change (0x80004f14#32).getLsbD 0 = false;decide) di2147503892 fun o => ?_
    have hv : c5.get 12 = (BitVec.ofNat 32 (n/4))*5243#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h11]
    rw [exec_opimm,hv]
    change interp B img o (.done (c5.wr 12 (((BitVec.ofNat 32 (n/4))*5243#32) >>> 17) 0x80004f16#32)) ram 0 [] = _
    rw [DigitSmallMath.reciprocal100 n hn];first | rfl | (rw [hp]; rfl)
  have s6 : DetStep B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine detStep_of (by change (0x80004f16#32).getLsbD 0 = false;decide) di2147503894 fun o => ?_
    have hv0 : c6.get 12 = BitVec.ofNat 32 (n/100) := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h11]
    have hv1 : c6.get 14 = 100#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h11]
    rw [ParamTurn.exec_muldiv,hv0,hv1];first | rfl | (rw [hp]; rfl)
  have s7 : DetStep B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine detStep_of (by change (0x80004f1a#32).getLsbD 0 = false;decide) di2147503898 fun o => ?_
    have hv0 : c7.get 11 = BitVec.ofNat 32 n := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h11]
    have hv1 : c7.get 14 = (BitVec.ofNat 32 (n/100))*100#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h11]
    rw [exec_op,hv0,hv1]
    change interp B img o (.done (c7.wr 11 ((BitVec.ofNat 32 n)-((BitVec.ofNat 32 (n/100))*100#32)) 0x80004f1c#32)) ram 0 [] = _
    rw [DigitSmallMath.remainder100 n hn];first | rfl | (rw [hp]; rfl)
  have s8 : DetStep B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine detStep_of (by change (0x80004f1c#32).getLsbD 0 = false;decide) di2147503900 fun o => ?_
    have hv : c8.get 11 = BitVec.ofNat 32 (n%100) := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h11]
    rw [exec_opimm,hv];first | rfl | (rw [hp]; rfl)
  have s9 : DetStep B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine detStep_of (by change (0x80004f1e#32).getLsbD 0 = false;decide) di2147503902 fun o => ?_
    rw [exec_lui];first | rfl | (rw [hp]; rfl)
  have s10 : DetStep B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine detStep_of (by change (0x80004f22#32).getLsbD 0 = false;decide) di2147503906 fun o => ?_
    have hv : c10.get 14 = 0x80006000#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h11]
    rw [exec_opimm,hv]
    change interp B img o (.done (c10.wr 14 (0x80006000#32+0xfffffe10#32) 0x80004f26#32)) ram 0 [] = _
    rw [show 0x80006000#32+0xfffffe10#32 = 0x80005e10#32 by decide +kernel];first | rfl | (rw [hp]; rfl)
  have s11 : DetStep B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine detStep_of (by change (0x80004f26#32).getLsbD 0 = false;decide) di2147503910 fun o => ?_
    have hv : c11.get 11 = (BitVec.ofNat 32 (n%100)) <<< 17 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h11]
    rw [exec_opimm,hv]
    change interp B img o (.done (c11.wr 11 (((BitVec.ofNat 32 (n%100)) <<< 17) >>> 16) 0x80004f28#32)) ram 0 [] = _
    rw [DigitSmallMath.pairOffset (n%100) (by omega)];first | rfl | (rw [hp]; rfl)
  have s12 : DetStep B img ⟨c12,ram⟩ ⟨c13,ram⟩ := by
    refine detStep_of (by change (0x80004f28#32).getLsbD 0 = false;decide) di2147503912 fun o => ?_
    have hv0 : c12.get 11 = BitVec.ofNat 32 (2*(n%100)) := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h11]
    have hv1 : c12.get 14 = 0x80005e10#32 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h11]
    rw [exec_op,hv0,hv1]
    change interp B img o (.done (c12.wr 11 ((BitVec.ofNat 32 (2*(n%100)))+0x80005e10#32) 0x80004f2a#32)) ram 0 [] = _
    rw [BitVec.add_comm (BitVec.ofNat 32 (2*(n%100))) 0x80005e10#32];first | rfl | (rw [hp]; rfl)
  refine ⟨c13,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.step s8 (.step s9 (.step s10 (.step s11 (.single s12)))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h11]
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h11]
  · simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h11]
  · intro r h14 h12 h11
    simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h11,h14,h12,h11]
end E5R.Thermostat.I16SmallArithmetic
