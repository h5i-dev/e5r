import Projects.thermostat.I16Code
import Projects.thermostat.DigitSmallMath
import Projects.thermostat.ParamTurn
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.I16LargeRemainder
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (n : Nat) (hn : n < 10000) (h11 : c.get 11 = BitVec.ofNat 32 n)
    (hp : c.pc = 0x80004ea6#32) :
    ∃ d, DetSteps B img 17 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80004eda#32 ∧
      d.get 14 = 0x80005e10#32+BitVec.ofNat 32 (2*(n/100)) ∧ d.get 15 = (BitVec.ofNat 32 (n/100))*100#32 ∧ d.get 16 = 0x80005e10#32 ∧ d.get 11 = 0x80005e10#32+BitVec.ofNat 32 (2*(n%100)) ∧ (∀ r : Reg, r ≠ 14 → r ≠ 15 → r ≠ 16 → r ≠ 11 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 14 (4096#32) 0x80004ea8#32
  let c2 := c1.wr 15 ((BitVec.ofNat 32 n) <<< 16) 0x80004eac#32
  let c3 := c2.wr 14 (5243#32) 0x80004eb0#32
  let c4 := c3.wr 15 (BitVec.ofNat 32 (n/4)) 0x80004eb2#32
  let c5 := c4.wr 14 ((BitVec.ofNat 32 (n/4))*5243#32) 0x80004eb6#32
  let c6 := c5.wr 15 (100#32) 0x80004eba#32
  let c7 := c6.wr 16 (BitVec.ofNat 32 (n/100)) 0x80004ebe#32
  let c8 := c7.wr 15 ((BitVec.ofNat 32 (n/100))*100#32) 0x80004ec2#32
  let c9 := c8.wr 16 (0x80006000#32) 0x80004ec6#32
  let c10 := c9.wr 16 (0x80005e10#32) 0x80004eca#32
  let c11 := c10.wr 11 (BitVec.ofNat 32 (n%100)) 0x80004ecc#32
  let c12 := c11.wr 14 (((BitVec.ofNat 32 (n/4))*5243#32) >>> 16) 0x80004ece#32
  let c13 := c12.wr 11 ((BitVec.ofNat 32 (n%100)) <<< 17) 0x80004ed0#32
  let c14 := c13.wr 14 (BitVec.ofNat 32 (2*(n/100))) 0x80004ed4#32
  let c15 := c14.wr 11 (BitVec.ofNat 32 (2*(n%100))) 0x80004ed6#32
  let c16 := c15.wr 14 (0x80005e10#32+BitVec.ofNat 32 (2*(n/100))) 0x80004ed8#32
  let c17 := c16.wr 11 (0x80005e10#32+BitVec.ofNat 32 (2*(n%100))) 0x80004eda#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact di2147503782) fun o => ?_
    rw [exec_lui,hp];first | rfl | (rw [hp]; rfl)
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x80004ea8#32).getLsbD 0 = false;decide) di2147503784 fun o => ?_
    have hv : c1.get 11 = BitVec.ofNat 32 n := by simp [c1,Core.wr_get_ne,Core.wr_get,h11]
    rw [exec_opimm,hv];first | rfl | (rw [hp]; rfl)
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x80004eac#32).getLsbD 0 = false;decide) di2147503788 fun o => ?_
    have hv : c2.get 14 = 4096#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h11]
    rw [exec_opimm,hv];first | rfl | (rw [hp]; rfl)
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine detStep_of (by change (0x80004eb0#32).getLsbD 0 = false;decide) di2147503792 fun o => ?_
    have hv : c3.get 15 = (BitVec.ofNat 32 n) <<< 16 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11]
    rw [exec_opimm,hv]
    change interp B img o (.done (c3.wr 15 (((BitVec.ofNat 32 n) <<< 16) >>> 18) 0x80004eb2#32)) ram 0 [] = _
    rw [DigitWordMath.shifted4 n (by omega)];first | rfl | (rw [hp]; rfl)
  have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine detStep_of (by change (0x80004eb2#32).getLsbD 0 = false;decide) di2147503794 fun o => ?_
    have hv0 : c4.get 15 = BitVec.ofNat 32 (n/4) := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11]
    have hv1 : c4.get 14 = 5243#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11]
    rw [ParamTurn.exec_muldiv,hv0,hv1];first | rfl | (rw [hp]; rfl)
  have s5 : DetStep B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine detStep_of (by change (0x80004eb6#32).getLsbD 0 = false;decide) di2147503798 fun o => ?_
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp]; rfl)
  have s6 : DetStep B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine detStep_of (by change (0x80004eba#32).getLsbD 0 = false;decide) di2147503802 fun o => ?_
    have hv : c6.get 14 = (BitVec.ofNat 32 (n/4))*5243#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11]
    rw [exec_opimm,hv]
    change interp B img o (.done (c6.wr 16 (((BitVec.ofNat 32 (n/4))*5243#32) >>> 17) 0x80004ebe#32)) ram 0 [] = _
    rw [DigitSmallMath.reciprocal100 n hn];first | rfl | (rw [hp]; rfl)
  have s7 : DetStep B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine detStep_of (by change (0x80004ebe#32).getLsbD 0 = false;decide) di2147503806 fun o => ?_
    have hv0 : c7.get 16 = BitVec.ofNat 32 (n/100) := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11]
    have hv1 : c7.get 15 = 100#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11]
    rw [ParamTurn.exec_muldiv,hv0,hv1];first | rfl | (rw [hp]; rfl)
  have s8 : DetStep B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine detStep_of (by change (0x80004ec2#32).getLsbD 0 = false;decide) di2147503810 fun o => ?_
    rw [exec_lui];first | rfl | (rw [hp]; rfl)
  have s9 : DetStep B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine detStep_of (by change (0x80004ec6#32).getLsbD 0 = false;decide) di2147503814 fun o => ?_
    have hv : c9.get 16 = 0x80006000#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11]
    rw [exec_opimm,hv]
    change interp B img o (.done (c9.wr 16 (0x80006000#32+0xfffffe10#32) 0x80004eca#32)) ram 0 [] = _
    rw [show 0x80006000#32+0xfffffe10#32 = 0x80005e10#32 by decide +kernel];first | rfl | (rw [hp]; rfl)
  have s10 : DetStep B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine detStep_of (by change (0x80004eca#32).getLsbD 0 = false;decide) di2147503818 fun o => ?_
    have hv0 : c10.get 11 = BitVec.ofNat 32 n := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11]
    have hv1 : c10.get 15 = (BitVec.ofNat 32 (n/100))*100#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11]
    rw [exec_op,hv0,hv1]
    change interp B img o (.done (c10.wr 11 ((BitVec.ofNat 32 n)-((BitVec.ofNat 32 (n/100))*100#32)) 0x80004ecc#32)) ram 0 [] = _
    rw [DigitSmallMath.remainder100 n hn];first | rfl | (rw [hp]; rfl)
  have s11 : DetStep B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine detStep_of (by change (0x80004ecc#32).getLsbD 0 = false;decide) di2147503820 fun o => ?_
    have hv : c11.get 14 = (BitVec.ofNat 32 (n/4))*5243#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11]
    rw [exec_opimm,hv];first | rfl | (rw [hp]; rfl)
  have s12 : DetStep B img ⟨c12,ram⟩ ⟨c13,ram⟩ := by
    refine detStep_of (by change (0x80004ece#32).getLsbD 0 = false;decide) di2147503822 fun o => ?_
    have hv : c12.get 11 = BitVec.ofNat 32 (n%100) := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11]
    rw [exec_opimm,hv];first | rfl | (rw [hp]; rfl)
  have s13 : DetStep B img ⟨c13,ram⟩ ⟨c14,ram⟩ := by
    refine detStep_of (by change (0x80004ed0#32).getLsbD 0 = false;decide) di2147503824 fun o => ?_
    have hv : c13.get 14 = ((BitVec.ofNat 32 (n/4))*5243#32) >>> 16 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11]
    rw [exec_opimm,hv]
    change interp B img o (.done (c13.wr 14 ((((BitVec.ofNat 32 (n/4))*5243#32) >>> 16) &&& 2046#32) 0x80004ed4#32)) ram 0 [] = _
    rw [DigitSmallMath.pairIndexRaw n hn];first | rfl | (rw [hp]; rfl)
  have s14 : DetStep B img ⟨c14,ram⟩ ⟨c15,ram⟩ := by
    refine detStep_of (by change (0x80004ed4#32).getLsbD 0 = false;decide) di2147503828 fun o => ?_
    have hv : c14.get 11 = (BitVec.ofNat 32 (n%100)) <<< 17 := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11]
    rw [exec_opimm,hv]
    change interp B img o (.done (c14.wr 11 (((BitVec.ofNat 32 (n%100)) <<< 17) >>> 16) 0x80004ed6#32)) ram 0 [] = _
    rw [DigitSmallMath.pairOffset (n%100) (by omega)];first | rfl | (rw [hp]; rfl)
  have s15 : DetStep B img ⟨c15,ram⟩ ⟨c16,ram⟩ := by
    refine detStep_of (by change (0x80004ed6#32).getLsbD 0 = false;decide) di2147503830 fun o => ?_
    have hv0 : c15.get 14 = BitVec.ofNat 32 (2*(n/100)) := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11]
    have hv1 : c15.get 16 = 0x80005e10#32 := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11]
    rw [exec_op,hv0,hv1]
    change interp B img o (.done (c15.wr 14 ((BitVec.ofNat 32 (2*(n/100)))+0x80005e10#32) 0x80004ed8#32)) ram 0 [] = _
    rw [BitVec.add_comm (BitVec.ofNat 32 (2*(n/100))) 0x80005e10#32];first | rfl | (rw [hp]; rfl)
  have s16 : DetStep B img ⟨c16,ram⟩ ⟨c17,ram⟩ := by
    refine detStep_of (by change (0x80004ed8#32).getLsbD 0 = false;decide) di2147503832 fun o => ?_
    have hv0 : c16.get 11 = BitVec.ofNat 32 (2*(n%100)) := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11]
    have hv1 : c16.get 16 = 0x80005e10#32 := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11]
    rw [exec_op,hv0,hv1]
    change interp B img o (.done (c16.wr 11 ((BitVec.ofNat 32 (2*(n%100)))+0x80005e10#32) 0x80004eda#32)) ram 0 [] = _
    rw [BitVec.add_comm (BitVec.ofNat 32 (2*(n%100))) 0x80005e10#32];first | rfl | (rw [hp]; rfl)
  refine ⟨c17,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.step s8 (.step s9 (.step s10 (.step s11 (.step s12 (.step s13 (.step s14 (.step s15 (.single s16)))))))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11]
  · simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11]
  · simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11]
  · simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11]
  · intro r h14 h15 h16 h11
    simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h14,h15,h16,h11]
end E5R.Thermostat.I16LargeRemainder
