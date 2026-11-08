import Projects.thermostat.I16Code
import Projects.thermostat.DigitSmallMath
import Projects.thermostat.ParamTurn
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.I16LargeQuotient
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (n : Nat) (hn : n ≤ 32768)
    (h12 : c.get 12 = (BitVec.ofNat 32 n) <<< 16) (h11 : c.get 11 = BitVec.ofNat 32 n)
    (hp : c.pc = 0x80004e8e#32) :
    ∃ d, DetSteps B img 8 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80004ea6#32 ∧
      d.get 12 = BitVec.ofNat 32 (n/10000) ∧ d.get 14 = (BitVec.ofNat 32 (n/10000))*10000#32 ∧ d.get 11 = BitVec.ofNat 32 (n%10000) ∧ (∀ r : Reg, r ≠ 12 → r ≠ 14 → r ≠ 11 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 12 (BitVec.ofNat 32 (n/16)) 0x80004e90#32
  let c2 := c1.wr 14 (839#32) 0x80004e94#32
  let c3 := c2.wr 12 ((BitVec.ofNat 32 (n/16))*839#32) 0x80004e98#32
  let c4 := c3.wr 14 (8192#32) 0x80004e9a#32
  let c5 := c4.wr 14 (10000#32) 0x80004e9e#32
  let c6 := c5.wr 12 (BitVec.ofNat 32 (n/10000)) 0x80004ea0#32
  let c7 := c6.wr 14 ((BitVec.ofNat 32 (n/10000))*10000#32) 0x80004ea4#32
  let c8 := c7.wr 11 (BitVec.ofNat 32 (n%10000)) 0x80004ea6#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact di2147503758) fun o => ?_
    rw [exec_opimm,h12,hp]
    change interp B img o (.done (c.wr 12 (((BitVec.ofNat 32 n) <<< 16) >>> 20) 0x80004e90#32)) ram 0 [] = _
    rw [DigitWordMath.shifted16 n (by omega)];first | rfl | (rw [hp]; rfl)
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x80004e90#32).getLsbD 0 = false;decide) di2147503760 fun o => ?_
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp]; rfl)
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x80004e94#32).getLsbD 0 = false;decide) di2147503764 fun o => ?_
    have hv0 : c2.get 12 = BitVec.ofNat 32 (n/16) := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h12,h11]
    have hv1 : c2.get 14 = 839#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h12,h11]
    rw [ParamTurn.exec_muldiv,hv0,hv1];first | rfl | (rw [hp]; rfl)
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine detStep_of (by change (0x80004e98#32).getLsbD 0 = false;decide) di2147503768 fun o => ?_
    rw [exec_lui];first | rfl | (rw [hp]; rfl)
  have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine detStep_of (by change (0x80004e9a#32).getLsbD 0 = false;decide) di2147503770 fun o => ?_
    have hv : c4.get 14 = 8192#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h11]
    rw [exec_opimm,hv];first | rfl | (rw [hp]; rfl)
  have s5 : DetStep B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine detStep_of (by change (0x80004e9e#32).getLsbD 0 = false;decide) di2147503774 fun o => ?_
    have hv : c5.get 12 = (BitVec.ofNat 32 (n/16))*839#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h11]
    rw [exec_opimm,hv]
    change interp B img o (.done (c5.wr 12 (((BitVec.ofNat 32 (n/16))*839#32) >>> 19) 0x80004ea0#32)) ram 0 [] = _
    rw [DigitSmallMath.reciprocal10000 n hn];first | rfl | (rw [hp]; rfl)
  have s6 : DetStep B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine detStep_of (by change (0x80004ea0#32).getLsbD 0 = false;decide) di2147503776 fun o => ?_
    have hv0 : c6.get 12 = BitVec.ofNat 32 (n/10000) := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h11]
    have hv1 : c6.get 14 = 10000#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h11]
    rw [ParamTurn.exec_muldiv,hv0,hv1];first | rfl | (rw [hp]; rfl)
  have s7 : DetStep B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine detStep_of (by change (0x80004ea4#32).getLsbD 0 = false;decide) di2147503780 fun o => ?_
    have hv0 : c7.get 11 = BitVec.ofNat 32 n := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h11]
    have hv1 : c7.get 14 = (BitVec.ofNat 32 (n/10000))*10000#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h11]
    rw [exec_op,hv0,hv1]
    change interp B img o (.done (c7.wr 11 ((BitVec.ofNat 32 n)-((BitVec.ofNat 32 (n/10000))*10000#32)) 0x80004ea6#32)) ram 0 [] = _
    rw [DigitSmallMath.remainder10000 n hn];first | rfl | (rw [hp]; rfl)
  refine ⟨c8,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.single s7))))))),rfl,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h11]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h11]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h11]
  · intro r h12 h14 h11
    simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h11,h12,h14,h11]
end E5R.Thermostat.I16LargeQuotient
