import Projects.thermostat.I16Code
import Projects.thermostat.SignedMagnitudeExtra
import Projects.thermostat.DigitSmallMath
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.I16LeadingPresent
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (v : BitVec 16) (n : Nat) (hn : 0 < n) (hb : n < 10) (hv : v.toInt.natAbs ≠ 0)
    (h10 : c.get 10 = SignedMagnitude.input v) (h12 : c.get 12 = BitVec.ofNat 32 n)
    (hp : c.pc = 0x80004f3c#32) :
    ∃ d, DetSteps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80004f4c#32 ∧
      d.get 11 = BitVec.ofNat 32 n ∧ d.get 12 = 0#32 ∧ d.get 15 = 1#32 ∧ (∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 15 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 11 (BitVec.ofNat 32 n) 0x80004f3e#32
  let c2 := c1.wr 12 ((BitVec.ofNat 32 n) <<< 16) 0x80004f40#32
  let c3 := c2.wr 12 (0#32) 0x80004f44#32
  let c4 := c3.wr 15 (1#32) 0x80004f48#32
  let c5 := c4.wr 12 (0#32) 0x80004f4a#32
  let c6 := c5.goto 0x80004f4c#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact di2147503932) fun o => ?_
    have hv : c.get 12 = BitVec.ofNat 32 n := by simp [Core.wr_get_ne,Core.wr_get,h10,h12]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x80004f3e#32).getLsbD 0 = false;decide) di2147503934 fun o => ?_
    have hv0 : c1.get 12 = BitVec.ofNat 32 n := by simp [c1,Core.wr_get_ne,Core.wr_get,h10,h12]
    rw [exec_opimm,hv0];first | rfl | (rw [hp]; rfl)
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x80004f40#32).getLsbD 0 = false;decide) di2147503936 fun o => ?_
    have hv0 : c2.get 12 = (BitVec.ofNat 32 n) <<< 16 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h10,h12]
    rw [exec_opimm,hv0]
    change interp B img o (.done (c2.wr 12 (alu .sltu (alu .sll (BitVec.ofNat 32 n) 16#32) 1#32) 0x80004f44#32)) ram 0 [] = _
    rw [DigitSmallMath.leading_nonzero n hn hb];first | rfl | (rw [hp]; rfl)
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine detStep_of (by change (0x80004f44#32).getLsbD 0 = false;decide) di2147503940 fun o => ?_
    have hv0 : c3.get 10 = SignedMagnitude.input v := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h12]
    rw [exec_op,Core.get_zero,hv0]
    change interp B img o (.done (c3.wr 15 (alu .sltu 0#32 (SignedMagnitude.input v)) 0x80004f48#32)) ram 0 [] = _
    rw [SignedMagnitude.nonzero_test v hv];first | rfl | (rw [hp]; rfl)
  have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine detStep_of (by change (0x80004f48#32).getLsbD 0 = false;decide) di2147503944 fun o => ?_
    have hv0 : c4.get 12 = 0#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h12]
    have hv1 : c4.get 15 = 1#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h12]
    rw [exec_op,hv0,hv1];first | rfl | (rw [hp]; rfl)
  have s5 : DetStep B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine detStep_of (by change (0x80004f4a#32).getLsbD 0 = false;decide) di2147503946 fun o => ?_
    have hv : c5.get 12 = 0#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h12]
    rw [exec_branch,hv,Core.get_zero,show E5R.taken .ne (0#32) (0 : Word) = false by decide]
    simp only [ite_true,ite_false]
    first | rfl | (rw [hp]; rfl)
  refine ⟨c6,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.single s5))))),rfl,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h12]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h12]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h12]
  · intro r h11 h12 h15
    simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h12,h11,h12,h15]
end E5R.Thermostat.I16LeadingPresent
