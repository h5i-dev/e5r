import Projects.thermostat.I16Code
import Projects.thermostat.SignedMagnitudeExtra
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.I16OneLeading
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (v : BitVec 16) (hn : v.toInt.natAbs < 10)
    (h10 : c.get 10 = SignedMagnitude.input v) (h11 : c.get 11 = BitVec.ofNat 32 v.toInt.natAbs)
    (hp : c.pc = 0x80004f90#32) :
    ∃ d, DetSteps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80004f4c#32 ∧
      d.get 14 = 5#32 ∧ d.get 12 = 0#32 ∧ d.get 15 = alu .sltu 0#32 (SignedMagnitude.input v) ∧ (∀ r : Reg, r ≠ 14 → r ≠ 12 → r ≠ 15 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 14 (5#32) 0x80004f92#32
  let c2 := c1.wr 12 ((BitVec.ofNat 32 v.toInt.natAbs) <<< 16) 0x80004f96#32
  let c3 := c2.wr 12 (alu .sltu (alu .sll (BitVec.ofNat 32 v.toInt.natAbs) 16#32) 1#32) 0x80004f9a#32
  let c4 := c3.wr 15 (alu .sltu 0#32 (SignedMagnitude.input v)) 0x80004f9e#32
  let c5 := c4.wr 12 (0#32) 0x80004fa0#32
  let c6 := c5.goto 0x80004f4c#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact di2147504016) fun o => ?_
    rw [exec_opimm,Core.get_zero,hp];first | rfl | (rw [hp]; rfl)
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x80004f92#32).getLsbD 0 = false;decide) di2147504018 fun o => ?_
    have hv : c1.get 11 = BitVec.ofNat 32 v.toInt.natAbs := by simp [c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_opimm,hv];first | rfl | (rw [hp]; rfl)
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x80004f96#32).getLsbD 0 = false;decide) di2147504022 fun o => ?_
    have hv : c2.get 12 = (BitVec.ofNat 32 v.toInt.natAbs) <<< 16 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_opimm,hv];first | rfl | (rw [hp]; rfl)
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine detStep_of (by change (0x80004f9a#32).getLsbD 0 = false;decide) di2147504026 fun o => ?_
    have hv : c3.get 10 = SignedMagnitude.input v := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_op,Core.get_zero,hv];first | rfl | (rw [hp]; rfl)
  have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine detStep_of (by change (0x80004f9e#32).getLsbD 0 = false;decide) di2147504030 fun o => ?_
    have hv0 : c4.get 12 = alu .sltu (alu .sll (BitVec.ofNat 32 v.toInt.natAbs) 16#32) 1#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    have hv1 : c4.get 15 = alu .sltu 0#32 (SignedMagnitude.input v) := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_op,hv0,hv1]
    change interp B img o (.done (c4.wr 12 (alu .and (alu .sltu (alu .sll (BitVec.ofNat 32 v.toInt.natAbs) 16#32) 1#32) (alu .sltu 0#32 (SignedMagnitude.input v))) 0x80004fa0#32)) ram 0 [] = _
    rw [SignedMagnitude.one_digit_leading v hn];first | rfl | (rw [hp]; rfl)
  have s5 : DetStep B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine detStep_of (by change (0x80004fa0#32).getLsbD 0 = false;decide) di2147504032 fun o => ?_
    have hv : c5.get 12 = 0#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_branch,hv,Core.get_zero,show taken .eq 0#32 (0 : Word) = true by decide]
    simp only [ite_true]
    change interp B img o (jump c5 (0x80004fa0#32+0xffffffac#32)) ram 0 [] = _
    rw [show 0x80004fa0#32+0xffffffac#32 = 0x80004f4c#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp]; rfl)
  refine ⟨c6,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.single s5))))),rfl,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
  · intro r h14 h12 h15
    simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h14,h12,h15]
end E5R.Thermostat.I16OneLeading
