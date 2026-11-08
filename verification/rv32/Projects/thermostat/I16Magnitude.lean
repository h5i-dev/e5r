import Projects.thermostat.I16Code
import Projects.thermostat.SignedMagnitudeExtra
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.I16Magnitude
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp ptr fmt : Word) (v : BitVec 16)
    (hs : c.get 2 = sp) (h10 : c.get 10 = ptr) (h11 : c.get 11 = fmt)
    (hm : Memory.Block B ptr 2) (ha : ptr.toNat%2 = 0)
    (hv : extend .h true (ramRead ram ptr .h) = SignedMagnitude.input v)
    (hp : c.pc = 0x80004e64#32) :
    ∃ d, DetSteps B img 11 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80004e8a#32 ∧
      d.get 8 = sp+16#32 ∧ d.get 13 = fmt ∧ d.get 10 = SignedMagnitude.input v ∧ d.get 15 = SignedMagnitude.input v <<< 16 ∧ d.get 11 = BitVec.ofNat 32 v.toInt.natAbs ∧ d.get 12 = (BitVec.ofNat 32 v.toInt.natAbs) <<< 16 ∧ d.get 14 = BitVec.ofNat 32 v.toInt.natAbs ∧ d.get 16 = 1000#32 ∧ (∀ r : Reg, r ≠ 8 → r ≠ 13 → r ≠ 10 → r ≠ 15 → r ≠ 11 → r ≠ 12 → r ≠ 14 → r ≠ 16 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 8 (sp+16#32) 0x80004e66#32
  let c2 := c1.wr 13 (fmt) 0x80004e68#32
  let c3 := c2.wr 10 (SignedMagnitude.input v) 0x80004e6c#32
  let c4 := c3.wr 15 (SignedMagnitude.input v <<< 16) 0x80004e70#32
  let c5 := c4.wr 11 (SignedMagnitude.sign v) 0x80004e74#32
  let c6 := c5.wr 10 ((SignedMagnitude.input v) ^^^ SignedMagnitude.sign v) 0x80004e76#32
  let c7 := c6.wr 11 (BitVec.ofNat 32 v.toInt.natAbs) 0x80004e7a#32
  let c8 := c7.wr 12 ((BitVec.ofNat 32 v.toInt.natAbs) <<< 16) 0x80004e7e#32
  let c9 := c8.wr 14 (BitVec.ofNat 32 v.toInt.natAbs) 0x80004e82#32
  let c10 := c9.wr 16 (1000#32) 0x80004e86#32
  let c11 := c10.wr 10 (SignedMagnitude.input v) 0x80004e8a#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact di2147503716) fun o => ?_
    rw [exec_opimm,hs,hp];first | rfl | (rw [hp]; rfl)
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x80004e66#32).getLsbD 0 = false;decide) di2147503718 fun o => ?_
    have hv : c1.get 11 = fmt := by simp [c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x80004e68#32).getLsbD 0 = false;decide) di2147503720 fun o => ?_
    have hp0 : c2.get 10 = ptr := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11]
    rw [exec_load,hp0,BitVec.add_zero,interp_load_ram (B := B) (img := img) (w := .h) o ha
      (by simpa only [BitVec.add_zero] using Memory.block_access hm (off := 0) (by decide) (by decide)),hv];first | rfl | (rw [hp]; rfl)
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine detStep_of (by change (0x80004e6c#32).getLsbD 0 = false;decide) di2147503724 fun o => ?_
    have hv0 : c3.get 10 = SignedMagnitude.input v := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11]
    rw [exec_opimm,hv0];first | rfl | (rw [hp]; rfl)
  have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine detStep_of (by change (0x80004e70#32).getLsbD 0 = false;decide) di2147503728 fun o => ?_
    have hv0 : c4.get 15 = SignedMagnitude.input v <<< 16 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11]
    rw [exec_opimm,hv0]
    change interp B img o (.done (c4.wr 11 (((SignedMagnitude.input v) <<< 16).sshiftRight 31) 0x80004e74#32)) ram 0 [] = _
    rw [SignedMagnitude.sign_mask];first | rfl | (rw [hp]; rfl)
  have s5 : DetStep B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine detStep_of (by change (0x80004e74#32).getLsbD 0 = false;decide) di2147503732 fun o => ?_
    have hv0 : c5.get 10 = SignedMagnitude.input v := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11]
    have hv1 : c5.get 11 = SignedMagnitude.sign v := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11]
    rw [exec_op,hv0,hv1];first | rfl | (rw [hp]; rfl)
  have s6 : DetStep B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine detStep_of (by change (0x80004e76#32).getLsbD 0 = false;decide) di2147503734 fun o => ?_
    have hv0 : c6.get 10 = (SignedMagnitude.input v) ^^^ SignedMagnitude.sign v := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11]
    have hv1 : c6.get 11 = SignedMagnitude.sign v := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11]
    rw [exec_op,hv0,hv1]
    change interp B img o (.done (c6.wr 11 (((SignedMagnitude.input v) ^^^ SignedMagnitude.sign v)-SignedMagnitude.sign v) 0x80004e7a#32)) ram 0 [] = _
    rw [SignedMagnitude.absolute];first | rfl | (rw [hp]; rfl)
  have s7 : DetStep B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine detStep_of (by change (0x80004e7a#32).getLsbD 0 = false;decide) di2147503738 fun o => ?_
    have hv0 : c7.get 11 = BitVec.ofNat 32 v.toInt.natAbs := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11]
    rw [exec_opimm,hv0];first | rfl | (rw [hp]; rfl)
  have s8 : DetStep B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine detStep_of (by change (0x80004e7e#32).getLsbD 0 = false;decide) di2147503742 fun o => ?_
    have hv0 : c8.get 12 = (BitVec.ofNat 32 v.toInt.natAbs) <<< 16 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11]
    rw [exec_opimm,hv0]
    change interp B img o (.done (c8.wr 14 (((BitVec.ofNat 32 v.toInt.natAbs) <<< 16) >>> 16) 0x80004e82#32)) ram 0 [] = _
    rw [SignedMagnitude.normalized];first | rfl | (rw [hp]; rfl)
  have s9 : DetStep B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine detStep_of (by change (0x80004e82#32).getLsbD 0 = false;decide) di2147503746 fun o => ?_
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp]; rfl)
  have s10 : DetStep B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine detStep_of (by change (0x80004e86#32).getLsbD 0 = false;decide) di2147503750 fun o => ?_
    have hv0 : c10.get 15 = SignedMagnitude.input v <<< 16 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11]
    rw [exec_opimm,hv0]
    change interp B img o (.done (c10.wr 10 (((SignedMagnitude.input v) <<< 16).sshiftRight 16) 0x80004e8a#32)) ram 0 [] = _
    rw [SignedMagnitude.recover];first | rfl | (rw [hp]; rfl)
  refine ⟨c11,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.step s8 (.step s9 (.single s10)))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11]
  · intro r h8 h13 h10 h15 h11 h12 h14 h16
    simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h8,h13,h10,h15,h11,h12,h14,h16]
end E5R.Thermostat.I16Magnitude
