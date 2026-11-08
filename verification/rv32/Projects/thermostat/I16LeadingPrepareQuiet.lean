-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.I16LeadingPrepare
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.I16LeadingPrepare
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (n k : Nat) (hn : n < 10) (hk : 1 ≤ k) (hkb : k ≤ 5)
    (hs : c.get 2 = sp) (h11 : c.get 11 = BitVec.ofNat 32 n) (h14 : c.get 14 = BitVec.ofNat 32 k)
    (hb : ReadBytes.Byte B img ram ((0x80005e10#32+BitVec.ofNat 32 (2*n))+1#32) (DecimalDigits.digit n))
    (hp : c.pc = 0x80004f4c#32) :
    ∃ d, Quiet.Steps B img 9 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80004f66#32 ∧
      d.get 11 = BitVec.ofNat 32 (48+n) ∧ d.get 12 = (sp+3#32)+BitVec.ofNat 32 (k-1) ∧ d.get 14 = BitVec.ofNat 32 (k-1) ∧ (∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 14 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 11 ((BitVec.ofNat 32 n) <<< 17) 0x80004f4e#32
  let c2 := c1.wr 11 (BitVec.ofNat 32 (2*n)) 0x80004f50#32
  let c3 := c2.wr 12 (0x80006000#32) 0x80004f54#32
  let c4 := c3.wr 12 (0x80005e10#32) 0x80004f58#32
  let c5 := c4.wr 11 (0x80005e10#32+BitVec.ofNat 32 (2*n)) 0x80004f5a#32
  let c6 := c5.wr 11 (BitVec.ofNat 32 (48+n)) 0x80004f5e#32
  let c7 := c6.wr 14 (BitVec.ofNat 32 (k-1)) 0x80004f60#32
  let c8 := c7.wr 12 (sp+3#32) 0x80004f64#32
  let c9 := c8.wr 12 ((sp+3#32)+BitVec.ofNat 32 (k-1)) 0x80004f66#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact di2147503948) fun o => ?_
    rw [exec_opimm,h11,hp];first | rfl | (rw [hp]; rfl)
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004f4e#32).getLsbD 0 = false;decide) di2147503950 fun o => ?_
    have hv : c1.get 11 = (BitVec.ofNat 32 n) <<< 17 := by simp [c1,Core.wr_get_ne,Core.wr_get,hs,h11,h14]
    rw [exec_opimm,hv]
    change interp B img o (.done (c1.wr 11 (((BitVec.ofNat 32 n) <<< 17) >>> 16) 0x80004f50#32)) ram 0 [] = _
    rw [DigitSmallMath.pairOffset n (by omega)];first | rfl | (rw [hp]; rfl)
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004f50#32).getLsbD 0 = false;decide) di2147503952 fun o => ?_
    rw [exec_lui];first | rfl | (rw [hp]; rfl)
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004f54#32).getLsbD 0 = false;decide) di2147503956 fun o => ?_
    have hv : c3.get 12 = 0x80006000#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h11,h14]
    rw [exec_opimm,hv]
    change interp B img o (.done (c3.wr 12 (0x80006000#32+0xfffffe10#32) 0x80004f58#32)) ram 0 [] = _
    rw [show 0x80006000#32+0xfffffe10#32 = 0x80005e10#32 by decide +kernel];first | rfl | (rw [hp]; rfl)
  have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004f58#32).getLsbD 0 = false;decide) di2147503960 fun o => ?_
    have hv0 : c4.get 11 = BitVec.ofNat 32 (2*n) := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h11,h14]
    have hv1 : c4.get 12 = 0x80005e10#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h11,h14]
    rw [exec_op,hv0,hv1]
    change interp B img o (.done (c4.wr 11 ((BitVec.ofNat 32 (2*n))+0x80005e10#32) 0x80004f5a#32)) ram 0 [] = _
    rw [BitVec.add_comm (BitVec.ofNat 32 (2*n)) 0x80005e10#32];first | rfl | (rw [hp]; rfl)
  have s5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004f5a#32).getLsbD 0 = false;decide) di2147503962 fun o => ?_
    have hv : c5.get 11 = 0x80005e10#32+BitVec.ofNat 32 (2*n) := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h11,h14]
    rw [exec_load,hv,ReadBytes.load hb,ReadBytes.extend_byte,←Memory.ofNat_width,DigitSmallMath.digit_nat n hn];first | rfl | (rw [hp]; rfl)
  have s6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004f5e#32).getLsbD 0 = false;decide) di2147503966 fun o => ?_
    have hv : c6.get 14 = BitVec.ofNat 32 k := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h11,h14]
    rw [exec_opimm,hv]
    change interp B img o (.done (c6.wr 14 ((BitVec.ofNat 32 k)+0xffffffff#32) 0x80004f60#32)) ram 0 [] = _
    rw [DigitSmallMath.previous k hk hkb];first | rfl | (rw [hp]; rfl)
  have s7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004f60#32).getLsbD 0 = false;decide) di2147503968 fun o => ?_
    have hv : c7.get 2 = sp := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h11,h14]
    rw [exec_opimm,hv];first | rfl | (rw [hp]; rfl)
  have s8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004f64#32).getLsbD 0 = false;decide) di2147503972 fun o => ?_
    have hv0 : c8.get 12 = sp+3#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h11,h14]
    have hv1 : c8.get 14 = BitVec.ofNat 32 (k-1) := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h11,h14]
    rw [exec_op,hv0,hv1];first | rfl | (rw [hp]; rfl)
  refine ⟨c9,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.single s8)))))))),rfl,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h11,h14]
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h11,h14]
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h11,h14]
  · intro r h11 h12 h14
    simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h11,h14,h11,h12,h14]

end E5R.Thermostat.I16LeadingPrepare
