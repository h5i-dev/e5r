-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.I16PadCall
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.I16PadCall
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (sp fmt : Word) (v : BitVec 16) (idx : Nat) (hi : idx ≤ 4)
    (hs : c.get 2 = sp) (h10 : c.get 10 = SignedMagnitude.input v)
    (h13 : c.get 13 = fmt) (h14 : c.get 14 = BitVec.ofNat 32 idx)
    (hp : c.pc = 0x80004f6a#32) :
    ∃ d, Quiet.Steps B img 11 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80004514#32 ∧
      d.get 10 = fmt ∧ d.get 15 = BitVec.ofNat 32 (5-idx) ∧ d.get 12 = 1#32 ∧ d.get 11 = SignedMagnitude.positive v ∧ d.get 14 = (sp+3#32)+BitVec.ofNat 32 idx ∧ d.get 13 = 0#32 ∧ d.get 1 = 0x80004f88#32 ∧ (∀ r : Reg, r ≠ 10 → r ≠ 15 → r ≠ 12 → r ≠ 11 → r ≠ 14 → r ≠ 13 → r ≠ 1 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (SignedMagnitude.negative v) 0x80004f6c#32
  let c2 := c1.wr 15 (5#32) 0x80004f6e#32
  let c3 := c2.wr 12 (sp+3#32) 0x80004f72#32
  let c4 := c3.wr 11 (SignedMagnitude.positive v) 0x80004f76#32
  let c5 := c4.wr 15 (BitVec.ofNat 32 (5-idx)) 0x80004f78#32
  let c6 := c5.wr 14 ((sp+3#32)+BitVec.ofNat 32 idx) 0x80004f7a#32
  let c7 := c6.wr 12 (1#32) 0x80004f7c#32
  let c8 := c7.wr 10 (fmt) 0x80004f7e#32
  let c9 := c8.wr 13 (0#32) 0x80004f80#32
  let c10 := c9.wr 1 (0x80003f80#32) 0x80004f84#32
  let c11 := c10.wr 1 (0x80004f88#32) 0x80004514#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact di2147503978) fun o => ?_
    rw [exec_opimm,h10,hp]
    change interp B img o (.done (c.wr 10 ((SignedMagnitude.input v) >>> 31) 0x80004f6c#32)) ram 0 [] = _
    rw [SignedMagnitude.sign_bit];first | rfl | (rw [hp]; rfl)
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004f6c#32).getLsbD 0 = false;decide) di2147503980 fun o => ?_
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp]; rfl)
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004f6e#32).getLsbD 0 = false;decide) di2147503982 fun o => ?_
    have hv : c2.get 2 = sp := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h13,h14]
    rw [exec_opimm,hv];first | rfl | (rw [hp]; rfl)
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004f72#32).getLsbD 0 = false;decide) di2147503986 fun o => ?_
    have hv : c3.get 10 = SignedMagnitude.negative v := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h13,h14]
    rw [exec_opimm,hv]
    change interp B img o (.done (c3.wr 11 ((SignedMagnitude.negative v) ^^^ 1#32) 0x80004f76#32)) ram 0 [] = _
    rw [SignedMagnitude.sign_flip];first | rfl | (rw [hp]; rfl)
  have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004f76#32).getLsbD 0 = false;decide) di2147503990 fun o => ?_
    have hv0 : c4.get 15 = 5#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h13,h14]
    have hv1 : c4.get 14 = BitVec.ofNat 32 idx := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h13,h14]
    rw [exec_op,hv0,hv1]
    change interp B img o (.done (c4.wr 15 ((BitVec.ofNat 32 5)-(BitVec.ofNat 32 idx)) 0x80004f78#32)) ram 0 [] = _
    rw [BitVec.ofNat_sub_ofNat_of_le 5 idx (by omega) (by omega)];first | rfl | (rw [hp]; rfl)
  have s5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004f78#32).getLsbD 0 = false;decide) di2147503992 fun o => ?_
    have hv0 : c5.get 14 = BitVec.ofNat 32 idx := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h13,h14]
    have hv1 : c5.get 12 = sp+3#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h13,h14]
    rw [exec_op,hv0,hv1]
    change interp B img o (.done (c5.wr 14 ((BitVec.ofNat 32 idx)+(sp+3#32)) 0x80004f7a#32)) ram 0 [] = _
    rw [BitVec.add_comm (BitVec.ofNat 32 idx) (sp+3#32)];first | rfl | (rw [hp]; rfl)
  have s6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004f7a#32).getLsbD 0 = false;decide) di2147503994 fun o => ?_
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp]; rfl)
  have s7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004f7c#32).getLsbD 0 = false;decide) di2147503996 fun o => ?_
    have hv : c7.get 13 = fmt := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h13,h14]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  have s8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004f7e#32).getLsbD 0 = false;decide) di2147503998 fun o => ?_
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp]; rfl)
  have s9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004f80#32).getLsbD 0 = false;decide) di2147504000 fun o => ?_
    rw [exec_auipc]
    change interp B img o (.done (c9.wr 1 (0x80004f80#32+0xfffff000#32) 0x80004f84#32)) ram 0 [] = _
    rw [show 0x80004f80#32+0xfffff000#32 = 0x80003f80#32 by decide +kernel];first | rfl | (rw [hp]; rfl)
  have s10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004f84#32).getLsbD 0 = false;decide) di2147504004 fun o => ?_
    have hv : c10.get 1 = 0x80003f80#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h13,h14]
    rw [exec_jalr,hv]
    change interp B img o (jump (c10.set 1 0x80004f88#32) ((0x80003f80#32+1428#32) &&& ~~~1)) ram 0 [] = _
    rw [show (0x80003f80#32+1428#32) &&& ~~~1 = 0x80004514#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp]; rfl)
  refine ⟨c11,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.step s8 (.step s9 (.single s10)))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h13,h14]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h13,h14]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h13,h14]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h13,h14]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h13,h14]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h13,h14]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h13,h14]
  · intro r h10 h15 h12 h11 h14 h13 h1
    simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h13,h14,h10,h15,h12,h11,h14,h13,h1]

end E5R.Thermostat.I16PadCall
