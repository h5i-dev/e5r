-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.I16LargePair
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.I16LargePair
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (sp p0 p1 : Word) (b0 b1 b2 b3 : BitVec 8)
    (hp : c.pc = 0x80004eda#32) (hs : c.get 2 = sp) (h14 : c.get 14 = p0) (h11 : c.get 11 = p1)
    (hb0 : ReadBytes.Byte B img ram p0 b0) (hb1 : ReadBytes.Byte B img ram (p0+1#32) b1)
    (hb2 : ReadBytes.Byte B img ram p1 b2) (hb3 : ReadBytes.Byte B img ram (p1+1#32) b3)
    (hm : Memory.Block B sp 16) :
    ∃ d, Quiet.Steps B img 10 ⟨c,ram⟩ ⟨d,memory ram sp b0 b1 b2 b3⟩ ∧ d.pc = 0x80004f3c#32 ∧
      d.get 14 = 1#32 ∧ (∀ r : Reg, r ≠ 15 → r ≠ 14 → r ≠ 16 → r ≠ 11 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 15 (BitVec.ofNat 32 b0.toNat) 0x80004ede#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact di2147503834) fun o => ?_
    rw [exec_load,h14,BitVec.add_zero,ReadBytes.load hb0,ReadBytes.extend_byte,←Memory.ofNat_width,hp];rfl
  let c2 := c1.wr 14 (BitVec.ofNat 32 b1.toNat) 0x80004ee2#32
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004ede#32).getLsbD 0 = false;decide) di2147503838 fun o => ?_
    have hv : c1.get 14 = p0 := by simp [c1,Core.wr_get_ne,h14]
    rw [exec_load,hv,ReadBytes.load hb1,ReadBytes.extend_byte,←Memory.ofNat_width];rfl
  let c3 := c2.wr 16 (BitVec.ofNat 32 b2.toNat) 0x80004ee6#32
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004ee2#32).getLsbD 0 = false;decide) di2147503842 fun o => ?_
    have hv : c2.get 11 = p1 := by simp [c2,c1,Core.wr_get_ne,h11]
    rw [exec_load,hv,BitVec.add_zero,ReadBytes.load hb2,ReadBytes.extend_byte,←Memory.ofNat_width];rfl
  let c4 := c3.wr 11 (BitVec.ofNat 32 b3.toNat) 0x80004eea#32
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004ee6#32).getLsbD 0 = false;decide) di2147503846 fun o => ?_
    have hv : c3.get 11 = p1 := by simp [c3,c2,c1,Core.wr_get_ne,h11]
    rw [exec_load,hv,ReadBytes.load hb3,ReadBytes.extend_byte,←Memory.ofNat_width];rfl
  let r1 := ramPut ram (sp+4#32) b0
  let c5 := c4.goto 0x80004eee#32
  have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,r1⟩ := by
    refine QuietDet.step_of (by change (0x80004eea#32).getLsbD 0 = false;decide) di2147503850 fun o => ?_
    have hsp : c4.get 2 = sp := by simp [c4,c3,c2,c1,Core.wr_get_ne,hs]
    have hv : c4.get 15 = BitVec.ofNat 32 b0.toNat := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_store,hsp,hv,interp_store_ram (B := B) (img := img) (w := .b) o
      (Nat.mod_one _) (Memory.block_access hm (off := 4) (by decide) (by decide))]
    change interp B img o (.done c5) (ramPut ram (sp+4#32) (byteOf (BitVec.ofNat 32 b0.toNat) 0)) 0 [] = _
    rw [SmallCopyTurn.byte_word];rfl
  let r2 := ramPut r1 (sp+5#32) b1
  let c6 := c5.goto 0x80004ef2#32
  have s5 : Quiet.Step B img ⟨c5,r1⟩ ⟨c6,r2⟩ := by
    refine QuietDet.step_of (by change (0x80004eee#32).getLsbD 0 = false;decide) di2147503854 fun o => ?_
    have hsp : c5.get 2 = sp := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,hs]
    have hv : c5.get 14 = BitVec.ofNat 32 b1.toNat := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_store,hsp,hv,interp_store_ram (B := B) (img := img) (w := .b) o
      (Nat.mod_one _) (Memory.block_access hm (off := 5) (by decide) (by decide))]
    change interp B img o (.done c6) (ramPut r1 (sp+5#32) (byteOf (BitVec.ofNat 32 b1.toNat) 0)) 0 [] = _
    rw [SmallCopyTurn.byte_word];rfl
  let r3 := ramPut r2 (sp+6#32) b2
  let c7 := c6.goto 0x80004ef6#32
  have s6 : Quiet.Step B img ⟨c6,r2⟩ ⟨c7,r3⟩ := by
    refine QuietDet.step_of (by change (0x80004ef2#32).getLsbD 0 = false;decide) di2147503858 fun o => ?_
    have hsp : c6.get 2 = sp := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,hs]
    have hv : c6.get 16 = BitVec.ofNat 32 b2.toNat := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_store,hsp,hv,interp_store_ram (B := B) (img := img) (w := .b) o
      (Nat.mod_one _) (Memory.block_access hm (off := 6) (by decide) (by decide))]
    change interp B img o (.done c7) (ramPut r2 (sp+6#32) (byteOf (BitVec.ofNat 32 b2.toNat) 0)) 0 [] = _
    rw [SmallCopyTurn.byte_word];rfl
  let r4 := ramPut r3 (sp+7#32) b3
  let c8 := c7.goto 0x80004efa#32
  have s7 : Quiet.Step B img ⟨c7,r3⟩ ⟨c8,r4⟩ := by
    refine QuietDet.step_of (by change (0x80004ef6#32).getLsbD 0 = false;decide) di2147503862 fun o => ?_
    have hsp : c7.get 2 = sp := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,hs]
    have hv : c7.get 11 = BitVec.ofNat 32 b3.toNat := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_store,hsp,hv,interp_store_ram (B := B) (img := img) (w := .b) o
      (Nat.mod_one _) (Memory.block_access hm (off := 7) (by decide) (by decide))]
    change interp B img o (.done c8) (ramPut r3 (sp+7#32) (byteOf (BitVec.ofNat 32 b3.toNat) 0)) 0 [] = _
    rw [SmallCopyTurn.byte_word];rfl
  let c9 := c8.wr 14 1#32 0x80004efc#32
  let d := c9.goto 0x80004f3c#32
  have s8 : Quiet.Step B img ⟨c8,r4⟩ ⟨c9,r4⟩ := by
    refine QuietDet.step_of (by change (0x80004efa#32).getLsbD 0 = false;decide) di2147503866 fun o => ?_
    rw [exec_opimm,Core.get_zero];rfl
  have s9 : Quiet.Step B img ⟨c9,r4⟩ ⟨d,r4⟩ := by
    refine QuietDet.step_of (by change (0x80004efc#32).getLsbD 0 = false;decide) di2147503868 fun o => ?_
    rw [exec_jal]
    change interp B img o (jump c9 0x80004f3c#32) r4 0 [] = _
    rw [jump_ok _ _ (by decide)];rfl
  refine ⟨d,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.step s8 (.single s9))))))))),rfl,?_,?_,by rfl⟩
  · simp [d,c9,Core.wr_get]
  · intro r h15 h14 h16 h11
    simp [d,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,h15,h14,h16,h11]

end E5R.Thermostat.I16LargePair
