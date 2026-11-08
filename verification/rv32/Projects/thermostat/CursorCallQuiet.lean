-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.CursorCall
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.CursorCall
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (obj dst : Word) (cap pos len : Nat)
    (hp : c.pc = 0x800022ba#32) (h10 : c.get 10 = obj) (h8 : c.get 8 = BitVec.ofNat 32 len)
    (h12 : c.get 12 = BitVec.ofNat 32 cap) (h14 : c.get 14 = BitVec.ofNat 32 pos)
    (hm : Memory.Block B obj 12) (ha : obj.toNat%4 = 0) (hptr : ramRead ram obj .w = dst)
    (hb : cap < 2^32) (hi : pos ≤ cap) (hf : len ≤ cap-pos) :
    ∃ d, Quiet.Steps B img 10 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80005182#32 ∧ d.get 1 = 0x800022d8#32 ∧
      d.get 10 = dst+BitVec.ofNat 32 pos ∧ d.get 12 = BitVec.ofNat 32 len ∧
      d.get 9 = BitVec.ofNat 32 (pos+len) ∧ d.get 19 = obj ∧
      (∀ r : Reg, r ≠ 1 → r ≠ 9 → r ≠ 10 → r ≠ 12 → r ≠ 13 → r ≠ 19 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 9 (BitVec.ofNat 32 (pos+len)) 0x800022be#32
  let c2 := c1.goto 0x800022c2#32
  let c3 := c2.goto 0x800022c6#32
  let c4 := c3.wr 13 dst 0x800022c8#32
  let c5 := c4.wr 13 (dst+BitVec.ofNat 32 pos) 0x800022ca#32
  let c6 := c5.wr 19 obj 0x800022cc#32
  let c7 := c6.wr 10 (dst+BitVec.ofNat 32 pos) 0x800022ce#32
  let c8 := c7.wr 12 (BitVec.ofNat 32 len) 0x800022d0#32
  let c9 := c8.wr 1 0x800052d0#32 0x800022d4#32
  let d := c9.wr 1 0x800022d8#32 0x80005182#32
  have hsum : pos+len < 2^32 := by omega
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact cu2147492538) fun o => ?_
    rw [exec_op,h14,h8]
    change interp B img o (.done (c.wr 9 (BitVec.ofNat 32 pos+BitVec.ofNat 32 len) (c.pc+4#32))) ram 0 [] = _
    rw [←BitVec.ofNat_add,hp];rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x800022be#32).getLsbD 0 = false;decide) cu2147492542 fun o => ?_
    have hv9 : c1.get 9 = BitVec.ofNat 32 (pos+len) := by simp [c1,Core.wr_get]
    have hv14 : c1.get 14 = BitVec.ofNat 32 pos := by simp [c1,Core.wr_get_ne,h14]
    rw [exec_branch,hv9,hv14,ParamMath.ult (pos+len) pos hsum (by omega),decide_eq_false (show ¬pos+len < pos by omega)];rfl
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x800022c2#32).getLsbD 0 = false;decide) cu2147492546 fun o => ?_
    have hv9 : c2.get 9 = BitVec.ofNat 32 (pos+len) := by simp [c2,c1,Core.wr_get]
    have hv12 : c2.get 12 = BitVec.ofNat 32 cap := by simp [c2,c1,Core.wr_get_ne,h12]
    rw [exec_branch,hv12,hv9,ParamMath.ult cap (pos+len) hb hsum,decide_eq_false (show ¬cap < pos+len by omega)];rfl
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (0x800022c6#32).getLsbD 0 = false;decide) cu2147492550 fun o => ?_
    have hv : c3.get 10 = obj := by simp [c3,c2,c1,Core.wr_get_ne,h10]
    rw [exec_load,hv,BitVec.add_zero,interp_load_ram (B := B) (img := img) (w := .w) o ha
      (by simpa only [BitVec.add_zero] using Memory.block_access hm (off := 0) (by decide) (by decide)),hptr];rfl
  have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine QuietDet.step_of (by change (0x800022c8#32).getLsbD 0 = false;decide) cu2147492552 fun o => ?_
    have hv13 : c4.get 13 = dst := by simp [c4,Core.wr_get]
    have hv14 : c4.get 14 = BitVec.ofNat 32 pos := by simp [c4,c3,c2,c1,Core.wr_get_ne,h14]
    rw [exec_op,hv13,hv14];rfl
  have s5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine QuietDet.step_of (by change (0x800022ca#32).getLsbD 0 = false;decide) cu2147492554 fun o => ?_
    have hv : c5.get 10 = obj := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,h10]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];rfl
  have s6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine QuietDet.step_of (by change (0x800022cc#32).getLsbD 0 = false;decide) cu2147492556 fun o => ?_
    have hv : c6.get 13 = dst+BitVec.ofNat 32 pos := by simp [c6,c5,Core.wr_get_ne,Core.wr_get]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];rfl
  have s7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine QuietDet.step_of (by change (0x800022ce#32).getLsbD 0 = false;decide) cu2147492558 fun o => ?_
    have hv : c7.get 8 = BitVec.ofNat 32 len := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,h8]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];rfl
  have s8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine QuietDet.step_of (by change (0x800022d0#32).getLsbD 0 = false;decide) cu2147492560 fun o => ?_
    rw [exec_auipc];rfl
  have s9 : Quiet.Step B img ⟨c9,ram⟩ ⟨d,ram⟩ := by
    refine QuietDet.step_of (by change (0x800022d4#32).getLsbD 0 = false;decide) cu2147492564 fun o => ?_
    have hv : c9.get 1 = 0x800052d0#32 := by simp [c9,Core.wr_get]
    rw [exec_jalr,hv]
    change interp B img o (jump (c9.set 1 0x800022d8#32) ((0x800052d0#32+0xfffffeb2#32) &&& ~~~1)) ram 0 [] = _
    rw [show (0x800052d0#32+0xfffffeb2#32) &&& ~~~1 = 0x80005182#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  refine ⟨d,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.step s8 (.single s9))))))))),rfl,?_,?_,?_,?_,?_,?_,by rfl⟩
  · simp [d,Core.wr_get]
  · simp [d,c9,c8,c7,Core.wr_get_ne,Core.wr_get]
  · simp [d,c9,c8,Core.wr_get_ne,Core.wr_get]
  · simp [d,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · simp [d,c9,c8,c7,c6,Core.wr_get_ne,Core.wr_get]
  · intro r h1 h9 h10 h12 h13 h19
    simp [d,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,h1,h9,h10,h12,h13,h19]

end E5R.Thermostat.CursorCall
