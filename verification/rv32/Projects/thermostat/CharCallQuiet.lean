-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.CharCall
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.CharCall
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (sp obj dst : Word) (cap pos len : Nat)
    (hp : c.pc = 0x80002394#32) (hsp : c.get 2 = sp) (h10 : c.get 10 = obj) (h8 : c.get 8 = BitVec.ofNat 32 len)
    (h12 : c.get 12 = BitVec.ofNat 32 cap) (h11 : c.get 11 = BitVec.ofNat 32 pos)
    (hm : Memory.Block B obj 12) (ha : obj.toNat%4 = 0) (hptr : ramRead ram obj .w = dst)
    (hb : cap < 2^32) (hi : pos ≤ cap) (hf : len ≤ cap-pos) :
    ∃ d, Quiet.Steps B img 11 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80005182#32 ∧ d.get 1 = 0x800023b4#32 ∧
      d.get 10 = dst+BitVec.ofNat 32 pos ∧ d.get 11 = sp+8#32 ∧ d.get 12 = BitVec.ofNat 32 len ∧
      d.get 9 = BitVec.ofNat 32 (pos+len) ∧ d.get 19 = obj ∧
      (∀ r : Reg, r ≠ 1 → r ≠ 9 → r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 19 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 9 (BitVec.ofNat 32 (pos+len)) 0x80002398#32
  let c2 := c1.goto 0x8000239c#32
  let c3 := c2.goto 0x800023a0#32
  let c4 := c3.wr 12 (dst) 0x800023a2#32
  let c5 := c4.wr 12 (dst+BitVec.ofNat 32 pos) 0x800023a4#32
  let c6 := c5.wr 11 (sp+8#32) 0x800023a6#32
  let c7 := c6.wr 19 (obj) 0x800023a8#32
  let c8 := c7.wr 10 (dst+BitVec.ofNat 32 pos) 0x800023aa#32
  let c9 := c8.wr 12 (BitVec.ofNat 32 len) 0x800023ac#32
  let c10 := c9.wr 1 (0x800053ac#32) 0x800023b0#32
  let c11 := c10.wr 1 (0x800023b4#32) 0x80005182#32
  have hsum : pos+len < 2^32 := by omega
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact ch2147492756) fun o => ?_
    have hv0 : c.get 11 = (BitVec.ofNat 32 pos) := by simp [Core.wr_get_ne,Core.wr_get,hsp,h10,h8,h12,h11]
    have hv1 : c.get 8 = (BitVec.ofNat 32 len) := by simp [Core.wr_get_ne,Core.wr_get,hsp,h10,h8,h12,h11]
    rw [exec_op,hv0,hv1]
    change interp B img o (.done (c.wr 9 (BitVec.ofNat 32 pos+BitVec.ofNat 32 len) (c.pc+4#32))) ram 0 [] = _
    rw [←BitVec.ofNat_add,hp];rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002398#32).getLsbD 0 = false;decide) ch2147492760 fun o => ?_
    have hv0 : c1.get 9 = (BitVec.ofNat 32 (pos+len)) := by simp [c1,Core.wr_get_ne,Core.wr_get,hsp,h10,h8,h12,h11]
    have hv1 : c1.get 11 = (BitVec.ofNat 32 pos) := by simp [c1,Core.wr_get_ne,Core.wr_get,hsp,h10,h8,h12,h11]
    rw [exec_branch,hv0,hv1,ParamMath.ult (pos+len) pos hsum (by omega),decide_eq_false (show ¬pos+len < pos by omega)];rfl
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000239c#32).getLsbD 0 = false;decide) ch2147492764 fun o => ?_
    have hv0 : c2.get 12 = (BitVec.ofNat 32 cap) := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,hsp,h10,h8,h12,h11]
    have hv1 : c2.get 9 = (BitVec.ofNat 32 (pos+len)) := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,hsp,h10,h8,h12,h11]
    rw [exec_branch,hv0,hv1,ParamMath.ult cap (pos+len) hb hsum,decide_eq_false (show ¬cap < pos+len by omega)];rfl
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (0x800023a0#32).getLsbD 0 = false;decide) ch2147492768 fun o => ?_
    have hv0 : c3.get 10 = (obj) := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,hsp,h10,h8,h12,h11]
    rw [exec_load,hv0,BitVec.add_zero,interp_load_ram (B := B) (img := img) (w := .w) o ha
      (by simpa only [BitVec.add_zero] using Memory.block_access hm (off := 0) (by decide) (by decide)),hptr];rfl
  have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine QuietDet.step_of (by change (0x800023a2#32).getLsbD 0 = false;decide) ch2147492770 fun o => ?_
    have hv0 : c4.get 12 = (dst) := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hsp,h10,h8,h12,h11]
    have hv1 : c4.get 11 = (BitVec.ofNat 32 pos) := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hsp,h10,h8,h12,h11]
    rw [exec_op,hv0,hv1];rfl
  have s5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine QuietDet.step_of (by change (0x800023a4#32).getLsbD 0 = false;decide) ch2147492772 fun o => ?_
    have hv0 : c5.get 2 = (sp) := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hsp,h10,h8,h12,h11]
    rw [exec_opimm,hv0];rfl
  have s6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine QuietDet.step_of (by change (0x800023a6#32).getLsbD 0 = false;decide) ch2147492774 fun o => ?_
    have hv0 : c6.get 10 = (obj) := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hsp,h10,h8,h12,h11]
    rw [exec_op,Core.get_zero,hv0]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];rfl
  have s7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine QuietDet.step_of (by change (0x800023a8#32).getLsbD 0 = false;decide) ch2147492776 fun o => ?_
    have hv0 : c7.get 12 = (dst+BitVec.ofNat 32 pos) := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hsp,h10,h8,h12,h11]
    rw [exec_op,Core.get_zero,hv0]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];rfl
  have s8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine QuietDet.step_of (by change (0x800023aa#32).getLsbD 0 = false;decide) ch2147492778 fun o => ?_
    have hv0 : c8.get 8 = (BitVec.ofNat 32 len) := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hsp,h10,h8,h12,h11]
    rw [exec_op,Core.get_zero,hv0]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];rfl
  have s9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine QuietDet.step_of (by change (0x800023ac#32).getLsbD 0 = false;decide) ch2147492780 fun o => ?_
    rw [exec_auipc];rfl
  have s10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine QuietDet.step_of (by change (0x800023b0#32).getLsbD 0 = false;decide) ch2147492784 fun o => ?_
    have hv0 : c10.get 1 = (0x800053ac#32) := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hsp,h10,h8,h12,h11]
    rw [exec_jalr,hv0]
    change interp B img o (jump (c10.set 1 0x800023b4#32) ((0x800053ac#32+0xfffffdd6#32) &&& ~~~1)) ram 0 [] = _
    rw [show (0x800053ac#32+0xfffffdd6#32) &&& ~~~1 = 0x80005182#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  refine ⟨c11,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.step s8 (.step s9 (.single s10)))))))))),rfl,?_,?_,?_,?_,?_,?_,?_,by rfl⟩
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · intro r h1 h9 h10 h11 h12 h19
    simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h1,h9,h10,h11,h12,h19]

end E5R.Thermostat.CharCall
