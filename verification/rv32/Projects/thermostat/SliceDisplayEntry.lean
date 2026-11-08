import Projects.thermostat.SliceFormatCode
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.SliceDisplayEntry
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (ptr src len fmt : Word) (h10 : c.get 10 = ptr) (h11 : c.get 11 = fmt)
    (hm : Memory.Block B ptr 8) (ha : ptr.toNat%4 = 0)
    (hsrc : ramRead ram ptr .w = src) (hlen : ramRead ram (ptr+4#32) .w = len)
    (hp : c.pc = 0x8000228c#32) :
    ∃ d, DetSteps B img 8 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x8000513e#32 ∧
      d.get 12 = fmt ∧ d.get 13 = len ∧ d.get 14 = fmt ∧ d.get 10 = src ∧ d.get 11 = len ∧ d.get 6 = 0x80005298#32 ∧ (∀ r : Reg, r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 10 → r ≠ 11 → r ≠ 6 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 12 (src) 0x8000228e#32
  let c2 := c1.wr 13 (len) 0x80002290#32
  let c3 := c2.wr 14 (fmt) 0x80002292#32
  let c4 := c3.wr 10 (src) 0x80002294#32
  let c5 := c4.wr 11 (len) 0x80002296#32
  let c6 := c5.wr 12 (fmt) 0x80002298#32
  let c7 := c6.wr 6 (0x80005298#32) 0x8000229c#32
  let c8 := c7.goto 0x8000513e#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact sf2147492492) fun o => ?_
    rw [exec_load,h10,BitVec.add_zero,interp_load_ram (B := B) (img := img) (w := .w) o ha
      (by simpa only [BitVec.add_zero] using Memory.block_access hm (off := 0) (by decide) (by decide)),hsrc,hp];first | rfl | (rw [hp]; rfl)
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x8000228e#32).getLsbD 0 = false;decide) sf2147492494 fun o => ?_
    have hv : c1.get 10 = ptr := by simp [c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_load,hv,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned ptr 1 ha) (Memory.block_access hm (off := 4) (by decide) (by decide)),hlen];first | rfl | (rw [hp]; rfl)
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x80002290#32).getLsbD 0 = false;decide) sf2147492496 fun o => ?_
    have hv : c2.get 11 = fmt := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine detStep_of (by change (0x80002292#32).getLsbD 0 = false;decide) sf2147492498 fun o => ?_
    have hv : c3.get 12 = src := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine detStep_of (by change (0x80002294#32).getLsbD 0 = false;decide) sf2147492500 fun o => ?_
    have hv : c4.get 13 = len := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  have s5 : DetStep B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine detStep_of (by change (0x80002296#32).getLsbD 0 = false;decide) sf2147492502 fun o => ?_
    have hv : c5.get 14 = fmt := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  have s6 : DetStep B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine detStep_of (by change (0x80002298#32).getLsbD 0 = false;decide) sf2147492504 fun o => ?_
    rw [exec_auipc];first | rfl | (rw [hp]; rfl)
  have s7 : DetStep B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine detStep_of (by change (0x8000229c#32).getLsbD 0 = false;decide) sf2147492508 fun o => ?_
    have hv : c7.get 6 = 0x80005298#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_jalr,hv]
    change interp B img o (jump c7 ((0x80005298#32+0xfffffea6#32) &&& ~~~1)) ram 0 [] = _
    rw [show (0x80005298#32+0xfffffea6#32) &&& ~~~1 = 0x8000513e#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp]; rfl)
  refine ⟨c8,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.single s7))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
  · intro r h12 h13 h14 h10 h11 h6
    simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h10,h11,h6]
end E5R.Thermostat.SliceDisplayEntry
