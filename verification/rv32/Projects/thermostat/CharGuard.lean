import Projects.thermostat.WriteCharCode
import Projects.thermostat.Memory
import Projects.thermostat.ParamMath
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.CharGuard
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (obj : Word) (cap pos : Nat)
    (hp : c.pc = 0x80002388#32) (h10 : c.get 10 = obj) (h8 : c.get 8 = 1#32)
    (hm : Memory.Block B obj 12) (ha : obj.toNat%4 = 0)
    (hc : ramRead ram (obj+4#32) .w = BitVec.ofNat 32 cap)
    (hat : ramRead ram (obj+8#32) .w = BitVec.ofNat 32 pos) (hb : cap < 2^32) (hi : pos ≤ cap) :
    ∃ d, DetSteps B img 4 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = (if 1 ≤ cap-pos then 0x80002394#32 else 0x800023b8#32) ∧
      d.get 12 = BitVec.ofNat 32 cap ∧ d.get 11 = BitVec.ofNat 32 pos ∧ d.get 18 = BitVec.ofNat 32 (cap-pos) ∧
      (∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 18 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 12 (BitVec.ofNat 32 cap) 0x8000238a#32
  let c2 := c1.wr 11 (BitVec.ofNat 32 pos) 0x8000238c#32
  let c3 := c2.wr 18 (BitVec.ofNat 32 (cap-pos)) 0x80002390#32
  let d := c3.goto (if 1 ≤ cap-pos then 0x80002394#32 else 0x800023b8#32)
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact ch2147492744) fun o => ?_
    rw [exec_load,h10,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned obj 1 ha) (Memory.block_access hm (off := 4) (by decide) (by decide)),hc,hp];rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x8000238a#32).getLsbD 0 = false;decide) ch2147492746 fun o => ?_
    have hv : c1.get 10 = obj := by simp [c1,Core.wr_get_ne,h10]
    rw [exec_load,hv,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned obj 2 ha) (Memory.block_access hm (off := 8) (by decide) (by decide)),hat];rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x8000238c#32).getLsbD 0 = false;decide) ch2147492748 fun o => ?_
    have hv12 : c2.get 12 = BitVec.ofNat 32 cap := by simp [c2,c1,Core.wr_get_ne,Core.wr_get]
    have hv11 : c2.get 11 = BitVec.ofNat 32 pos := by simp [c2,Core.wr_get]
    rw [exec_op,hv12,hv11]
    change interp B img o (.done (c2.wr 18 (BitVec.ofNat 32 cap-BitVec.ofNat 32 pos) 0x80002390#32)) ram 0 [] = _
    rw [BitVec.ofNat_sub_ofNat_of_le cap pos (by omega) hi];rfl
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨d,ram⟩ := by
    refine detStep_of (by change (0x80002390#32).getLsbD 0 = false;decide) ch2147492752 fun o => ?_
    have hv18 : c3.get 18 = BitVec.ofNat 32 (cap-pos) := by simp [c3,Core.wr_get]
    have hv8 : c3.get 8 = 1#32 := by simp [c3,c2,c1,Core.wr_get_ne,h8]
    rw [exec_branch,hv18,hv8,ParamMath.ult (cap-pos) 1 (by omega) (by decide)]
    by_cases he : 1 ≤ cap-pos
    · rw [decide_eq_false (show ¬cap-pos < 1 by omega)]
      simp only [Bool.false_eq_true,ite_false,d,ite_eq_left he];rfl
    · rw [decide_eq_true (show cap-pos < 1 by omega)]
      simp only [ite_true,d,ite_eq_right he]
      change interp B img o (jump c3 0x800023b8#32) ram 0 [] = _
      rw [jump_ok _ _ (by decide)];rfl
  refine ⟨d,.step s0 (.step s1 (.step s2 (.single s3))),rfl,?_,?_,?_,?_,by rfl⟩
  · simp [d,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · simp [d,c3,c2,Core.wr_get_ne,Core.wr_get]
  · simp [d,c3,Core.wr_get]
  · intro r h11 h12 h18;simp [d,c3,c2,c1,Core.wr_get_ne,h11,h12,h18]
end E5R.Thermostat.CharGuard
