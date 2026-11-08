-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.CursorGuard
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.CursorGuard
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (obj : Word) (cap pos len : Nat)
    (hp : c.pc = 0x800022ac#32) (h10 : c.get 10 = obj) (h12 : c.get 12 = BitVec.ofNat 32 len)
    (hm : Memory.Block B obj 12) (ha : obj.toNat%4 = 0)
    (hc : ramRead ram (obj+4#32) .w = BitVec.ofNat 32 cap)
    (hat : ramRead ram (obj+8#32) .w = BitVec.ofNat 32 pos)
    (hb : cap < 2^32) (hi : pos ≤ cap) (hl : len < 2^32) :
    ∃ d, Quiet.Steps B img 5 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = (if len ≤ cap-pos then 0x800022ba#32 else 0x800022dc#32) ∧
      d.get 8 = BitVec.ofNat 32 len ∧ d.get 12 = BitVec.ofNat 32 cap ∧ d.get 14 = BitVec.ofNat 32 pos ∧
      d.get 18 = BitVec.ofNat 32 (cap-pos) ∧
      (∀ r : Reg, r ≠ 8 → r ≠ 12 → r ≠ 14 → r ≠ 18 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 8 (BitVec.ofNat 32 len) 0x800022ae#32
  let c2 := c1.wr 12 (BitVec.ofNat 32 cap) 0x800022b0#32
  let c3 := c2.wr 14 (BitVec.ofNat 32 pos) 0x800022b2#32
  let c4 := c3.wr 18 (BitVec.ofNat 32 (cap-pos)) 0x800022b6#32
  let d := c4.goto (if len ≤ cap-pos then 0x800022ba#32 else 0x800022dc#32)
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact cu2147492524) fun o => ?_
    rw [exec_op,h12,Core.get_zero,hp]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x800022ae#32).getLsbD 0 = false;decide) cu2147492526 fun o => ?_
    have hv : c1.get 10 = obj := by simp [c1,Core.wr_get_ne,h10]
    rw [exec_load,hv,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned obj 1 ha) (Memory.block_access hm (off := 4) (by decide) (by decide)),hc];rfl
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x800022b0#32).getLsbD 0 = false;decide) cu2147492528 fun o => ?_
    have hv : c2.get 10 = obj := by simp [c2,c1,Core.wr_get_ne,h10]
    rw [exec_load,hv,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned obj 2 ha) (Memory.block_access hm (off := 8) (by decide) (by decide)),hat];rfl
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (0x800022b2#32).getLsbD 0 = false;decide) cu2147492530 fun o => ?_
    have hv12 : c3.get 12 = BitVec.ofNat 32 cap := by simp [c3,c2,Core.wr_get_ne,Core.wr_get]
    have hv14 : c3.get 14 = BitVec.ofNat 32 pos := by simp [c3,Core.wr_get]
    rw [exec_op,hv12,hv14]
    change interp B img o (.done (c3.wr 18 (BitVec.ofNat 32 cap-BitVec.ofNat 32 pos) 0x800022b6#32)) ram 0 [] = _
    rw [BitVec.ofNat_sub_ofNat_of_le cap pos (by omega) hi];rfl
  have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨d,ram⟩ := by
    refine QuietDet.step_of (by change (0x800022b6#32).getLsbD 0 = false;decide) cu2147492534 fun o => ?_
    have hv18 : c4.get 18 = BitVec.ofNat 32 (cap-pos) := by simp [c4,Core.wr_get]
    have hv8 : c4.get 8 = BitVec.ofNat 32 len := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_branch,hv18,hv8,ParamMath.ult (cap-pos) len (by omega) hl]
    by_cases he : len ≤ cap-pos
    · have hf : ¬cap-pos < len := by omega
      rw [decide_eq_false hf];simp only [Bool.false_eq_true,ite_false,d,ite_eq_left he];rfl
    · have ht : cap-pos < len := by omega
      rw [decide_eq_true ht];simp only [ite_true,d,ite_eq_right he]
      change interp B img o (jump c4 0x800022dc#32) ram 0 [] = _
      rw [jump_ok _ _ (by decide)];rfl
  refine ⟨d,.step s0 (.step s1 (.step s2 (.step s3 (.single s4)))),rfl,?_,?_,?_,?_,?_,by rfl⟩
  · simp [d,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · simp [d,c4,c3,c2,Core.wr_get_ne,Core.wr_get]
  · simp [d,c4,c3,Core.wr_get_ne,Core.wr_get]
  · simp [d,c4,Core.wr_get]
  · intro r h8 h12 h14 h18
    simp [d,c4,c3,c2,c1,Core.wr_get_ne,h8,h12,h14,h18]

end E5R.Thermostat.CursorGuard
