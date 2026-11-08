import Projects.thermostat.CursorRestore
import Projects.thermostat.HighFrame
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.CursorRestore
open E5R E5R.Thermostat

theorem contract_full (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x800022e0#32) (hm : Memory.Block B (c.get 2) 32) (ha : (c.get 2).toNat%4 = 0) :
    ∃ d, DetSteps B img 7 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = ramRead ram (c.get 2+28#32) .w &&& ~~~1 ∧ d.get 2 = c.get 2+32#32 ∧
      Restored c d ram ∧ d.get 10 = c.get 10 ∧ d.sameCsr c ∧ HighFrame.Frame c d := by
  let c1 := c.wr 1 (ramRead ram (c.get 2+28#32) .w) 0x800022e2#32
  let c2 := c1.wr 8 (ramRead ram (c.get 2+24#32) .w) 0x800022e4#32
  let c3 := c2.wr 9 (ramRead ram (c.get 2+20#32) .w) 0x800022e6#32
  let c4 := c3.wr 18 (ramRead ram (c.get 2+16#32) .w) 0x800022e8#32
  let c5 := c4.wr 19 (ramRead ram (c.get 2+12#32) .w) 0x800022ea#32
  let c6 := c5.wr 2 (c.get 2+32#32) 0x800022ec#32
  let d := c6.goto (ramRead ram (c.get 2+28#32) .w &&& ~~~1)
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact cu2147492576) fun o => ?_
    rw [exec_load,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned (c.get 2) 7 ha) (Memory.block_access hm (off := 28) (by decide) (by decide)),hp];rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x800022e2#32).getLsbD 0 = false;decide) cu2147492578 fun o => ?_
    have hv : c1.get 2 = c.get 2 := by simp [c1,Core.wr_get_ne]
    rw [exec_load,hv,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned (c.get 2) 6 ha) (Memory.block_access hm (off := 24) (by decide) (by decide))];rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x800022e4#32).getLsbD 0 = false;decide) cu2147492580 fun o => ?_
    have hv : c2.get 2 = c.get 2 := by simp [c2,c1,Core.wr_get_ne]
    rw [exec_load,hv,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned (c.get 2) 5 ha) (Memory.block_access hm (off := 20) (by decide) (by decide))];rfl
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine detStep_of (by change (0x800022e6#32).getLsbD 0 = false;decide) cu2147492582 fun o => ?_
    have hv : c3.get 2 = c.get 2 := by simp [c3,c2,c1,Core.wr_get_ne]
    rw [exec_load,hv,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned (c.get 2) 4 ha) (Memory.block_access hm (off := 16) (by decide) (by decide))];rfl
  have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine detStep_of (by change (0x800022e8#32).getLsbD 0 = false;decide) cu2147492584 fun o => ?_
    have hv : c4.get 2 = c.get 2 := by simp [c4,c3,c2,c1,Core.wr_get_ne]
    rw [exec_load,hv,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned (c.get 2) 3 ha) (Memory.block_access hm (off := 12) (by decide) (by decide))];rfl
  have s5 : DetStep B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine detStep_of (by change (0x800022ea#32).getLsbD 0 = false;decide) cu2147492586 fun o => ?_
    have hv : c5.get 2 = c.get 2 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne]
    rw [exec_opimm,hv];rfl
  have s6 : DetStep B img ⟨c6,ram⟩ ⟨d,ram⟩ := by
    refine detStep_of (by change (0x800022ec#32).getLsbD 0 = false;decide) cu2147492588 fun o => ?_
    have hv : c6.get 1 = ramRead ram (c.get 2+28#32) .w := by simp [d,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_jalr,hv,BitVec.add_zero]
    change interp B img o (jump c6 (ramRead ram (c.get 2+28#32) .w &&& ~~~1)) ram 0 [] = _
    rw [jump_ok _ _ (clear_bit0 _)];rfl
  refine ⟨d,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.single s6)))))),rfl,?_,?_,?_,by rfl,?_⟩
  · simp [d,c6,Core.wr_get]
  · constructor
    · simp [d,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    · simp [d,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    · simp [d,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    · simp [d,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    · simp [d,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · simp [d,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · intro r hr
    have hn (k : Reg) (hk : k.val < 20) : r ≠ k := HighFrame.ne r k hr hk
    simp [d,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,hn 1 (by decide),hn 2 (by decide),hn 8 (by decide),hn 9 (by decide),hn 18 (by decide),hn 19 (by decide)]
end E5R.Thermostat.CursorRestore
