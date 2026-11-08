import Projects.thermostat.WritePrefixCode
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.PrefixRestore
open E5R E5R.Thermostat

structure Restored (before after : Core) (ram : Word → BitVec 8) : Prop where
  x1 : after.get 1 = ramRead ram (before.get 2+28#32) .w
  x8 : after.get 8 = ramRead ram (before.get 2+24#32) .w
  x9 : after.get 9 = ramRead ram (before.get 2+20#32) .w
  x18 : after.get 18 = ramRead ram (before.get 2+16#32) .w
  x19 : after.get 19 = ramRead ram (before.get 2+12#32) .w
  x20 : after.get 20 = ramRead ram (before.get 2+8#32) .w

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80004e4e#32) (hm : Memory.Block B (c.get 2) 32) (ha : (c.get 2).toNat%4 = 0) :
    ∃ d, DetSteps B img 8 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = ramRead ram (c.get 2+28#32) .w &&& ~~~1 ∧ d.get 2 = c.get 2+32#32 ∧
      Restored c d ram ∧ (∀ r : Reg, r ≠ 1 → r ≠ 2 → r ≠ 8 → r ≠ 9 → r ≠ 18 → r ≠ 19 → r ≠ 20 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 1 (ramRead ram (c.get 2+28#32) .w) 0x80004e50#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact wp2147503694) fun o => ?_
    rw [exec_load,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned (c.get 2) 7 ha) (Memory.block_access hm (off := 28) (by decide) (by decide)),hp];rfl
  let c2 := c1.wr 8 (ramRead ram (c.get 2+24#32) .w) 0x80004e52#32
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x80004e50#32).getLsbD 0 = false;decide) wp2147503696 fun o => ?_
    have hs : c1.get 2 = c.get 2 := by simp [c1,Core.wr_get_ne]
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned (c.get 2) 6 ha) (Memory.block_access hm (off := 24) (by decide) (by decide))];rfl
  let c3 := c2.wr 9 (ramRead ram (c.get 2+20#32) .w) 0x80004e54#32
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x80004e52#32).getLsbD 0 = false;decide) wp2147503698 fun o => ?_
    have hs : c2.get 2 = c.get 2 := by simp [c2,c1,Core.wr_get_ne]
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned (c.get 2) 5 ha) (Memory.block_access hm (off := 20) (by decide) (by decide))];rfl
  let c4 := c3.wr 18 (ramRead ram (c.get 2+16#32) .w) 0x80004e56#32
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine detStep_of (by change (0x80004e54#32).getLsbD 0 = false;decide) wp2147503700 fun o => ?_
    have hs : c3.get 2 = c.get 2 := by simp [c3,c2,c1,Core.wr_get_ne]
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned (c.get 2) 4 ha) (Memory.block_access hm (off := 16) (by decide) (by decide))];rfl
  let c5 := c4.wr 19 (ramRead ram (c.get 2+12#32) .w) 0x80004e58#32
  have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine detStep_of (by change (0x80004e56#32).getLsbD 0 = false;decide) wp2147503702 fun o => ?_
    have hs : c4.get 2 = c.get 2 := by simp [c4,c3,c2,c1,Core.wr_get_ne]
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned (c.get 2) 3 ha) (Memory.block_access hm (off := 12) (by decide) (by decide))];rfl
  let c6 := c5.wr 20 (ramRead ram (c.get 2+8#32) .w) 0x80004e5a#32
  have s5 : DetStep B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine detStep_of (by change (0x80004e58#32).getLsbD 0 = false;decide) wp2147503704 fun o => ?_
    have hs : c5.get 2 = c.get 2 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne]
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned (c.get 2) 2 ha) (Memory.block_access hm (off := 8) (by decide) (by decide))];rfl
  let c7 := c6.wr 2 (c.get 2+32#32) 0x80004e5c#32
  let d := c7.goto (ramRead ram (c.get 2+28#32) .w &&& ~~~1)
  have s6 : DetStep B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine detStep_of (by change (0x80004e5a#32).getLsbD 0 = false;decide) wp2147503706 fun o => ?_
    have hs : c6.get 2 = c.get 2 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne]
    rw [exec_opimm,hs];rfl
  have s7 : DetStep B img ⟨c7,ram⟩ ⟨d,ram⟩ := by
    refine detStep_of (by change (0x80004e5c#32).getLsbD 0 = false;decide) wp2147503708 fun o => ?_
    have hv : c7.get 1 = ramRead ram (c.get 2+28#32) .w := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_jalr,hv,BitVec.add_zero]
    change interp B img o (jump c7 (ramRead ram (c.get 2+28#32) .w &&& ~~~1)) ram 0 [] = _
    rw [jump_ok _ _ (clear_bit0 _)];rfl
  refine ⟨d,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.single s7))))))),rfl,?_,?_,?_,by rfl⟩
  · simp [d,c7,Core.wr_get]
  · constructor
    · simp [d,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    · simp [d,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    · simp [d,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    · simp [d,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    · simp [d,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    · simp [d,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · intro r h1 h2 h8 h9 h18 h19 h20
    simp [d,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,h1,h2,h8,h9,h18,h19,h20]
end E5R.Thermostat.PrefixRestore
