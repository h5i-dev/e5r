import Projects.thermostat.WriteCharCode
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.CharSave
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp : Word) (c : Core) : Word → BitVec 8 :=
  ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ram) (sp+28#32) (c.get 1) .w) (sp+24#32) (c.get 8) .w) (sp+20#32) (c.get 9) .w) (sp+16#32) (c.get 18) .w) (sp+12#32) (c.get 19) .w

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word)
    (hp : c.pc = 0x80002302#32) (hsp : c.get 2 = sp+32#32)
    (hm : Memory.Block B sp 32) (ha : sp.toNat%4 = 0) :
    ∃ d, DetSteps B img 6 ⟨c,ram⟩ ⟨d,memory ram sp c⟩ ∧ d.pc = 0x8000230e#32 ∧
      d.get 2 = sp ∧ (∀ r : Reg, r ≠ 2 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 2 sp 0x80002304#32
  let c2 := c1.goto 0x80002306#32
  let c3 := c2.goto 0x80002308#32
  let c4 := c3.goto 0x8000230a#32
  let c5 := c4.goto 0x8000230c#32
  let c6 := c5.goto 0x8000230e#32
  let r1 := ramWrite ram (sp+28#32) (c.get 1) .w
  let r2 := ramWrite r1 (sp+24#32) (c.get 8) .w
  let r3 := ramWrite r2 (sp+20#32) (c.get 9) .w
  let r4 := ramWrite r3 (sp+16#32) (c.get 18) .w
  let r5 := ramWrite r4 (sp+12#32) (c.get 19) .w
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact ch2147492610) fun o => ?_
    rw [exec_opimm,hsp]
    simp only [alu]
    rw [BitVec.add_assoc,show 32#32+0xffffffe0#32 = 0#32 by decide +kernel,BitVec.add_zero,hp];rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,r1⟩ := by
    refine detStep_of (by change (0x80002304#32).getLsbD 0 = false;decide) ch2147492612 fun o => ?_
    have hs : c1.get 2 = sp := by simp [c1,Core.wr_get_ne,Core.wr_get]
    have hv : c1.get 1 = c.get 1 := by simp [c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 7 ha) (Memory.block_access hm (off := 28) (by decide) (by decide))];rfl
  have s2 : DetStep B img ⟨c2,r1⟩ ⟨c3,r2⟩ := by
    refine detStep_of (by change (0x80002306#32).getLsbD 0 = false;decide) ch2147492614 fun o => ?_
    have hs : c2.get 2 = sp := by simp [c2,c1,Core.wr_get_ne,Core.wr_get]
    have hv : c2.get 8 = c.get 8 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 6 ha) (Memory.block_access hm (off := 24) (by decide) (by decide))];rfl
  have s3 : DetStep B img ⟨c3,r2⟩ ⟨c4,r3⟩ := by
    refine detStep_of (by change (0x80002308#32).getLsbD 0 = false;decide) ch2147492616 fun o => ?_
    have hs : c3.get 2 = sp := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    have hv : c3.get 9 = c.get 9 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 5 ha) (Memory.block_access hm (off := 20) (by decide) (by decide))];rfl
  have s4 : DetStep B img ⟨c4,r3⟩ ⟨c5,r4⟩ := by
    refine detStep_of (by change (0x8000230a#32).getLsbD 0 = false;decide) ch2147492618 fun o => ?_
    have hs : c4.get 2 = sp := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    have hv : c4.get 18 = c.get 18 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 4 ha) (Memory.block_access hm (off := 16) (by decide) (by decide))];rfl
  have s5 : DetStep B img ⟨c5,r4⟩ ⟨c6,r5⟩ := by
    refine detStep_of (by change (0x8000230c#32).getLsbD 0 = false;decide) ch2147492620 fun o => ?_
    have hs : c5.get 2 = sp := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    have hv : c5.get 19 = c.get 19 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_store,hs,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 3 ha) (Memory.block_access hm (off := 12) (by decide) (by decide))];rfl
  refine ⟨c6,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.single s5))))),rfl,?_,?_,by rfl⟩
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · intro r hr
    simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hr]

theorem frame (ram : Word → BitVec 8) (sp : Word) (c : Core) (x : Word)
    (hx : ∀ i : Fin 32, x ≠ sp+BitVec.ofNat 32 i.val) : memory ram sp c x = ram x := by
  unfold memory
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hx ⟨12+i,by omega⟩)]
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hx ⟨16+i,by omega⟩)]
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hx ⟨20+i,by omega⟩)]
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hx ⟨24+i,by omega⟩)]
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hx ⟨28+i,by omega⟩)]

theorem saved (ram : Word → BitVec 8) (sp : Word) (c : Core) :
    ramRead (memory ram sp c) (sp+28#32) .w = c.get 1 ∧
    ramRead (memory ram sp c) (sp+24#32) .w = c.get 8 ∧
    ramRead (memory ram sp c) (sp+20#32) .w = c.get 9 ∧
    ramRead (memory ram sp c) (sp+16#32) .w = c.get 18 ∧
    ramRead (memory ram sp c) (sp+12#32) .w = c.get 19 := by
  refine ⟨?_ ,?_ ,?_ ,?_ ,?_ ⟩
  · unfold memory
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 28 12 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 28 16 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 28 20 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 28 24 (by decide) (by decide) (by decide) (by decide) (by decide))]
    exact ramRead_ramWrite_w _ _ _
  · unfold memory
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 24 12 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 24 16 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 24 20 (by decide) (by decide) (by decide) (by decide) (by decide))]
    exact ramRead_ramWrite_w _ _ _
  · unfold memory
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 20 12 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 20 16 (by decide) (by decide) (by decide) (by decide) (by decide))]
    exact ramRead_ramWrite_w _ _ _
  · unfold memory
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 16 12 (by decide) (by decide) (by decide) (by decide) (by decide))]
    exact ramRead_ramWrite_w _ _ _
  · unfold memory
    exact ramRead_ramWrite_w _ _ _
end E5R.Thermostat.CharSave
