import Projects.thermostat.EncodeErrorCode
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ErrorSave
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp : Word) (c : Core) : Word → BitVec 8 :=
  ramWrite (ramWrite (ramWrite (ram) (sp+12#32) (c.get 1) .w) (sp+8#32) (c.get 8) .w) (sp+4#32) (c.get 9) .w

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word)
    (hp : c.pc = 0x80001e4a#32) (hs : c.get 2 = sp+16#32)
    (hm : Memory.Block B sp 16) (ha : sp.toNat%4 = 0) :
    ∃ d, DetSteps B img 4 ⟨c,ram⟩ ⟨d,memory ram sp c⟩ ∧ d.pc = 0x80001e52#32 ∧
      d.get 2 = sp ∧ (∀ r : Reg, r ≠ 2 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 2 sp 0x80001e4c#32
  let c2 := c1.goto 0x80001e4e#32
  let r1 := ramWrite ram (sp+12#32) (c.get 1) .w
  let c3 := c2.goto 0x80001e50#32
  let r2 := ramWrite r1 (sp+8#32) (c.get 8) .w
  let c4 := c3.goto 0x80001e52#32
  let r3 := ramWrite r2 (sp+4#32) (c.get 9) .w
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact ee2147491402) fun o => ?_
    rw [exec_opimm,hs,hp]
    change interp B img o (.done (c.wr 2 ((sp+16#32)+0xfffffff0#32) 0x80001e4c#32)) ram 0 [] = _
    rw [BitVec.add_assoc,show 16#32+0xfffffff0#32 = 0#32 by decide +kernel,BitVec.add_zero];rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,r1⟩ := by
    refine detStep_of (by change (0x80001e4c#32).getLsbD 0 = false;decide) ee2147491404 fun o => ?_
    have hsp : c1.get 2 = sp := by simp [c1,Core.wr_get_ne,Core.wr_get]
    have hv : c1.get 1 = c.get 1 := by simp [c1,Core.wr_get_ne]
    rw [exec_store,hsp,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 3 ha) (Memory.block_access hm (off := 12) (by decide) (by decide))];rfl
  have s2 : DetStep B img ⟨c2,r1⟩ ⟨c3,r2⟩ := by
    refine detStep_of (by change (0x80001e4e#32).getLsbD 0 = false;decide) ee2147491406 fun o => ?_
    have hsp : c2.get 2 = sp := by simp [c2,c1,Core.wr_get_ne,Core.wr_get]
    have hv : c2.get 8 = c.get 8 := by simp [c2,c1,Core.wr_get_ne]
    rw [exec_store,hsp,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 2 ha) (Memory.block_access hm (off := 8) (by decide) (by decide))];rfl
  have s3 : DetStep B img ⟨c3,r2⟩ ⟨c4,r3⟩ := by
    refine detStep_of (by change (0x80001e50#32).getLsbD 0 = false;decide) ee2147491408 fun o => ?_
    have hsp : c3.get 2 = sp := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    have hv : c3.get 9 = c.get 9 := by simp [c3,c2,c1,Core.wr_get_ne]
    rw [exec_store,hsp,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 1 ha) (Memory.block_access hm (off := 4) (by decide) (by decide))];rfl
  refine ⟨c4,.step s0 (.step s1 (.step s2 (.single s3))),rfl,?_,?_,by rfl⟩
  · simp [c4,c3,c2,c1,Core.wr_get]
  · intro r hr
    simp [c4,c3,c2,c1,Core.wr_get_ne,hr]

theorem frame (ram : Word → BitVec 8) (sp : Word) (c : Core) (x : Word)
    (hx : ∀ i : Fin 16, x ≠ sp+BitVec.ofNat 32 i.val) : memory ram sp c x = ram x := by
  unfold memory
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hx ⟨4+i,by omega⟩)]
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hx ⟨8+i,by omega⟩)]
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hx ⟨12+i,by omega⟩)]

theorem saved (ram : Word → BitVec 8) (sp : Word) (c : Core) :
    ramRead (memory ram sp c) (sp+12#32) .w = c.get 1 ∧
    ramRead (memory ram sp c) (sp+8#32) .w = c.get 8 ∧
    ramRead (memory ram sp c) (sp+4#32) .w = c.get 9 := by
  refine ⟨?_ ,?_ ,?_ ⟩
  · unfold memory
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 12 4 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 12 8 (by decide) (by decide) (by decide) (by decide) (by decide))]
    exact ramRead_ramWrite_w _ _ _
  · unfold memory
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 8 4 (by decide) (by decide) (by decide) (by decide) (by decide))]
    exact ramRead_ramWrite_w _ _ _
  · unfold memory
    exact ramRead_ramWrite_w _ _ _
end E5R.Thermostat.ErrorSave
