import Projects.thermostat.I16Code
import Projects.thermostat.Memory
namespace E5R.Thermostat.I16Save
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp : Word) (c : Core) :=
  ramWrite (ramWrite ram (sp+12#32) (c.get 1) .w) (sp+8#32) (c.get 8) .w

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word)
    (hp : c.pc = 0x80004e5e#32) (hs : c.get 2 = sp+16#32)
    (hm : Memory.Block B sp 16) (ha : sp.toNat%4 = 0) :
    ∃ d, DetSteps B img 3 ⟨c,ram⟩ ⟨d,memory ram sp c⟩ ∧ d.pc = 0x80004e64#32 ∧
      d.get 2 = sp ∧ (∀ r : Reg, r ≠ 2 → d.get r = c.get r) ∧ d.sameCsr c := by
  let a := c.wr 2 sp 0x80004e60#32
  let r0 := ramWrite ram (sp+12#32) (c.get 1) .w
  let b := a.goto 0x80004e62#32
  let d := b.goto 0x80004e64#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact di2147503710) fun o => ?_
    rw [exec_opimm,hs,hp]
    change interp B img o (.done (c.wr 2 ((sp+16#32)+0xfffffff0#32) 0x80004e60#32)) ram 0 [] = _
    rw [BitVec.add_assoc,show 16#32+0xfffffff0#32 = 0#32 by decide +kernel,BitVec.add_zero];rfl
  have s1 : DetStep B img ⟨a,ram⟩ ⟨b,r0⟩ := by
    refine detStep_of (by change (0x80004e60#32).getLsbD 0 = false;decide) di2147503712 fun o => ?_
    have hs0 : a.get 2 = sp := by simp [a,Core.wr_get]
    have hv : a.get 1 = c.get 1 := by simp [a,Core.wr_get_ne]
    rw [exec_store,hs0,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 3 ha) (Memory.block_access hm (off := 12) (by decide) (by decide))];rfl
  have s2 : DetStep B img ⟨b,r0⟩ ⟨d,memory ram sp c⟩ := by
    refine detStep_of (by change (0x80004e62#32).getLsbD 0 = false;decide) di2147503714 fun o => ?_
    have hs0 : b.get 2 = sp := by simp [b,a,Core.wr_get]
    have hv : b.get 8 = c.get 8 := by simp [b,a,Core.wr_get_ne]
    rw [exec_store,hs0,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 2 ha) (Memory.block_access hm (off := 8) (by decide) (by decide))];rfl
  refine ⟨d,.step s0 (.step s1 (.single s2)),rfl,?_,?_,by rfl⟩
  · simp [d,b,a,Core.wr_get]
  · intro r hr;simp [d,b,a,Core.wr_get_ne,hr]

theorem frame (ram : Word → BitVec 8) (sp : Word) (c : Core) (x : Word)
    (hx : ∀ i : Fin 16, x ≠ sp+BitVec.ofNat 32 i.val) : memory ram sp c x = ram x := by
  unfold memory
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hx ⟨8+i,by omega⟩)]
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hx ⟨12+i,by omega⟩)]

theorem saved (ram : Word → BitVec 8) (sp : Word) (c : Core) :
    ramRead (memory ram sp c) (sp+12#32) .w = c.get 1 ∧ ramRead (memory ram sp c) (sp+8#32) .w = c.get 8 := by
  constructor
  · unfold memory
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 12 8 (by decide) (by decide) (by decide) (by decide) (by decide))]
    exact ramRead_ramWrite_w _ _ _
  · exact ramRead_ramWrite_w _ _ _
end E5R.Thermostat.I16Save
