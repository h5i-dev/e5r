import Projects.thermostat.FormatEngineCode
import Projects.thermostat.Memory
import Projects.thermostat.ViewFrame
namespace E5R.Thermostat.FormatArgumentCall
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp obj : Word) :=
  ramWrite (ramWrite (ramWrite (ramWrite ram sp obj .w) (sp+4#32) 0x80005c04#32 .w)
    (sp+8#32) 0x60000020#32 .w) (sp+12#32) 0#32 .w

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp obj method : Word)
    (hp : c.pc = 0x800049cc#32) (hs : c.get 2 = sp) (h19 : c.get 19 = obj)
    (h18 : c.get 18 = 0x80005c04#32) (h26 : c.get 26 = 0x60000020#32) (h12 : c.get 12 = method)
    (hm : Memory.Block B sp 16) (ha : sp.toNat%4 = 0) :
    ∃ d, DetSteps B img 6 ⟨c,ram⟩ ⟨d,memory ram sp obj⟩ ∧ d.pc = method &&& ~~~1 ∧
      d.get 1 = 0x800049d8#32 ∧ d.get 11 = sp ∧
      (∀ r : Reg, r ≠ 1 → r ≠ 11 → d.get r = c.get r) ∧ d.sameCsr c := by
  let r1 := ramWrite ram sp obj .w
  let a := c.goto 0x800049ce#32
  let r2 := ramWrite r1 (sp+4#32) 0x80005c04#32 .w
  let b := a.goto 0x800049d0#32
  let r3 := ramWrite r2 (sp+8#32) 0x60000020#32 .w
  let u := b.goto 0x800049d2#32
  let r4 := ramWrite r3 (sp+12#32) 0#32 .w
  let w := u.goto 0x800049d4#32
  let y := w.wr 11 sp 0x800049d6#32
  let d := (y.set 1 0x800049d8#32).goto (method &&& ~~~1)
  have s0 : DetStep B img ⟨c,ram⟩ ⟨a,r1⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact fe2147502540) fun o => ?_
    rw [exec_store,hs,h19,BitVec.add_zero,interp_store_ram (B := B) (img := img) (w := .w) o ha
      (by simpa only [BitVec.add_zero] using Memory.block_access hm (off := 0) (by decide) (by decide)),hp];rfl
  have s1 : DetStep B img ⟨a,r1⟩ ⟨b,r2⟩ := by
    refine detStep_of (by change (0x800049ce#32).getLsbD 0 = false;decide) fe2147502542 fun o => ?_
    have hsp : a.get 2 = sp := hs
    have hv : a.get 18 = 0x80005c04#32 := h18
    rw [exec_store,hsp,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 1 ha) (Memory.block_access hm (off := 4) (by decide) (by decide))];rfl
  have s2 : DetStep B img ⟨b,r2⟩ ⟨u,r3⟩ := by
    refine detStep_of (by change (0x800049d0#32).getLsbD 0 = false;decide) fe2147502544 fun o => ?_
    have hsp : b.get 2 = sp := hs
    have hv : b.get 26 = 0x60000020#32 := h26
    rw [exec_store,hsp,hv,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 2 ha) (Memory.block_access hm (off := 8) (by decide) (by decide))];rfl
  have s3 : DetStep B img ⟨u,r3⟩ ⟨w,r4⟩ := by
    refine detStep_of (by change (0x800049d2#32).getLsbD 0 = false;decide) fe2147502546 fun o => ?_
    have hsp : u.get 2 = sp := hs
    rw [exec_store,hsp,Core.get_zero,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 3 ha) (Memory.block_access hm (off := 12) (by decide) (by decide))];rfl
  have s4 : DetStep B img ⟨w,r4⟩ ⟨y,r4⟩ := by
    refine detStep_of (by change (0x800049d4#32).getLsbD 0 = false;decide) fe2147502548 fun o => ?_
    have hsp : w.get 2 = sp := hs
    rw [exec_op,Core.get_zero,hsp]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];rfl
  have s5 : DetStep B img ⟨y,r4⟩ ⟨d,r4⟩ := by
    refine detStep_of (by change (0x800049d6#32).getLsbD 0 = false;decide) fe2147502550 fun o => ?_
    have hv : y.get 12 = method := by simp [y,w,u,b,a,Core.wr_get_ne,h12]
    rw [exec_jalr,hv,BitVec.add_zero]
    change interp B img o (jump (y.set 1 0x800049d8#32) (method &&& ~~~1)) r4 0 [] = _
    rw [jump_ok _ _ (clear_bit0 _)];rfl
  refine ⟨d,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.single s5))))),rfl,?_,?_,?_,by rfl⟩
  · simp [d,Core.get_set]
  · simp [d,y,Core.get_set,Core.wr_get]
  · intro r h1 h11
    simp [d,y,w,u,b,a,Core.get_set,Core.wr_get_ne,h1,h11]
end E5R.Thermostat.FormatArgumentCall
