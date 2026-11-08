import Projects.thermostat.EncodeReplyCode
import Projects.thermostat.Memory
namespace E5R.Thermostat.EncodeReplyStart
open E5R E5R.Thermostat

def saved (ram : Word → BitVec 8) (sp : Word) (c : Core) := ramWrite ram (sp+92#32) (c.get 1) .w

def memory (ram : Word → BitVec 8) (sp dst cap : Word) (c : Core) :=
  ramWrite (ramWrite (ramWrite (saved ram sp c) (sp+8#32) dst .w) (sp+12#32) cap .w) (sp+16#32) 0#32 .w

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp reply dst cap mode : Word)
    (hp : c.pc = 0x80001eb8#32) (hs : c.get 2 = sp+96#32)
    (h10 : c.get 10 = reply) (h11 : c.get 11 = dst) (h12 : c.get 12 = cap)
    (hm : Memory.Block B sp 96) (ha : sp.toNat%4 = 0) (hr : Memory.Block B reply 10)
    (hmode : extend .b false (ramRead (saved ram sp c) (reply+9#32) .b) = mode) :
    ∃ d, DetSteps B img 6 ⟨c,ram⟩ ⟨d,memory ram sp dst cap c⟩ ∧ d.pc = 0x80001ec6#32 ∧
      d.get 2 = sp ∧ d.get 13 = mode ∧
      (∀ r : Reg, r ≠ 2 → r ≠ 13 → d.get r = c.get r) ∧ d.sameCsr c := by
  let a := c.wr 2 sp 0x80001eba#32
  let b := a.goto 0x80001ebc#32
  let r1 := saved ram sp c
  let z := b.wr 13 mode 0x80001ec0#32
  let u := z.goto 0x80001ec2#32
  let r2 := ramWrite r1 (sp+8#32) dst .w
  let v := u.goto 0x80001ec4#32
  let r3 := ramWrite r2 (sp+12#32) cap .w
  let d := v.goto 0x80001ec6#32
  have t0 : DetStep B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact ej2147491512) fun o => ?_
    rw [exec_opimm,hs,hp]
    change interp B img o (.done (c.wr 2 ((sp+96#32)+0xffffffa0#32) 0x80001eba#32)) ram 0 [] = _
    rw [BitVec.add_assoc,show 96#32+0xffffffa0#32 = 0#32 by decide +kernel,BitVec.add_zero];rfl
  have t1 : DetStep B img ⟨a,ram⟩ ⟨b,r1⟩ := by
    refine detStep_of (by change (0x80001eba#32).getLsbD 0 = false;decide) ej2147491514 fun o => ?_
    have a2 : a.get 2 = sp := by simp [a,Core.wr_get]
    have a1 : a.get 1 = c.get 1 := by simp [a,Core.wr_get_ne]
    rw [exec_store,a2,a1,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 23 ha) (Memory.block_access hm (off := 92) (by decide) (by decide))];rfl
  have t2 : DetStep B img ⟨b,r1⟩ ⟨z,r1⟩ := by
    refine detStep_of (by change (0x80001ebc#32).getLsbD 0 = false;decide) ej2147491516 fun o => ?_
    have b10 : b.get 10 = reply := by simp [b,a,Core.wr_get_ne,h10]
    rw [exec_load,b10,interp_load_ram (B := B) (img := img) (w := .b) o (by change (reply+9#32).toNat%1=0;omega)
      (Memory.block_access hr (off := 9) (by decide) (by decide)),hmode];rfl
  have t3 : DetStep B img ⟨z,r1⟩ ⟨u,r2⟩ := by
    refine detStep_of (by change (0x80001ec0#32).getLsbD 0 = false;decide) ej2147491520 fun o => ?_
    have z2 : z.get 2 = sp := by simp [z,b,a,Core.wr_get_ne,Core.wr_get]
    have z11 : z.get 11 = dst := by simp [z,b,a,Core.wr_get_ne,h11]
    rw [exec_store,z2,z11,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 2 ha) (Memory.block_access hm (off := 8) (by decide) (by decide))];rfl
  have t4 : DetStep B img ⟨u,r2⟩ ⟨v,r3⟩ := by
    refine detStep_of (by change (0x80001ec2#32).getLsbD 0 = false;decide) ej2147491522 fun o => ?_
    have u2 : u.get 2 = sp := by simp [u,z,b,a,Core.wr_get_ne,Core.wr_get]
    have u12 : u.get 12 = cap := by simp [u,z,b,a,Core.wr_get_ne,h12]
    rw [exec_store,u2,u12,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 3 ha) (Memory.block_access hm (off := 12) (by decide) (by decide))];rfl
  have t5 : DetStep B img ⟨v,r3⟩ ⟨d,memory ram sp dst cap c⟩ := by
    refine detStep_of (by change (0x80001ec4#32).getLsbD 0 = false;decide) ej2147491524 fun o => ?_
    have v2 : v.get 2 = sp := by simp [v,u,z,b,a,Core.wr_get_ne,Core.wr_get]
    rw [exec_store,v2,Core.get_zero,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 4 ha) (Memory.block_access hm (off := 16) (by decide) (by decide))];rfl
  refine ⟨d,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.single t5))))),rfl,?_,?_,?_,by rfl⟩
  · simp [d,v,u,z,b,a,Core.wr_get_ne,Core.wr_get]
  · simp [d,v,u,z,Core.wr_get]
  · intro reg h2 h13
    simp [d,v,u,z,b,a,Core.wr_get_ne,h2,h13]
end E5R.Thermostat.EncodeReplyStart
