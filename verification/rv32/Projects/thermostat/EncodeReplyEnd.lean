import Projects.thermostat.EncodeReplyCode
import Projects.thermostat.Memory
namespace E5R.Thermostat.EncodeReplyEnd
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp len ret : Word)
    (hp : c.pc = 0x80001f62#32) (hs : c.get 2 = sp) (h10 : c.get 10 = 0#32)
    (hm : Memory.Block B sp 96) (ha : sp.toNat%4=0)
    (hlen : ramRead ram (sp+16#32) .w = len) (hret : ramRead ram (sp+92#32) .w = ret) :
    ∃ d, DetSteps B img 5 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = ret &&& ~~~1 ∧ d.get 2 = sp+96#32 ∧
      d.get 1 = ret ∧ d.get 10 = 1#32 ∧ d.get 11 = len ∧
      (∀ r : Reg, r ≠ 1 → r ≠ 2 → r ≠ 10 → r ≠ 11 → d.get r = c.get r) ∧ d.sameCsr c := by
  let a := c.wr 11 len 0x80001f64#32
  let b := a.wr 10 1#32 0x80001f68#32
  let z := b.wr 1 ret 0x80001f6a#32
  let u := z.wr 2 (sp+96#32) 0x80001f6c#32
  let d := u.goto (ret &&& ~~~1)
  have t0 : DetStep B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact ej2147491682) fun o => ?_
    rw [exec_load,hs,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 4 ha) (Memory.block_access hm (off := 16) (by decide) (by decide)),hlen,hp];rfl
  have t1 : DetStep B img ⟨a,ram⟩ ⟨b,ram⟩ := by
    refine detStep_of (by change (0x80001f64#32).getLsbD 0 = false;decide) ej2147491684 fun o => ?_
    have a10 : a.get 10 = 0#32 := by simp [a,Core.wr_get_ne,h10]
    rw [exec_opimm,a10];rfl
  have t2 : DetStep B img ⟨b,ram⟩ ⟨z,ram⟩ := by
    refine detStep_of (by change (0x80001f68#32).getLsbD 0 = false;decide) ej2147491688 fun o => ?_
    have b2 : b.get 2 = sp := by simp [b,a,Core.wr_get_ne,hs]
    rw [exec_load,b2,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 23 ha) (Memory.block_access hm (off := 92) (by decide) (by decide)),hret];rfl
  have t3 : DetStep B img ⟨z,ram⟩ ⟨u,ram⟩ := by
    refine detStep_of (by change (0x80001f6a#32).getLsbD 0 = false;decide) ej2147491690 fun o => ?_
    have z2 : z.get 2 = sp := by simp [z,b,a,Core.wr_get_ne,hs]
    rw [exec_opimm,z2];rfl
  have t4 : DetStep B img ⟨u,ram⟩ ⟨d,ram⟩ := by
    refine detStep_of (by change (0x80001f6c#32).getLsbD 0 = false;decide) ej2147491692 fun o => ?_
    have u1 : u.get 1 = ret := by simp [u,z,Core.wr_get_ne,Core.wr_get]
    rw [exec_jalr,u1,BitVec.add_zero]
    change interp B img o (jump u (ret &&& ~~~1)) ram 0 [] = _
    rw [jump_ok _ _ (clear_bit0 _)];rfl
  refine ⟨d,.step t0 (.step t1 (.step t2 (.step t3 (.single t4)))),rfl,?_,?_,?_,?_,?_,by rfl⟩
  · simp [d,u,Core.wr_get]
  · simp [d,u,z,Core.wr_get_ne,Core.wr_get]
  · simp [d,u,z,b,Core.wr_get_ne,Core.wr_get]
  · simp [d,u,z,b,a,Core.wr_get_ne,Core.wr_get]
  · intro reg h1 h2 h10 h11
    simp [d,u,z,b,a,Core.wr_get_ne,h1,h2,h10,h11]
end E5R.Thermostat.EncodeReplyEnd
