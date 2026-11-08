import Projects.thermostat.EncodeErrorCode
import Projects.thermostat.Memory
namespace E5R.Thermostat.ErrorReturn
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp len status ret old8 old9 : Word)
    (hp : c.pc=0x80001e96#32) (hsp : c.get 2=sp) (h8 : c.get 8=len) (h9 : c.get 9=status)
    (hm : Memory.Block B sp 16) (ha : sp.toNat%4=0)
    (hr : ramRead ram (sp+12#32) .w=ret) (hs0 : ramRead ram (sp+8#32) .w=old8) (hs1 : ramRead ram (sp+4#32) .w=old9) :
    ∃ d, DetSteps B img 7 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=ret &&& ~~~1 ∧ d.get 2=sp+16#32 ∧
      d.get 10=status ∧ d.get 11=len ∧ d.get 1=ret ∧ d.get 8=old8 ∧ d.get 9=old9 ∧
      (∀ r : Reg, r≠10 → r≠11 → r≠1 → r≠8 → r≠9 → r≠2 → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.wr 10 status 0x80001e98#32
  let b := a.wr 11 len 0x80001e9a#32
  let z := b.wr 1 ret 0x80001e9c#32
  let u := z.wr 8 old8 0x80001e9e#32
  let v := u.wr 9 old9 0x80001ea0#32
  let q := v.wr 2 (sp+16#32) 0x80001ea2#32
  let d := q.goto (ret &&& ~~~1)
  have t0 : DetStep B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact ee2147491478) fun o => ?_
    rw [exec_op,Core.get_zero,h9,hp];simp only [alu,show (0:Word)=0#32 from rfl,BitVec.zero_add];rfl
  have t1 : DetStep B img ⟨a,ram⟩ ⟨b,ram⟩ := by
    refine detStep_of (by change (0x80001e98#32).getLsbD 0=false;decide) ee2147491480 fun o => ?_
    have a8 : a.get 8=len := (Core.wr_get_ne _ _ _ _ _ (by decide)).trans h8
    rw [exec_op,Core.get_zero,a8];simp only [alu,show (0:Word)=0#32 from rfl,BitVec.zero_add];rfl
  have t2 : DetStep B img ⟨b,ram⟩ ⟨z,ram⟩ := by
    refine detStep_of (by change (0x80001e9a#32).getLsbD 0=false;decide) ee2147491482 fun o => ?_
    have b2 : b.get 2=sp := by simp [b,a,Core.wr_get_ne,hsp]
    rw [exec_load,b2,interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 3 ha)
      (Memory.block_access hm (off := 12) (by decide) (by decide)),hr];rfl
  have t3 : DetStep B img ⟨z,ram⟩ ⟨u,ram⟩ := by
    refine detStep_of (by change (0x80001e9c#32).getLsbD 0=false;decide) ee2147491484 fun o => ?_
    have z2 : z.get 2=sp := by simp [z,b,a,Core.wr_get_ne,hsp]
    rw [exec_load,z2,interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 2 ha)
      (Memory.block_access hm (off := 8) (by decide) (by decide)),hs0];rfl
  have t4 : DetStep B img ⟨u,ram⟩ ⟨v,ram⟩ := by
    refine detStep_of (by change (0x80001e9e#32).getLsbD 0=false;decide) ee2147491486 fun o => ?_
    have u2 : u.get 2=sp := by simp [u,z,b,a,Core.wr_get_ne,hsp]
    rw [exec_load,u2,interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 1 ha)
      (Memory.block_access hm (off := 4) (by decide) (by decide)),hs1];rfl
  have t5 : DetStep B img ⟨v,ram⟩ ⟨q,ram⟩ := by
    refine detStep_of (by change (0x80001ea0#32).getLsbD 0=false;decide) ee2147491488 fun o => ?_
    have v2 : v.get 2=sp := by simp [v,u,z,b,a,Core.wr_get_ne,hsp]
    rw [exec_opimm,v2];rfl
  have t6 : DetStep B img ⟨q,ram⟩ ⟨d,ram⟩ := by
    refine detStep_of (by change (0x80001ea2#32).getLsbD 0=false;decide) ee2147491490 fun o => ?_
    have q1 : q.get 1=ret := by simp [q,v,u,z,Core.wr_get_ne,Core.wr_get]
    rw [exec_jalr,q1,BitVec.add_zero]
    change interp B img o (jump q (ret &&& ~~~1)) ram 0 [] = _
    rw [jump_ok _ _ (clear_bit0 _)];rfl
  refine ⟨d,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.single t6)))))),rfl,?_,?_,?_,?_,?_,?_,?_,by rfl⟩
  · simp [d,q,Core.wr_get]
  · simp [d,q,v,u,z,b,a,Core.wr_get_ne,Core.wr_get]
  · simp [d,q,v,u,z,b,Core.wr_get_ne,Core.wr_get]
  · simp [d,q,v,u,z,Core.wr_get_ne,Core.wr_get]
  · simp [d,q,v,u,Core.wr_get_ne,Core.wr_get]
  · simp [d,q,v,Core.wr_get_ne,Core.wr_get]
  · intro reg h10 h11 h1 h8 h9 h2
    simp [d,q,v,u,z,b,a,Core.wr_get_ne,h10,h11,h1,h8,h9,h2]
end E5R.Thermostat.ErrorReturn
