-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.CopyUnalignedScratch
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
open E5R E5R.Thermostat
namespace E5R.Thermostat.CopyUnalignedScratch
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (offset : Nat)
    (hp : c.pc=0x800051ca#32) (hsp : c.get 2=sp) (h5 : c.get 5=BitVec.ofNat 32 offset)
    (hm : Memory.Block B sp 16) (ha : sp.toNat%4=0) (ho : offset<4) :
    ∃ d, Quiet.Steps B img 7 ⟨c,ram⟩ ⟨d,memory ram sp⟩ ∧ d.pc=0x800051e0#32 ∧
      d.get 16=0#32 ∧ d.get 17=4#32-BitVec.ofNat 32 offset ∧ d.get 6=sp+BitVec.ofNat 32 (12+offset) ∧
      d.get 7=(4#32-BitVec.ofNat 32 offset) &&& 1#32 ∧
      (∀ r : Reg, r≠16 → r≠17 → r≠6 → r≠7 → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.wr 16 0#32 0x800051cc#32
  let b := a.wr 17 4#32 0x800051ce#32
  let z := b.wr 17 (4#32-BitVec.ofNat 32 offset) 0x800051d2#32
  let u := z.wr 6 (sp+12#32) 0x800051d6#32
  let v := u.wr 7 ((4#32-BitVec.ofNat 32 offset) &&& 1#32) 0x800051da#32
  let q := v.goto 0x800051dc#32
  let d := q.wr 6 (sp+BitVec.ofNat 32 (12+offset)) 0x800051e0#32
  let r := memory ram sp
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact cp2147504586) fun o => ?_
    rw [exec_opimm,Core.get_zero,hp];rfl
  have t1 : Quiet.Step B img ⟨a,ram⟩ ⟨b,ram⟩ := by
    refine QuietDet.step_of (by change (0x800051cc#32).getLsbD 0=false;decide) cp2147504588 fun o => ?_
    rw [exec_opimm,Core.get_zero];rfl
  have t2 : Quiet.Step B img ⟨b,ram⟩ ⟨z,ram⟩ := by
    refine QuietDet.step_of (by change (0x800051ce#32).getLsbD 0=false;decide) cp2147504590 fun o => ?_
    have b17 : b.get 17=4#32 := by simp [b,Core.wr_get]
    have b5 : b.get 5=BitVec.ofNat 32 offset := by simp [b,a,Core.wr_get_ne,h5]
    rw [exec_op,b17,b5];rfl
  have t3 : Quiet.Step B img ⟨z,ram⟩ ⟨u,ram⟩ := by
    refine QuietDet.step_of (by change (0x800051d2#32).getLsbD 0=false;decide) cp2147504594 fun o => ?_
    have z2 : z.get 2=sp := by simp [z,b,a,Core.wr_get_ne,hsp]
    rw [exec_opimm,z2];rfl
  have t4 : Quiet.Step B img ⟨u,ram⟩ ⟨v,ram⟩ := by
    refine QuietDet.step_of (by change (0x800051d6#32).getLsbD 0=false;decide) cp2147504598 fun o => ?_
    have u17 : u.get 17=4#32-BitVec.ofNat 32 offset := by simp [u,z,Core.wr_get_ne,Core.wr_get]
    rw [exec_opimm,u17];rfl
  have t5 : Quiet.Step B img ⟨v,ram⟩ ⟨q,r⟩ := by
    refine QuietDet.step_of (by change (0x800051da#32).getLsbD 0=false;decide) cp2147504602 fun o => ?_
    have v2 : v.get 2=sp := by simp [v,u,z,b,a,Core.wr_get_ne,hsp]
    rw [exec_store,v2,Core.get_zero,interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned sp 3 ha) (Memory.block_access hm (off := 12) (by decide) (by decide))];rfl
  have t6 : Quiet.Step B img ⟨q,r⟩ ⟨d,r⟩ := by
    refine QuietDet.step_of (by change (0x800051dc#32).getLsbD 0=false;decide) cp2147504604 fun o => ?_
    have q6 : q.get 6=sp+12#32 := by simp [q,v,u,Core.wr_get_ne,Core.wr_get]
    have q5 : q.get 5=BitVec.ofNat 32 offset := by simp [q,v,u,z,b,a,Core.wr_get_ne,h5]
    have hn : (sp+12#32).toNat+offset<2^32 := by
      rw [WordZero.add_nat sp 12 (by have := hm.2.2;omega)]
      have := hm.2.2;omega
    have he : (sp+12#32) ||| BitVec.ofNat 32 offset=sp+BitVec.ofNat 32 (12+offset) := by
      rw [CopyBits.or_low (sp+12#32) offset (Memory.word_aligned sp 3 ha) ho hn,BitVec.add_assoc,←BitVec.ofNat_add]
    rw [exec_op,q6,q5]
    change interp B img o (.done (q.wr 6 ((sp+12#32) ||| BitVec.ofNat 32 offset) 0x800051e0#32)) r 0 [] = _
    rw [he];rfl
  refine ⟨d,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.single t6)))))),rfl,?_,?_,?_,?_,?_,by rfl⟩
  · simp [d,q,v,u,z,b,a,Core.wr_get_ne,Core.wr_get]
  · simp [d,q,v,u,z,Core.wr_get_ne,Core.wr_get]
  · simp [d,Core.wr_get]
  · simp [d,q,v,Core.wr_get_ne,Core.wr_get]
  · intro reg h16 h17 h6 h7
    simp [d,q,v,u,z,b,a,Core.wr_get_ne,h16,h17,h6,h7]

end E5R.Thermostat.CopyUnalignedScratch
