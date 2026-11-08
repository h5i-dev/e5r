-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.UnalignedCopyTurn
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
open E5R E5R.Thermostat
namespace E5R.Thermostat.UnalignedCopyTurn
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (src dst finish previous next shift comp : Word) (again : Bool)
    (hp : c.pc=0x8000525e#32) (h6 : c.get 6=src) (h7 : c.get 7=comp) (h13 : c.get 13=finish)
    (h14 : c.get 14=dst) (h16 : c.get 16=shift) (h17 : c.get 17=previous)
    (has : (src+4#32).toNat%4=0) (had : dst.toNat%4=0) (ho : B.inRam (src+4#32) 4=false)
    (hv : romRead? img (src+4#32).toNat 4 false=some next) (hd : B.inRam dst 4=true)
    (ht : taken .ltu (dst+8#32) finish=again) :
    ∃ d, Quiet.Steps B img 10 ⟨c,ram⟩ ⟨d,ramWrite ram dst (mix previous next shift comp) .w⟩ ∧
      d.pc=(if again then 0x8000525e#32 else 0x80005280#32) ∧ d.get 6=src+4#32 ∧ d.get 14=dst+4#32 ∧ d.get 17=next ∧
      (∀ r : Reg, r≠6 → r≠14 → r≠17 → r≠28 → r≠29 → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.wr 28 previous 0x80005260#32
  let b := a.wr 17 next 0x80005264#32
  let z := b.wr 28 (alu .srl previous shift) 0x80005268#32
  let u := z.wr 6 (src+4#32) 0x8000526a#32
  let v := u.wr 29 (alu .sll next comp) 0x8000526e#32
  let q := v.wr 28 (mix previous next shift comp) 0x80005272#32
  let j := q.wr 29 (dst+8#32) 0x80005276#32
  let k := j.goto 0x8000527a#32
  let r := ramWrite ram dst (mix previous next shift comp) .w
  let l := k.wr 14 (dst+4#32) 0x8000527c#32
  let d := l.goto (if again then 0x8000525e#32 else 0x80005280#32)
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact cp2147504734) fun o => ?_
    rw [exec_op,Core.get_zero,h17,hp];simp only [alu,show (0:Word)=0#32 from rfl,BitVec.zero_add];rfl
  have t1 : Quiet.Step B img ⟨a,ram⟩ ⟨b,ram⟩ := by
    refine QuietDet.step_of (by change (0x80005260#32).getLsbD 0=false;decide) cp2147504736 fun o => ?_
    have a6 : a.get 6=src := (Core.wr_get_ne _ _ _ _ _ (by decide)).trans h6
    rw [exec_load,a6,interp_load_rom (B := B) (img := img) (w := .w) o has ho rfl hv];rfl
  have t2 : Quiet.Step B img ⟨b,ram⟩ ⟨z,ram⟩ := by
    refine QuietDet.step_of (by change (0x80005264#32).getLsbD 0=false;decide) cp2147504740 fun o => ?_
    have b28 : b.get 28=previous := by simp [b,a,Core.wr_get_ne,Core.wr_get]
    have b16 : b.get 16=shift := by simp [b,a,Core.wr_get_ne,h16]
    rw [exec_op,b28,b16];rfl
  have t3 : Quiet.Step B img ⟨z,ram⟩ ⟨u,ram⟩ := by
    refine QuietDet.step_of (by change (0x80005268#32).getLsbD 0=false;decide) cp2147504744 fun o => ?_
    have z6 : z.get 6=src := by simp [z,b,a,Core.wr_get_ne,h6]
    rw [exec_opimm,z6];rfl
  have t4 : Quiet.Step B img ⟨u,ram⟩ ⟨v,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000526a#32).getLsbD 0=false;decide) cp2147504746 fun o => ?_
    have u17 : u.get 17=next := by simp [u,z,b,Core.wr_get_ne,Core.wr_get]
    have u7 : u.get 7=comp := by simp [u,z,b,a,Core.wr_get_ne,h7]
    rw [exec_op,u17,u7];rfl
  have t5 : Quiet.Step B img ⟨v,ram⟩ ⟨q,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000526e#32).getLsbD 0=false;decide) cp2147504750 fun o => ?_
    have v29 : v.get 29=alu .sll next comp := by simp [v,Core.wr_get]
    have v28 : v.get 28=alu .srl previous shift := by simp [v,u,z,Core.wr_get_ne,Core.wr_get]
    rw [exec_op,v29,v28];rfl
  have t6 : Quiet.Step B img ⟨q,ram⟩ ⟨j,ram⟩ := by
    refine QuietDet.step_of (by change (0x80005272#32).getLsbD 0=false;decide) cp2147504754 fun o => ?_
    have q14 : q.get 14=dst := by simp [q,v,u,z,b,a,Core.wr_get_ne,h14]
    rw [exec_opimm,q14];rfl
  have t7 : Quiet.Step B img ⟨j,ram⟩ ⟨k,r⟩ := by
    refine QuietDet.step_of (by change (0x80005276#32).getLsbD 0=false;decide) cp2147504758 fun o => ?_
    have j14 : j.get 14=dst := by simp [j,q,v,u,z,b,a,Core.wr_get_ne,h14]
    have j28 : j.get 28=mix previous next shift comp := by simp [j,q,Core.wr_get_ne,Core.wr_get]
    rw [exec_store,j14,j28,BitVec.add_zero,interp_store_ram (B := B) (img := img) (w := .w) o had hd];rfl
  have t8 : Quiet.Step B img ⟨k,r⟩ ⟨l,r⟩ := by
    refine QuietDet.step_of (by change (0x8000527a#32).getLsbD 0=false;decide) cp2147504762 fun o => ?_
    have k14 : k.get 14=dst := by simp [k,j,q,v,u,z,b,a,Core.wr_get_ne,h14]
    rw [exec_opimm,k14];rfl
  have t9 : Quiet.Step B img ⟨l,r⟩ ⟨d,r⟩ := by
    refine QuietDet.step_of (by change (0x8000527c#32).getLsbD 0=false;decide) cp2147504764 fun o => ?_
    have l29 : l.get 29=dst+8#32 := by simp [l,k,j,Core.wr_get_ne,Core.wr_get]
    have l13 : l.get 13=finish := by simp [l,k,j,q,v,u,z,b,a,Core.wr_get_ne,h13]
    rw [exec_branch,l29,l13,ht]
    cases again with
    | false => rfl
    | true =>
      simp only [ite_true]
      change interp B img o (jump l (0x8000527c#32+0xffffffe2#32)) r 0 [] = _
      rw [show (0x8000527c#32+0xffffffe2#32)=0x8000525e#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  refine ⟨d,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.single t9))))))))),rfl,?_,?_,?_,?_,by rfl⟩
  · simp [d,l,k,j,q,v,u,Core.wr_get_ne,Core.wr_get]
  · simp [d,l,Core.wr_get]
  · simp [d,l,k,j,q,v,u,z,b,Core.wr_get_ne,Core.wr_get]
  · intro reg h6 h14 h17 h28 h29
    simp [d,l,k,j,q,v,u,z,b,a,Core.wr_get_ne,h6,h14,h17,h28,h29]

end E5R.Thermostat.UnalignedCopyTurn
