import Projects.thermostat.HttpParseCode00
import Projects.thermostat.Quiet
namespace E5R.Thermostat.HeadMin
open E5R E5R.Thermostat

theorem branch (B : Board) (c : Core) (ram : Word → BitVec 8) (length : Word) (short : Bool)
    (hp : c.pc=0x80002c82#32) (h12 : c.get 12=length) (h16 : c.get 16=1024#32)
    (ht : taken .ltu length 1024#32=short) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if short then 0x80002c88#32 else 0x80002c86#32) ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  let d := c.goto (if short then 0x80002c88#32 else 0x80002c86#32)
  have t : Quiet.Step B img ⟨c,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495042) fun o => ?_
    rw [exec_branch,h12,h16,ht,hp]
    cases short with
    | false => rfl
    | true =>
      simp only [ite_true]
      rw [show 0x80002c82#32+6#32=0x80002c88#32 by decide +kernel,jump_ok _ _ (by decide)]
      rfl
  exact ⟨d,.single t,rfl,fun _ => rfl,rfl⟩

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (length : Word) (short : Bool)
    (hp : c.pc=0x80002c82#32) (h12 : c.get 12=length) (h14 : c.get 14=length) (h16 : c.get 16=1024#32)
    (ht : taken .ltu length 1024#32=short) :
    ∃ n d, 1≤n ∧ n≤2 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=0x80002c88#32 ∧ d.get 14=(if short then length else 1024#32) ∧
      (∀ r : Reg, r≠14 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,first,pc,frame,csr⟩ := branch B c ram length short hp h12 h16 ht
  cases short with
  | true => exact ⟨1,a,by decide,by decide,first,pc,(frame 14).trans h14,fun r _ => frame r,csr⟩
  | false =>
    let d := a.wr 14 1024#32 0x80002c88#32
    have t : Quiet.Step B img ⟨a,ram⟩ ⟨d,ram⟩ := by
      refine Quiet.step_of (by rw [pc];decide) (by rw [pc];exact hh2147495046) fun o => ?_
      rw [exec_op,Core.get_zero,(frame 16).trans h16,show alu .add (0 : Word) 1024#32=1024#32 by decide +kernel,pc]
      rfl
    exact ⟨2,d,by decide,by decide,first.trans (.single t),rfl,by simp [d,Core.wr_get],
      fun r hr => (Core.wr_get_ne _ _ _ _ _ hr).trans (frame r),by exact csr⟩
end E5R.Thermostat.HeadMin
