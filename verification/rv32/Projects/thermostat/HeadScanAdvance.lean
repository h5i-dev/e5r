import Projects.thermostat.HttpParseCode00
import Projects.thermostat.Quiet
namespace E5R.Thermostat.HeadScanAdvance
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (index n : Word) (again : Bool)
    (hp : c.pc=0x80002ca0#32) (h9 : c.get 9=index) (h14 : c.get 14=n)
    (ht : taken .ne n (index+1#32)=again) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if again then 0x80002c90#32 else 0x80002ca6#32) ∧ d.get 9=index+1#32 ∧
      (∀ r : Reg, r≠9 → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.wr 9 (index+1#32) 0x80002ca2#32
  let d := a.goto (if again then 0x80002c90#32 else 0x80002ca6#32)
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495072) fun o => ?_
    rw [exec_opimm,h9,hp]
    rfl
  have t1 : Quiet.Step B img ⟨a,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of (by change (0x80002ca2#32).getLsbD 0=false;decide) hh2147495074 fun o => ?_
    have v14 : a.get 14=n := by simp [a,Core.wr_get_ne,h14]
    have v9 : a.get 9=index+1#32 := by simp [a,Core.wr_get]
    rw [exec_branch,v14,v9,ht]
    cases again with
    | false => rfl
    | true =>
      simp only [ite_true]
      change Observed.interp B img o (jump a (0x80002ca2#32+0xffffffee#32)) ram 0 [] []=_
      rw [show 0x80002ca2#32+0xffffffee#32=0x80002c90#32 by decide +kernel,jump_ok _ _ (by decide)]
      rfl
  exact ⟨d,.step t0 (.single t1),rfl,by simp [d,a,Core.wr_get],fun r hr => by simp [d,a,Core.wr_get_ne,hr],rfl⟩

theorem finish (B : Board) (c : Core) (ram : Word → BitVec 8) (hp : c.pc=0x80002ca6#32) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80002ce6#32 ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  let d := c.goto 0x80002ce6#32
  have t : Quiet.Step B img ⟨c,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495078) fun o => ?_
    rw [exec_jal,Core.set_zero,hp]
    rw [show 0x80002ca6#32+0x40#32=0x80002ce6#32 by decide +kernel,jump_ok _ _ (by decide)]
    rfl
  exact ⟨d,.single t,rfl,fun _ => rfl,rfl⟩
end E5R.Thermostat.HeadScanAdvance
