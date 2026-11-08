import Projects.thermostat.HttpParseCode00
import Projects.thermostat.Quiet
namespace E5R.Thermostat.HeadCRGuard
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (index n : Word) (full : Bool)
    (hp : c.pc=0x80002ca8#32) (h9 : c.get 9=index) (h14 : c.get 14=n)
    (ht : taken .geu (index+1#32) n=full) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if full then 0x80002ce6#32 else 0x80002cb0#32) ∧ d.get 15=index+1#32 ∧
      (∀ r : Reg, r≠15 → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.wr 15 (index+1#32) 0x80002cac#32
  let d := a.goto (if full then 0x80002ce6#32 else 0x80002cb0#32)
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495080) fun o => ?_
    rw [exec_opimm,h9,hp]
    rfl
  have t1 : Quiet.Step B img ⟨a,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of (by change (0x80002cac#32).getLsbD 0=false;decide) hh2147495084 fun o => ?_
    have v14 : a.get 14=n := by simp [a,Core.wr_get_ne,h14]
    have v15 : a.get 15=index+1#32 := by simp [a,Core.wr_get]
    rw [exec_branch,v15,v14,ht]
    cases full with
    | false => rfl
    | true =>
      simp only [ite_true]
      change Observed.interp B img o (jump a (0x80002cac#32+0x3a#32)) ram 0 [] []=_
      rw [show 0x80002cac#32+0x3a#32=0x80002ce6#32 by decide +kernel,jump_ok _ _ (by decide)]
      rfl
  exact ⟨d,.step t0 (.single t1),rfl,by simp [d,a,Core.wr_get],fun r hr => by simp [d,a,Core.wr_get_ne,hr],rfl⟩
end E5R.Thermostat.HeadCRGuard
