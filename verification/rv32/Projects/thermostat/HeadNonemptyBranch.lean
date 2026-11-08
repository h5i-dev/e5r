import Projects.thermostat.HttpParseCode00
import Projects.thermostat.Quiet
namespace E5R.Thermostat.HeadNonemptyBranch
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (n : Word) (empty : Bool)
    (hp : c.pc=0x80002c88#32) (h14 : c.get 14=n) (ht : taken .eq n (0 : Word)=empty) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if empty then 0x80002ce6#32 else 0x80002c8a#32) ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  let d := c.goto (if empty then 0x80002ce6#32 else 0x80002c8a#32)
  have t : Quiet.Step B img ⟨c,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495048) fun o => ?_
    rw [exec_branch,h14,Core.get_zero,ht,hp]
    cases empty with
    | false => rfl
    | true =>
      simp only [ite_true]
      rw [show 0x80002c88#32+0x5e#32=0x80002ce6#32 by decide +kernel,jump_ok _ _ (by decide)]
      rfl
  exact ⟨d,.single t,rfl,fun _ => rfl,rfl⟩
end E5R.Thermostat.HeadNonemptyBranch
