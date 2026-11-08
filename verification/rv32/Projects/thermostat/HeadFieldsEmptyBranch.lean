import Projects.thermostat.HttpParseCode
import Projects.thermostat.Quiet
namespace E5R.Thermostat.HeadFieldsEmptyBranch
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (count : Word) (empty : Bool)
    (hp : c.pc=0x80002fb4#32) (h21 : c.get 21=count)
    (ht : taken .eq count (0 : Word)=empty) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if empty then 0x80003456#32 else 0x80002fb8#32) ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  let d := c.goto (if empty then 0x80003456#32 else 0x80002fb8#32)
  have step : Quiet.Step B img ⟨c,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495860) fun o => ?_
    rw [exec_branch,h21,Core.get_zero,ht,hp]
    cases empty with
    | false => rfl
    | true =>
      simp only [ite_true]
      rw [show 0x80002fb4#32+0x4a2#32=0x80003456#32 by decide +kernel,jump_ok _ _ (by decide)]
      rfl
  exact ⟨d,.single step,rfl,fun _ => rfl,rfl⟩

end E5R.Thermostat.HeadFieldsEmptyBranch
