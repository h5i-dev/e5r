import Projects.thermostat.HttpParseCode
import Projects.thermostat.Quiet
namespace E5R.Thermostat.HeadMethodSpaceBranch
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (flag : Word) (bad : Bool)
    (hp : c.pc=0x80002dbc#32) (h6 : c.get 6=flag) (ht : taken .ne flag (0 : Word)=bad) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if bad then 0x80002efc#32 else 0x80002dc0#32) ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  let d := c.goto (if bad then 0x80002efc#32 else 0x80002dc0#32)
  have t : Quiet.Step B img ⟨c,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495356) fun o => ?_
    rw [exec_branch,h6,Core.get_zero,ht,hp]
    cases bad with
    | false => rfl
    | true =>
      simp only [ite_true]
      rw [show 0x80002dbc#32+0x140#32=0x80002efc#32 by decide +kernel,jump_ok _ _ (by decide)]
      rfl
  exact ⟨d,.single t,rfl,fun _ => rfl,rfl⟩
end E5R.Thermostat.HeadMethodSpaceBranch
