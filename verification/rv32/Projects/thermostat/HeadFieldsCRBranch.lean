import Projects.thermostat.HttpParseCode
import Projects.thermostat.Quiet
namespace E5R.Thermostat.HeadFieldsCRBranch
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (index cap : Word) (bad : Bool)
    (hp : c.pc=0x80002fa4#32) (h13 : c.get 13=index) (h10 : c.get 10=cap) (ht : taken .geu index cap=bad) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if bad then 0x800033ea#32 else 0x80002fa8#32) ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  let d := c.goto (if bad then 0x800033ea#32 else 0x80002fa8#32)
  have t : Quiet.Step B img ⟨c,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495844) fun o => ?_
    rw [exec_branch,h13,h10,ht,hp]
    cases bad with
    | false => rfl
    | true =>
      simp only [ite_true]
      rw [show 0x80002fa4#32+0x446#32=0x800033ea#32 by decide +kernel,jump_ok _ _ (by decide)]
      rfl
  exact ⟨d,.single t,rfl,fun _ => rfl,rfl⟩
end E5R.Thermostat.HeadFieldsCRBranch
