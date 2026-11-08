import Projects.thermostat.HttpParseCode
import Projects.thermostat.Quiet
namespace E5R.Thermostat.HeadFieldsScanBranch
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (index cap : Word) (again : Bool)
    (hp : c.pc=0x80002f94#32) (h30 : c.get 30=index) (h15 : c.get 15=cap)
    (ht : taken .ltu index cap=again) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if again then 0x80002f6e#32 else 0x80002f98#32) ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  let d := c.goto (if again then 0x80002f6e#32 else 0x80002f98#32)
  have step : Quiet.Step B img ⟨c,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495828) fun o => ?_
    rw [exec_branch,h30,h15,ht,hp]
    cases again with
    | false => rfl
    | true =>
      simp only [ite_true]
      rw [show 0x80002f94#32+0xffffffda#32=0x80002f6e#32 by decide +kernel,jump_ok _ _ (by decide)]
      rfl
  exact ⟨d,.single step,rfl,fun _ => rfl,rfl⟩

theorem exhausted (B : Board) (c : Core) (ram : Word → BitVec 8) (hp : c.pc=0x80002f98#32) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800033ea#32 ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  let d := c.goto 0x800033ea#32
  have step : Quiet.Step B img ⟨c,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495832) fun o => ?_
    rw [exec_jal,Core.set_zero,hp]
    rw [show 0x80002f98#32+0x452#32=0x800033ea#32 by decide +kernel,jump_ok _ _ (by decide)]
    rfl
  exact ⟨d,.single step,rfl,fun _ => rfl,rfl⟩
end E5R.Thermostat.HeadFieldsScanBranch
