import Projects.thermostat.HttpParseCode
import Projects.thermostat.Quiet
namespace E5R.Thermostat.HeadTargetContinue
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (remaining : Word) (again : Bool)
    (hp : c.pc=0x80002df8#32) (h31 : c.get 31=remaining) (ht : taken .ne remaining (0 : Word)=again) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if again then 0x80002dd8#32 else 0x80002dfc#32) ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  let d := c.goto (if again then 0x80002dd8#32 else 0x80002dfc#32)
  have t : Quiet.Step B img ⟨c,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495416) fun o => ?_
    rw [exec_branch,h31,Core.get_zero,ht,hp]
    cases again with
    | false => rfl
    | true =>
      simp only [ite_true]
      rw [show 0x80002df8#32+0xffffffe0#32=0x80002dd8#32 by decide +kernel,jump_ok _ _ (by decide)]
      rfl
  exact ⟨d,.single t,rfl,fun _ => rfl,rfl⟩

theorem exhausted (B : Board) (c : Core) (ram : Word → BitVec 8) (hp : c.pc=0x80002dfc#32) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80002efc#32 ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  let d := c.goto 0x80002efc#32
  have t : Quiet.Step B img ⟨c,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495420) fun o => ?_
    rw [exec_jal,Core.set_zero,hp]
    rw [show 0x80002dfc#32+0x100#32=0x80002efc#32 by decide +kernel,jump_ok _ _ (by decide)]
    rfl
  exact ⟨d,.single t,rfl,fun _ => rfl,rfl⟩
end E5R.Thermostat.HeadTargetContinue
