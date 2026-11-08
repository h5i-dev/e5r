import Projects.thermostat.ZeroCode
import Projects.thermostat.Quiet
namespace E5R.Thermostat.HeadZeroRet
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc=0x8000569e#32) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=c.get 1 &&& ~~~1 ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  let d := c.goto (c.get 1 &&& ~~~1)
  have t : Quiet.Step B img ⟨c,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact ze2147505822) fun o => ?_
    rw [exec_jalr,BitVec.add_zero,jump_ok _ _ (clear_bit0 _)]
    rfl
  exact ⟨d,.single t,rfl,fun _ => rfl,rfl⟩
end E5R.Thermostat.HeadZeroRet
