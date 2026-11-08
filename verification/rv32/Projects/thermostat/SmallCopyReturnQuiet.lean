-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.SmallCopyReturn
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.SmallCopyReturn
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (hp : c.pc = 0x8000530c#32) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = c.get 1 &&& ~~~1 ∧ d.get 2 = c.get 2+16#32 ∧
      (∀ r : Reg, r ≠ 2 → d.get r = c.get r) ∧ d.sameCsr c := by
  let a := c.wr 2 (c.get 2+16#32) 0x8000530e#32
  let d := a.goto (c.get 1 &&& ~~~1)
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact cp2147504908) fun o => ?_
    rw [exec_opimm,hp];rfl
  have s1 : Quiet.Step B img ⟨a,ram⟩ ⟨d,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000530e#32).getLsbD 0 = false;decide) cp2147504910 fun o => ?_
    have h1 : a.get 1 = c.get 1 := Core.wr_get_ne _ _ _ _ _ (by decide)
    rw [exec_jalr,h1,BitVec.add_zero]
    change interp B img o (jump a (c.get 1 &&& ~~~1)) ram 0 [] = _
    rw [jump_ok _ _ (clear_bit0 _)];rfl
  refine ⟨d,.step s0 (.single s1),rfl,?_,?_,by rfl⟩
  · simp [d,a,Core.wr_get]
  · intro r hr;exact Core.wr_get_ne _ _ _ _ _ hr

end E5R.Thermostat.SmallCopyReturn
