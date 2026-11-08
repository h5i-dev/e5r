import Projects.thermostat.HeaderCode
namespace E5R.Thermostat.HeaderNone
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (hp : c.pc = 0x8000274e#32) :
    ∃ d, DetSteps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = c.get 1 &&& ~~~1 ∧ d.get 10 = 0#32 ∧
      (∀ r : Reg, r ≠ 10 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 0#32 0x80002750#32
  let d := c1.goto (c.get 1 &&& ~~~1)
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact hd2147493710) fun o => ?_
    rw [exec_opimm,Core.get_zero,hp];rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨d,ram⟩ := by
    refine detStep_of (by change (0x80002750#32).getLsbD 0 = false;decide) hd2147493712 fun o => ?_
    have hv : c1.get 1 = c.get 1 := by simp [c1,Core.wr_get_ne]
    rw [exec_jalr,hv,BitVec.add_zero,jump_ok _ _ (clear_bit0 _)];rfl
  refine ⟨d,.step s0 (.single s1),rfl,?_,?_,by rfl⟩
  · simp [d,c1,Core.wr_get]
  · intro r hr;simp [d,c1,Core.wr_get_ne,hr]
end E5R.Thermostat.HeaderNone
