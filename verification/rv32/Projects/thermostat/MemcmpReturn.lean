import Projects.thermostat.MemcmpCode
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.MemcmpReturn
open E5R E5R.Thermostat

theorem zero (B : Board) (c : Core) (ram : Word → BitVec 8) (hp : c.pc = 0x80005178#32) :
    ∃ d, DetSteps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = c.get 1 &&& ~~~1 ∧
      d.get 10 = 0#32 ∧ (∀ r : Reg, r ≠ 10 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (0#32) 0x8000517a#32
  let d := c1.goto (c.get 1 &&& ~~~1)
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact mc2147504504) fun o => ?_
    rw [exec_opimm,Core.get_zero,hp];rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨d,ram⟩ := by
    refine detStep_of (by change (0x8000517a#32).getLsbD 0 = false;decide) mc2147504506 fun o => ?_
    have hv : c1.get 1 = c.get 1 := by simp [c1,Core.wr_get_ne]
    rw [exec_jalr,hv,BitVec.add_zero,jump_ok _ _ (clear_bit0 _)];rfl
  refine ⟨d,.step s0 (.single s1),rfl,?_,?_,by rfl⟩
  · simp [d,c1,Core.wr_get]
  · intro r hr;simp [d,c1,Core.wr_get_ne,hr]

theorem diff (B : Board) (c : Core) (ram : Word → BitVec 8) (hp : c.pc = 0x8000517c#32) :
    ∃ d, DetSteps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = c.get 1 &&& ~~~1 ∧
      d.get 10 = c.get 13-c.get 14 ∧ (∀ r : Reg, r ≠ 10 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (c.get 13-c.get 14) 0x80005180#32
  let d := c1.goto (c.get 1 &&& ~~~1)
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact mc2147504508) fun o => ?_
    rw [exec_op,hp];rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨d,ram⟩ := by
    refine detStep_of (by change (0x80005180#32).getLsbD 0 = false;decide) mc2147504512 fun o => ?_
    have hv : c1.get 1 = c.get 1 := by simp [c1,Core.wr_get_ne]
    rw [exec_jalr,hv,BitVec.add_zero,jump_ok _ _ (clear_bit0 _)];rfl
  refine ⟨d,.step s0 (.single s1),rfl,?_,?_,by rfl⟩
  · simp [d,c1,Core.wr_get]
  · intro r hr;simp [d,c1,Core.wr_get_ne,hr]
end E5R.Thermostat.MemcmpReturn
