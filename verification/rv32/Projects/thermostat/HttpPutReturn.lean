import Projects.thermostat.HttpPutCode
import Projects.thermostat.Quiet
namespace E5R.Thermostat.HttpPutReturn
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (pos n : Word)
    (hp : c.pc=0x80004166#32) (h12 : c.get 12=pos) (h14 : c.get 14=n) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=c.get 1 &&& ~~~1 ∧
      d.get 10=1#32 ∧ d.get 11=n+pos ∧
      (∀ r : Reg, r≠10 → r≠11 → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.wr 11 (n+pos) 0x8000416a#32
  let b := a.wr 10 1#32 0x8000416c#32
  let d := b.goto (c.get 1 &&& ~~~1)
  have ta : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hp2147500390) fun o => ?_
    rw [exec_op,h14,h12,hp];rfl
  have tb : Quiet.Step B img ⟨a,ram⟩ ⟨b,ram⟩ := by
    refine Quiet.step_of (by change (0x8000416a#32).getLsbD 0=false;decide) hp2147500394 fun o => ?_
    rw [exec_opimm,Core.get_zero];rfl
  have td : Quiet.Step B img ⟨b,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of (by change (0x8000416c#32).getLsbD 0=false;decide) hp2147500396 fun o => ?_
    have hb : b.get 1=c.get 1 := by simp [b,a,Core.wr_get_ne]
    rw [exec_jalr,hb,BitVec.add_zero]
    change Observed.interp B img o (jump b (c.get 1 &&& ~~~1)) ram 0 [] [] = _
    rw [jump_ok _ _ (clear_bit0 _)];rfl
  refine ⟨d,.step ta (.step tb (.single td)),rfl,?_,?_,?_,by rfl⟩
  · simp [d,b,Core.wr_get]
  · simp [d,b,a,Core.wr_get,Core.wr_get_ne]
  · intro r h10 h11;simp [d,b,a,Core.wr_get_ne,h10,h11]
end E5R.Thermostat.HttpPutReturn
