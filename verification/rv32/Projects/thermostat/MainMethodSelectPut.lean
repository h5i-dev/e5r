import Projects.thermostat.MainMethodDecodeCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainMethodSelectPut
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) 

    (hp : c.pc=0x8000114c#32) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80001154#32 ∧
      d.get 14=3#32 ∧ d.get 16=84#32 ∧ d.get 17=2#32 ∧ (∀ r : Reg, r≠14 → r≠16 → r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 14 (3#32) 0x8000114e#32
  let c2 := c1.wr 16 (84#32) 0x80001152#32
  let c3 := c2.wr 17 (2#32) 0x80001154#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact re2147488076) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x8000114e#32).getLsbD 0=false;decide) re2147488078 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80001152#32).getLsbD 0=false;decide) re2147488082 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  refine ⟨c3,.step t0 (.step t1 (.single t2)),rfl,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · intro reg h14 h16 h17;simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h14,h16,h17]
end E5R.Thermostat.MainMethodSelectPut
