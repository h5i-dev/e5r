import Projects.thermostat.MainQueryCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainQueryIncrement
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (offset ptr : Word)
(h14 : c.get 14=offset) (h12 : c.get 12=ptr)
    (hp : c.pc=0x80000be8#32) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80000bec#32 ∧
      d.get 14=offset+1#32 ∧ d.get 12=ptr+1#32 ∧ (∀ r : Reg, r≠14 → r≠12 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 14 (offset+1#32) 0x80000bea#32
  let c2 := c1.wr 12 (ptr+1#32) 0x80000bec#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact re2147486696) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v14 : c.get 14=offset := by simp [Core.wr_get_ne,Core.wr_get,h14,h12]
    rw [exec_opimm,v14];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80000bea#32).getLsbD 0=false;decide) re2147486698 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v12 : c1.get 12=ptr := by simp [c1,Core.wr_get_ne,Core.wr_get,h14,h12]
    rw [exec_opimm,v12];first | rfl | (rw [hp];rfl)
  refine ⟨c2,.step t0 (.single t1),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c2,c1,Core.wr_get_ne,Core.wr_get,h14,h12]
  · simp [c2,c1,Core.wr_get_ne,Core.wr_get,h14,h12]
  · intro reg h14 h12;simp [c2,c1,Core.wr_get_ne,Core.wr_get,h14,h12,h14,h12]
end E5R.Thermostat.MainQueryIncrement
