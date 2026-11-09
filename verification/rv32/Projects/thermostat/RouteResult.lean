import Projects.thermostat.MainRouterCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.RouteResult
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (flag count : Word) (h11 : c.get 11=flag) (h8 : c.get 8=count)
    (hp : c.pc=0x80002936#32) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x8000293a#32 ∧
      d.get 10=flag ∧ d.get 11=count ∧ (∀ r : Reg, r≠10 → r≠11 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (flag) 0x80002938#32
  let c2 := c1.wr 11 (count) 0x8000293a#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rt2147494198) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have source : c.get 11=flag := by simp [Core.wr_get_ne,Core.wr_get,h11,h8]
    rw [exec_op,Core.get_zero,source]
    try rw [hp]
    change Observed.interp B img o (.done (c.wr 10 (0#32+flag) 0x80002938#32)) ram 0 [] []=_
    rw [BitVec.zero_add];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80002938#32).getLsbD 0=false;decide) rt2147494200 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have source : c1.get 8=count := by simp [c1,Core.wr_get_ne,Core.wr_get,h11,h8]
    rw [exec_op,Core.get_zero,source]
    try rw [hp]
    change Observed.interp B img o (.done (c1.wr 11 (0#32+count) 0x8000293a#32)) ram 0 [] []=_
    rw [BitVec.zero_add];first | rfl | (rw [hp];rfl)
  refine ⟨c2,.step t0 (.single t1),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c2,c1,Core.wr_get_ne,Core.wr_get,h11,h8]
  · simp [c2,c1,Core.wr_get_ne,Core.wr_get,h11,h8]
  · intro reg h10 h11;simp [c2,c1,Core.wr_get_ne,Core.wr_get,h11,h8,h10,h11]
end E5R.Thermostat.RouteResult
