import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadTargetIncrement
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (remaining offset : Word) (h31 : c.get 31=remaining) (h30 : c.get 30=offset)
    (hp : c.pc=0x80002df4#32) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80002df8#32 ∧
      d.get 31=remaining+0xffffffff#32 ∧ d.get 30=offset+1#32 ∧ (∀ r : Reg, r≠31 → r≠30 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 31 (remaining+0xffffffff#32) 0x80002df6#32
  let c2 := c1.wr 30 (offset+1#32) 0x80002df8#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495412) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,h31];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80002df6#32).getLsbD 0=false;decide) hh2147495414 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v30 : c1.get 30=offset := by simp [c1,Core.wr_get_ne,Core.wr_get,h31,h30]
    rw [exec_opimm,v30];first | rfl | (rw [hp];rfl)
  refine ⟨c2,.step t0 (.single t1),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c2,c1,Core.wr_get_ne,Core.wr_get,h31,h30]
  · simp [c2,c1,Core.wr_get_ne,Core.wr_get,h31,h30]
  · intro reg h31 h30;simp [c2,c1,Core.wr_get_ne,Core.wr_get,h31,h30,h31,h30]
end E5R.Thermostat.HeadTargetIncrement
