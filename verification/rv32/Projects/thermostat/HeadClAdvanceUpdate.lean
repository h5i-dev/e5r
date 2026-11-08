import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadClAdvanceUpdate
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (remaining ptr literal : Word) (h10 : c.get 10=remaining) (h31 : c.get 31=ptr) (h30 : c.get 30=literal)
    (hp : c.pc=0x800031d4#32) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800031da#32 ∧
      d.get 10=remaining+0xffffffff#32 ∧ d.get 31=ptr+1#32 ∧ d.get 30=literal+1#32 ∧ (∀ r : Reg, r≠10 → r≠31 → r≠30 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (remaining+0xffffffff#32) 0x800031d6#32
  let c2 := c1.wr 31 (ptr+1#32) 0x800031d8#32
  let c3 := c2.wr 30 (literal+1#32) 0x800031da#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147496404) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,h10];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x800031d6#32).getLsbD 0=false;decide) hh2147496406 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v31 : c1.get 31=ptr := by simp [c1,Core.wr_get_ne,Core.wr_get,h10,h31,h30]
    rw [exec_opimm,v31];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x800031d8#32).getLsbD 0=false;decide) hh2147496408 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v30 : c2.get 30=literal := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h10,h31,h30]
    rw [exec_opimm,v30];first | rfl | (rw [hp];rfl)
  refine ⟨c3,.step t0 (.step t1 (.single t2)),rfl,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h31,h30]
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h31,h30]
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h31,h30]
  · intro reg h10 h31 h30;simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h31,h30,h10,h31,h30]
end E5R.Thermostat.HeadClAdvanceUpdate
