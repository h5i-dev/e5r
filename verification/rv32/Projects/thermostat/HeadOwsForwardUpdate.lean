import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadOwsForwardUpdate
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (index remaining : Word) (h15 : c.get 15=index) (h25 : c.get 25=remaining)
    (hp : c.pc=0x8000309c#32) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800030a0#32 ∧
      d.get 25=remaining+0xffffffff#32 ∧ d.get 15=index+1#32 ∧ (∀ r : Reg, r≠25 → r≠15 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 25 (remaining+0xffffffff#32) 0x8000309e#32
  let c2 := c1.wr 15 (index+1#32) 0x800030a0#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147496092) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,h25];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x8000309e#32).getLsbD 0=false;decide) hh2147496094 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v15 : c1.get 15=index := by simp [c1,Core.wr_get_ne,Core.wr_get,h15,h25]
    rw [exec_opimm,v15];first | rfl | (rw [hp];rfl)
  refine ⟨c2,.step t0 (.single t1),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c2,c1,Core.wr_get_ne,Core.wr_get,h15,h25]
  · simp [c2,c1,Core.wr_get_ne,Core.wr_get,h15,h25]
  · intro reg h25 h15;simp [c2,c1,Core.wr_get_ne,Core.wr_get,h15,h25,h25,h15]
end E5R.Thermostat.HeadOwsForwardUpdate
