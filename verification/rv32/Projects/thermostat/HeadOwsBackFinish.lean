import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadOwsBackFinish
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (start : Word) (h15 : c.get 15=start)
    (hp : c.pc=0x800030f8#32) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800030fa#32 ∧
      d.get 25=start ∧ (∀ r : Reg, r≠25 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 25 (start) 0x800030fa#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147496184) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_op,Core.get_zero,h15,show alu .add (0 : Word) start=start from BitVec.zero_add _];first | rfl | (rw [hp];rfl)
  refine ⟨c1,.single t0,rfl,?_ ,?_ ,by rfl⟩
  · simp [c1,Core.wr_get_ne,Core.wr_get,h15]
  · intro reg h25;simp [c1,Core.wr_get_ne,Core.wr_get,h15,h25]
end E5R.Thermostat.HeadOwsBackFinish
