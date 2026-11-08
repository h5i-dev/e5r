import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadTeGuardAdd
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (raw remaining : Word) (h11 : c.get 11=raw) (h10 : c.get 10=remaining)
    (hp : c.pc=0x80003284#32) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x8000328a#32 ∧
      d.get 12=raw+remaining ∧ d.get 14=17#32 ∧ (∀ r : Reg, r≠12 → r≠14 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 12 (raw+remaining) 0x80003288#32
  let c2 := c1.wr 14 (17#32) 0x8000328a#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147496580) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_op,h11,h10];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80003288#32).getLsbD 0=false;decide) hh2147496584 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  refine ⟨c2,.step t0 (.single t1),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c2,c1,Core.wr_get_ne,Core.wr_get,h11,h10]
  · simp [c2,c1,Core.wr_get_ne,Core.wr_get,h11,h10]
  · intro reg h12 h14;simp [c2,c1,Core.wr_get_ne,Core.wr_get,h11,h10,h12,h14]
end E5R.Thermostat.HeadTeGuardAdd
