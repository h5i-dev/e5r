import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadChunkedGuard6
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (remaining : Word) (h11 : c.get 11=remaining) (test : taken .eq remaining 6#32=false)
    (hp : c.pc=0x80003392#32) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80003398#32 ∧
      d.get 12=6#32 ∧ (∀ r : Reg, r≠12 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 12 (6#32) 0x80003394#32
  let c2 := c1.goto 0x80003398#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147496850) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80003394#32).getLsbD 0=false;decide) hh2147496852 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v11 : c1.get 11=remaining := by simp [c1,Core.wr_get_ne,Core.wr_get,h11]
    have v12 : c1.get 12=6#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h11]
    rw [exec_branch,v11,v12,test];first | rfl | (rw [hp];rfl)
  refine ⟨c2,.step t0 (.single t1),rfl,?_ ,?_ ,by rfl⟩
  · simp [c2,c1,Core.wr_get_ne,Core.wr_get,h11]
  · intro reg h12;simp [c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12]
end E5R.Thermostat.HeadChunkedGuard6
