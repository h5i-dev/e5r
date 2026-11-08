import Projects.thermostat.MainChunkCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainChunkDataBranch
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)  (h10 : c.get 10=1#32) (h22 : c.get 22=1#32)
    (hp : c.pc=0x80000f62#32) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80000f6a#32 ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x80000f66#32
  let c2 := c1.goto 0x80000f6a#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact cc2147487586) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_branch,Core.get_zero,h10,show taken .ge (0 : Word) 1#32=false by decide +kernel,hp];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80000f66#32).getLsbD 0=false;decide) cc2147487590 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v10 : c1.get 10=1#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h10,h22]
    have v22 : c1.get 22=1#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h10,h22]
    rw [exec_branch,v10,v22,show taken .ne 1#32 1#32=false by decide +kernel];first | rfl | (rw [hp];rfl)
  refine ⟨c2,.step t0 (.single t1),rfl,?_ ,by rfl⟩
  · intro reg ;simp [c2,c1,Core.wr_get_ne,Core.wr_get,h10,h22]
end E5R.Thermostat.MainChunkDataBranch
