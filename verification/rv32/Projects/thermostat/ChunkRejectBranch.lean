import Projects.thermostat.ChunkRejectCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ChunkRejectBranch
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)  (tag : c.get 10=3#32) (two : c.get 18=2#32)
    (hp : c.pc=0x8000106c#32) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80000a9a#32 ∧
      d.get 18=0#32 ∧ d.get 9=3#32 ∧ (∀ r : Reg, r≠18 → r≠9 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x80001828#32
  let c2 := c1.wr 18 (0#32) 0x8000182a#32
  let c3 := c2.wr 9 (3#32) 0x8000182c#32
  let c4 := c3.goto 0x80000a9a#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact ChunkRejectCode.cr2147487852) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v10 : c.get 10=3#32 := by simp [Core.wr_get_ne,Core.wr_get,tag,two]
    have v18 : c.get 18=2#32 := by simp [Core.wr_get_ne,Core.wr_get,tag,two]
    rw [exec_branch,v10,v18,show taken .ne 3#32 2#32=true by decide +kernel]
    simp only [ite_true]
    rw [hp,show 0x8000106c#32+0x000007bc#32=0x80001828#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80001828#32).getLsbD 0=false;decide) ChunkRejectCode.cr2147489832 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x8000182a#32).getLsbD 0=false;decide) ChunkRejectCode.cr2147489834 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x8000182c#32).getLsbD 0=false;decide) ChunkRejectCode.cr2147489836 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    rw [exec_jal,Core.set_zero,show c3.pc=0x8000182c#32 from rfl]
    rw [show 0x8000182c#32+0xfffff26e#32=0x80000a9a#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c4,.step t0 (.step t1 (.step t2 (.single t3))),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,tag,two]
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,tag,two]
  · intro reg h18 h9;simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,tag,two,h18,h9]
end E5R.Thermostat.ChunkRejectBranch
