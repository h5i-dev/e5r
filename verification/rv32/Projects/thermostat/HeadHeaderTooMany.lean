import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadHeaderTooMany
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)  
    (hp : c.pc=0x800034d4#32) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x8000342c#32 ∧
      d.get 1=431#32 ∧ (∀ r : Reg, r≠1 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 1 (431#32) 0x800034d8#32
  let c2 := c1.goto 0x8000342c#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147497172) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x800034d8#32).getLsbD 0=false;decide) hh2147497176 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    rw [exec_jal,Core.set_zero]
    change Observed.interp B img o (jump c1 (0x800034d8#32+0xffffff54#32)) ram 0 [] [] = _
    rw [show 0x800034d8#32+0xffffff54#32=0x8000342c#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c2,.step t0 (.single t1),rfl,?_ ,?_ ,by rfl⟩
  · simp [c2,c1,Core.wr_get_ne,Core.wr_get]
  · intro reg h1;simp [c2,c1,Core.wr_get_ne,Core.wr_get,h1]
end E5R.Thermostat.HeadHeaderTooMany
