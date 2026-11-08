import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadOwsTrimEmpty
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (finish : Word) (h26 : c.get 26=finish)
    (hp : c.pc=0x800030c6#32) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800030fa#32 ∧
      d.get 25=finish ∧ (∀ r : Reg, r≠25 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 25 (finish) 0x800030c8#32
  let c2 := c1.goto 0x800030fa#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147496134) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v26 : c.get 26=finish := by simp [Core.wr_get_ne,Core.wr_get,h26]
    rw [exec_op,Core.get_zero,v26,show alu .add (0 : Word) finish=finish from BitVec.zero_add _];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x800030c8#32).getLsbD 0=false;decide) hh2147496136 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    rw [exec_jal,Core.set_zero]
    change Observed.interp B img o (jump c1 (0x800030c8#32+0x32#32)) ram 0 [] [] = _
    rw [show 0x800030c8#32+0x32#32=0x800030fa#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c2,.step t0 (.single t1),rfl,?_ ,?_ ,by rfl⟩
  · simp [c2,c1,Core.wr_get_ne,Core.wr_get,h26]
  · intro reg h25;simp [c2,c1,Core.wr_get_ne,Core.wr_get,h26,h25]
end E5R.Thermostat.HeadOwsTrimEmpty
