import Projects.thermostat.HttpParseCode01
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadReject414
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)  
    (hp : c.pc=0x80002d52#32) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80002d60#32 ∧
      d.get 11=4#32 ∧ d.get 12=414#32 ∧ (∀ r : Reg, r≠11 → r≠12 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 11 (4#32) 0x80002d54#32
  let c2 := c1.wr 12 (414#32) 0x80002d58#32
  let c3 := c2.goto 0x80002d60#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495250) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80002d54#32).getLsbD 0=false;decide) hh2147495252 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80002d58#32).getLsbD 0=false;decide) hh2147495256 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    rw [exec_jal,Core.set_zero]
    change Observed.interp B img o (jump c2 (0x80002d58#32+8#32)) ram 0 [] []=_
    rw [show 0x80002d58#32+8#32=0x80002d60#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c3,.step t0 (.step t1 (.single t2)),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · intro reg h11 h12;simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12]
end E5R.Thermostat.HeadReject414
