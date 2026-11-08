import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadNameAdvanceRaw
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (count relative ptr inverse remaining : Word) (h14 : c.get 14=count) (h13 : c.get 13=relative) (h10 : c.get 10=ptr) (h25 : c.get 25=inverse) (h31 : c.get 31=remaining)
(ht : taken .eq (relative+(count+1#32)) (0 : Word)=false)
    (hp : c.pc=0x80002fe0#32) :
    ∃ d, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80002ff0#32 ∧
      d.get 14=count+1#32 ∧ d.get 30=relative+(count+1#32) ∧ d.get 10=ptr+1#32 ∧ d.get 25=inverse+0xffffffff#32 ∧ d.get 31=remaining+0xffffffff#32 ∧ (∀ r : Reg, r≠14 → r≠30 → r≠10 → r≠25 → r≠31 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 14 (count+1#32) 0x80002fe2#32
  let c2 := c1.wr 30 (relative+(count+1#32)) 0x80002fe6#32
  let c3 := c2.wr 10 (ptr+1#32) 0x80002fe8#32
  let c4 := c3.wr 25 (inverse+0xffffffff#32) 0x80002fea#32
  let c5 := c4.wr 31 (remaining+0xffffffff#32) 0x80002fec#32
  let c6 := c5.goto 0x80002ff0#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495904) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,h14];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80002fe2#32).getLsbD 0=false;decide) hh2147495906 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v13 : c1.get 13=relative := by simp [c1,Core.wr_get_ne,Core.wr_get,h14,h13,h10,h25,h31]
    have v14 : c1.get 14=count+1#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h14,h13,h10,h25,h31]
    rw [exec_op,v13,v14];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80002fe6#32).getLsbD 0=false;decide) hh2147495910 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v10 : c2.get 10=ptr := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h14,h13,h10,h25,h31]
    rw [exec_opimm,v10];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80002fe8#32).getLsbD 0=false;decide) hh2147495912 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v25 : c3.get 25=inverse := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h14,h13,h10,h25,h31]
    rw [exec_opimm,v25];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80002fea#32).getLsbD 0=false;decide) hh2147495914 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v31 : c4.get 31=remaining := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h14,h13,h10,h25,h31]
    rw [exec_opimm,v31];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80002fec#32).getLsbD 0=false;decide) hh2147495916 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v30 : c5.get 30=relative+(count+1#32) := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h14,h13,h10,h25,h31]
    rw [exec_branch,v30,Core.get_zero,ht];first | rfl | (rw [hp];rfl)
  refine ⟨c6,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.single t5))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h14,h13,h10,h25,h31]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h14,h13,h10,h25,h31]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h14,h13,h10,h25,h31]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h14,h13,h10,h25,h31]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h14,h13,h10,h25,h31]
  · intro reg h14 h30 h10 h25 h31;simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h14,h13,h10,h25,h31,h14,h30,h10,h25,h31]
end E5R.Thermostat.HeadNameAdvanceRaw
