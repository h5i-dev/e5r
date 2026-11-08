import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadTargetSetup
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (m j : Word) (h17 : c.get 17=m) (h9 : c.get 9=j)
    (hp : c.pc=0x80002dc8#32) :
    ∃ d, Quiet.Steps B img 5 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80002dd8#32 ∧
      d.get 30=0#32 ∧ d.get 31=(~~~m)+j ∧ d.get 8=m+1#32 ∧ d.get 19=94#32 ∧ (∀ r : Reg, r≠30 → r≠31 → r≠8 → r≠19 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 30 (0#32) 0x80002dca#32
  let c2 := c1.wr 31 (~~~m) 0x80002dce#32
  let c3 := c2.wr 31 ((~~~m)+j) 0x80002dd0#32
  let c4 := c3.wr 8 (m+1#32) 0x80002dd4#32
  let c5 := c4.wr 19 (94#32) 0x80002dd8#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495368) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80002dca#32).getLsbD 0=false;decide) hh2147495370 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v17 : c1.get 17=m := by simp [c1,Core.wr_get_ne,Core.wr_get,h17,h9]
    rw [exec_opimm,v17]
    change Observed.interp B img o (.done (c1.wr 31 (m ^^^ BitVec.allOnes 32) (c1.pc+4#32))) ram 0 [] [] = _
    rw [BitVec.xor_allOnes];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80002dce#32).getLsbD 0=false;decide) hh2147495374 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v31 : c2.get 31= ~~~m := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h17,h9]
    have v9 : c2.get 9=j := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h17,h9]
    rw [exec_op,v31,v9];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80002dd0#32).getLsbD 0=false;decide) hh2147495376 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v17 : c3.get 17=m := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h17,h9]
    rw [exec_opimm,v17];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80002dd4#32).getLsbD 0=false;decide) hh2147495380 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  refine ⟨c5,.step t0 (.step t1 (.step t2 (.step t3 (.single t4)))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h17,h9]
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h17,h9]
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h17,h9]
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h17,h9]
  · intro reg h30 h31 h8 h19;simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h17,h9,h30,h31,h8,h19]
end E5R.Thermostat.HeadTargetSetup
