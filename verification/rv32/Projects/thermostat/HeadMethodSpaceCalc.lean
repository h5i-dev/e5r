import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadMethodSpaceCalc
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (m j v : Word) (h17 : c.get 17=m) (h9 : c.get 9=j) (h19 : c.get 19=v)
    (hp : c.pc=0x80002da2#32) :
    ∃ d, Quiet.Steps B img 7 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80002dbc#32 ∧
      d.get 6=alu .or (alu .or (alu .sltu (m) (1#32)) (alu .xor (alu .sltu (m) (j)) (1#32))) (alu .sltu ((0 : Word)) (alu .add (v) (0xffffffe0#32))) ∧ d.get 7=alu .sltu ((0 : Word)) (alu .add (v) (0xffffffe0#32)) ∧ d.get 19=alu .add (v) (0xffffffe0#32) ∧ (∀ r : Reg, r≠6 → r≠7 → r≠19 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 6 (alu .sltu (m) (1#32)) 0x80002da6#32
  let c2 := c1.wr 7 (alu .sltu (m) (j)) 0x80002daa#32
  let c3 := c2.wr 7 (alu .xor (alu .sltu (m) (j)) (1#32)) 0x80002dae#32
  let c4 := c3.wr 19 (alu .add (v) (0xffffffe0#32)) 0x80002db0#32
  let c5 := c4.wr 6 (alu .or (alu .sltu (m) (1#32)) (alu .xor (alu .sltu (m) (j)) (1#32))) 0x80002db4#32
  let c6 := c5.wr 7 (alu .sltu ((0 : Word)) (alu .add (v) (0xffffffe0#32))) 0x80002db8#32
  let c7 := c6.wr 6 (alu .or (alu .or (alu .sltu (m) (1#32)) (alu .xor (alu .sltu (m) (j)) (1#32))) (alu .sltu ((0 : Word)) (alu .add (v) (0xffffffe0#32)))) 0x80002dbc#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495330) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v17 : c.get 17=m := by simp [Core.wr_get_ne,Core.wr_get,h17,h9,h19]
    rw [exec_opimm,v17];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80002da6#32).getLsbD 0=false;decide) hh2147495334 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v17 : c1.get 17=m := by simp [c1,Core.wr_get_ne,Core.wr_get,h17,h9,h19]
    have v9 : c1.get 9=j := by simp [c1,Core.wr_get_ne,Core.wr_get,h17,h9,h19]
    rw [exec_op,v17,v9];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80002daa#32).getLsbD 0=false;decide) hh2147495338 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v7 : c2.get 7=alu .sltu (m) (j) := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h17,h9,h19]
    rw [exec_opimm,v7];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80002dae#32).getLsbD 0=false;decide) hh2147495342 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v19 : c3.get 19=v := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h17,h9,h19]
    rw [exec_opimm,v19];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80002db0#32).getLsbD 0=false;decide) hh2147495344 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v6 : c4.get 6=alu .sltu (m) (1#32) := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h17,h9,h19]
    have v7 : c4.get 7=alu .xor (alu .sltu (m) (j)) (1#32) := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h17,h9,h19]
    rw [exec_op,v6,v7];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80002db4#32).getLsbD 0=false;decide) hh2147495348 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v19 : c5.get 19=alu .add (v) (0xffffffe0#32) := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h17,h9,h19]
    rw [exec_op,Core.get_zero,v19];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x80002db8#32).getLsbD 0=false;decide) hh2147495352 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v6 : c6.get 6=alu .or (alu .sltu (m) (1#32)) (alu .xor (alu .sltu (m) (j)) (1#32)) := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h17,h9,h19]
    have v7 : c6.get 7=alu .sltu ((0 : Word)) (alu .add (v) (0xffffffe0#32)) := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h17,h9,h19]
    rw [exec_op,v6,v7];first | rfl | (rw [hp];rfl)
  refine ⟨c7,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.single t6)))))),rfl,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h17,h9,h19]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h17,h9,h19]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h17,h9,h19]
  · intro reg h6 h7 h19;simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h17,h9,h19,h6,h7,h19]
end E5R.Thermostat.HeadMethodSpaceCalc
