import Projects.thermostat.SendCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.SendFresh
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (obj res : Word) (h10 : c.get 10=res) (h11 : c.get 11=obj) (hm : Memory.Block B obj 89) (hz : ram (obj+45#32)=0#8)
    (hp : c.pc=0x80000322#32) :
    ∃ d, Quiet.Steps B img 7 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x8000036a#32 ∧
      d.get 8=obj ∧ d.get 9=res ∧ d.get 10=0#32 ∧ d.get 11=3#32 ∧ d.get 18=obj+48#32 ∧ (∀ r : Reg, r≠8 → r≠9 → r≠10 → r≠11 → r≠18 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 8 (obj) 0x80000324#32
  let c2 := c1.wr 9 (res) 0x80000326#32
  let c3 := c2.wr 10 (0#32) 0x8000032a#32
  let c4 := c3.wr 11 (3#32) 0x8000032c#32
  let c5 := c4.wr 18 (obj+48#32) 0x80000330#32
  let c6 := c5.goto 0x80000334#32
  let c7 := c6.goto 0x8000036a#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact se2147484450) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v11 : c.get 11=obj := by simp [Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_op,Core.get_zero,v11,(show alu .add (0 : Word) (obj)=obj from BitVec.zero_add _)];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80000324#32).getLsbD 0=false;decide) se2147484452 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v10 : c1.get 10=res := by simp [c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_op,Core.get_zero,v10,(show alu .add (0 : Word) (res)=res from BitVec.zero_add _)];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80000326#32).getLsbD 0=false;decide) se2147484454 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v11 : c2.get 11=obj := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_load,v11,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access hm (off := 45) (by decide) (by decide))]
    change Observed.interp B img o (.done (c2.wr 10 (extend .b false (ramRead ram (obj+45#32) .b)) (c2.pc+4#32))) ram 0 [] [] = _
    rw [Memory.load_byte,hz];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x8000032a#32).getLsbD 0=false;decide) se2147484458 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x8000032c#32).getLsbD 0=false;decide) se2147484460 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v8 : c4.get 8=obj := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_opimm,v8];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80000330#32).getLsbD 0=false;decide) se2147484464 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v11 : c5.get 11=3#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    have v10 : c5.get 10=0#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_branch,v11,v10,show taken .lt 3#32 0#32=false by decide];simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x80000334#32).getLsbD 0=false;decide) se2147484468 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v10 : c6.get 10=0#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_branch,v10,Core.get_zero,show taken .eq 0#32 (0 : Word)=true by decide]
    simp only [ite_true]
    rw [show c6.pc=0x80000334#32 by rfl,show 0x80000334#32+54#32=0x8000036a#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c7,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.single t6)))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
  · intro reg h8 h9 h10 h11 h18;simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h8,h9,h10,h11,h18]
end E5R.Thermostat.SendFresh
