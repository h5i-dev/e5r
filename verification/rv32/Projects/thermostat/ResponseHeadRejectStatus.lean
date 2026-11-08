import Projects.thermostat.ResponseHeadCode
import Projects.thermostat.QuietRam
import Projects.thermostat.ResponseHeadMath
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ResponseHeadRejectStatus
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)  (status : Nat) (hu16 : status<65536) (h12 : c.get 12=BitVec.ofNat 32 status) (hv : ¬(100≤status ∧ status≤599))
    (hp : c.pc=0x80003e4e#32) :
    ∃ d, Quiet.Steps B img 11 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=c.get 1 &&& ~~~1 ∧
      d.get 17=0#32 ∧ d.get 5=65036#32 ∧ d.get 10=0#32 ∧ d.get 11=65036#32 ∧ (∀ r : Reg, r≠17 → r≠5 → r≠10 → r≠11 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 17 (BitVec.ofNat 32 status+0xfffffda8#32) 0x80003e52#32
  let c2 := c1.wr 17 (((BitVec.ofNat 32 status+0xfffffda8#32) <<< 16)) 0x80003e54#32
  let c3 := c2.wr 5 (65536#32) 0x80003e56#32
  let c4 := c3.wr 17 (ResponseHeadMath.folded status) 0x80003e5a#32
  let c5 := c4.wr 5 (65036#32) 0x80003e5e#32
  let c6 := c5.goto 0x80003e62#32
  let c7 := c6.wr 17 (0#32) 0x80003e64#32
  let c8 := c7.goto 0x8000411c#32
  let c9 := c8.wr 10 (0#32) 0x8000411e#32
  let c10 := c9.wr 11 (65036#32) 0x80004120#32
  let c11 := c10.goto (c.get 1 &&& ~~~1)
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rh2147499598) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,h12,hp];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80003e52#32).getLsbD 0=false;decide) rh2147499602 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v17 : c1.get 17=BitVec.ofNat 32 status+0xfffffda8#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h12]
    rw [exec_opimm,v17];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80003e54#32).getLsbD 0=false;decide) rh2147499604 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    rw [exec_lui];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80003e56#32).getLsbD 0=false;decide) rh2147499606 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v17 : c3.get 17=((BitVec.ofNat 32 status+0xfffffda8#32) <<< 16) := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12]
    rw [exec_opimm,v17];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80003e5a#32).getLsbD 0=false;decide) rh2147499610 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v5 : c4.get 5=65536#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12]
    rw [exec_opimm,v5];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80003e5e#32).getLsbD 0=false;decide) rh2147499614 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v17 : c5.get 17=ResponseHeadMath.folded status := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12]
    have v5 : c5.get 5=65036#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12]
    rw [exec_branch,v17,v5,ResponseHeadMath.range_guard status hu16,decide_eq_false hv]
    simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x80003e62#32).getLsbD 0=false;decide) rh2147499618 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x80003e64#32).getLsbD 0=false;decide) rh2147499620 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    rw [exec_jal]
    change Observed.interp B img o (jump c7 (0x80003e64#32+696#32)) ram 0 [] [] = _
    rw [show 0x80003e64#32+696#32=0x8000411c#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine Quiet.step_of (by change (0x8000411c#32).getLsbD 0=false;decide) rh2147500316 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 ram [],[]⟩
    have v17 : c8.get 17=0#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12]
    rw [exec_op,Core.get_zero,v17];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine Quiet.step_of (by change (0x8000411e#32).getLsbD 0=false;decide) rh2147500318 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) ram 0 [] [] = ⟨.ok c10 ram [],[]⟩
    have v5 : c9.get 5=65036#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12]
    rw [exec_op,Core.get_zero,v5];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine Quiet.step_of (by change (0x80004120#32).getLsbD 0=false;decide) rh2147500320 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) ram 0 [] [] = ⟨.ok c11 ram [],[]⟩
    have v1 : c10.get 1=c.get 1 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12]
    rw [exec_jalr,v1,BitVec.add_zero]
    change Observed.interp B img o (jump c10 (c.get 1 &&& ~~~1)) ram 0 [] [] = _
    rw [jump_ok _ _ (clear_bit0 _)];first | rfl | (rw [hp];rfl)
  refine ⟨c11,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.single t10)))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12]
  · intro reg h17 h5 h10 h11;simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h17,h5,h10,h11]
end E5R.Thermostat.ResponseHeadRejectStatus
