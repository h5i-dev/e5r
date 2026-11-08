import Projects.thermostat.ZeroEntry
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadZeroEntry271
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (h10 : c.get 10=p) (h11 : c.get 11=0#32) (h12 : c.get 12=271#32)
(ha : p.toNat%4=0) (htop : p.toNat+271<2^32)
    (hp : c.pc=0x80005638#32) :
    ∃ d, Quiet.Steps B img 14 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80005676#32 ∧
      d.get 13=p+268#32 ∧ d.get 14=p ∧ d.get 12=271#32 ∧ d.get 15=0#32 ∧ d.get 16=0#32 ∧ (∀ r : Reg, r≠13 → r≠14 → r≠12 → r≠15 → r≠16 → d.get r=c.get r) ∧ d.sameCsr c := by
  have compare : taken .geu p (p+268#32)=false := by
    change (!decide (p.toNat<(p+268#32).toNat))=false
    rw [WordZero.add_nat p 268 (by omega)]
    simp only [show p.toNat<p.toNat+268 by omega,decide_true,Bool.not_true]
  let c1 := c.wr 13 (16#32) 0x8000563a#32
  let c2 := c1.goto 0x8000563e#32
  let c3 := c2.wr 13 (0#32-p) 0x80005642#32
  let c4 := c3.wr 13 (0#32) 0x80005644#32
  let c5 := c4.wr 14 (p) 0x80005648#32
  let c6 := c5.goto 0x8000565a#32
  let c7 := c6.wr 12 (271#32) 0x8000565c#32
  let c8 := c7.wr 13 (268#32) 0x80005660#32
  let c9 := c8.wr 13 (p+268#32) 0x80005662#32
  let c10 := c9.goto 0x80005666#32
  let c11 := c10.wr 15 (0x01010000#32) 0x8000566a#32
  let c12 := c11.wr 16 (0#32) 0x8000566e#32
  let c13 := c12.wr 15 (0x01010101#32) 0x80005672#32
  let c14 := c13.wr 15 (0#32) 0x80005676#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact ze2147505720) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x8000563a#32).getLsbD 0=false;decide) ze2147505722 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v12 : c1.get 12=271#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    have v13 : c1.get 13=16#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    rw [exec_branch,v12,v13,show taken .ltu 271#32 16#32=false by decide +kernel];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x8000563e#32).getLsbD 0=false;decide) ze2147505726 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v10 : c2.get 10=p := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    rw [exec_op,Core.get_zero,v10];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80005642#32).getLsbD 0=false;decide) ze2147505730 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v13 : c3.get 13=0#32-p := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    rw [exec_opimm,v13]
    change Observed.interp B img o (.done (c3.wr 13 ((0#32-p) &&& 3#32) (c3.pc+2#32))) ram 0 [] [] = _
    rw [WordZero.neg_and_three p ha];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80005644#32).getLsbD 0=false;decide) ze2147505732 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v10 : c4.get 10=p := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    have v13 : c4.get 13=0#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    rw [exec_op,v10,v13];simp only [alu,BitVec.add_zero];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80005648#32).getLsbD 0=false;decide) ze2147505736 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v10 : c5.get 10=p := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    have v14 : c5.get 14=p := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    rw [exec_branch,v10,v14,show taken .geu p p=true by simp [taken,BitVec.ult]]
    simp only [ite_true]
    change Observed.interp B img o (jump c5 (0x80005648#32+0x12#32)) ram 0 [] [] = _
    rw [show 0x80005648#32+0x12#32=0x8000565a#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x8000565a#32).getLsbD 0=false;decide) ze2147505754 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v12 : c6.get 12=271#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    have v13 : c6.get 13=0#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    rw [exec_op,v12,v13,show alu .sub 271#32 0#32=271#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x8000565c#32).getLsbD 0=false;decide) ze2147505756 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    have v12 : c7.get 12=271#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    rw [exec_opimm,v12,show alu .and 271#32 0xfffffffc#32=268#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine Quiet.step_of (by change (0x80005660#32).getLsbD 0=false;decide) ze2147505760 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 ram [],[]⟩
    have v13 : c8.get 13=268#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    have v14 : c8.get 14=p := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    rw [exec_op,v13,v14]
    change Observed.interp B img o (.done (c8.wr 13 (268#32+p) (c8.pc+2#32))) ram 0 [] [] = _
    rw [BitVec.add_comm 268#32 p];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine Quiet.step_of (by change (0x80005662#32).getLsbD 0=false;decide) ze2147505762 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) ram 0 [] [] = ⟨.ok c10 ram [],[]⟩
    have v13 : c9.get 13=p+268#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    have v14 : c9.get 14=p := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    rw [exec_branch,v14,v13,compare];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine Quiet.step_of (by change (0x80005666#32).getLsbD 0=false;decide) ze2147505766 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) ram 0 [] [] = ⟨.ok c11 ram [],[]⟩
    rw [exec_lui];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine Quiet.step_of (by change (0x8000566a#32).getLsbD 0=false;decide) ze2147505770 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) ram 0 [] [] = ⟨.ok c12 ram [],[]⟩
    have v11 : c11.get 11=0#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    rw [exec_opimm,v11,show alu .and 0#32 255#32=0#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t12 : Quiet.Step B img ⟨c12,ram⟩ ⟨c13,ram⟩ := by
    refine Quiet.step_of (by change (0x8000566e#32).getLsbD 0=false;decide) ze2147505774 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) ram 0 [] [] = ⟨.ok c13 ram [],[]⟩
    have v15 : c12.get 15=0x01010000#32 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    rw [exec_opimm,v15,show alu .add 0x01010000#32 257#32=0x01010101#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,ram⟩ ⟨c14,ram⟩ := by
    refine Quiet.step_of (by change (0x80005672#32).getLsbD 0=false;decide) ze2147505778 fun o => ?_
    change Observed.interp B img o (exec c13 _ _) ram 0 [] [] = ⟨.ok c14 ram [],[]⟩
    have v15 : c13.get 15=0x01010101#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    have v16 : c13.get 16=0#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
    rw [ZeroEntry.exec_mul_checked,v16,v15];simp only [muldiv,BitVec.zero_mul];first | rfl | (rw [hp];rfl)
  refine ⟨c14,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.single t13))))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
  · simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
  · simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
  · simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
  · simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12]
  · intro reg h13 h14 h12 h15 h16;simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h12,h15,h16]
end E5R.Thermostat.HeadZeroEntry271
