import Projects.thermostat.HttpReasonDefault402
import Projects.thermostat.StackBoard
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 5000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.ReasonBoardHttpReasonDefault402
open E5R E5R.Thermostat HttpReasonDefault402
abbrev B := StackBoard.board

theorem contract (c : Core) (ram : Word → BitVec 8) (dst : Word) (status : Nat) (hlo : 402≤status) (hhi : status≤402) (h10 : c.get 10=dst) (h11 : c.get 11=192#32) (h12 : c.get 12=13#32) (h13 : c.get 13=BitVec.ofNat 32 status)
    (hp : c.pc=0x80003584#32) :
    ∃ d, Quiet.Steps B img 14 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=c.get 1 &&& ~~~1 ∧
      d.get 14=dst ∧ d.get 15=403#32 ∧ d.get 10=1#32 ∧ d.get 11=13#32 ∧ (∀ r : Reg, r≠14 → r≠15 → r≠10 → r≠11 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 14 (dst) 0x80003586#32
  let c2 := c1.wr 15 (408#32) 0x8000358a#32
  let c3 := c2.wr 10 (1#32) 0x8000358c#32
  let c4 := c3.goto 0x80003590#32
  let c5 := c4.wr 15 (400#32) 0x80003594#32
  let c6 := c5.goto 0x80003598#32
  let c7 := c6.wr 15 (403#32) 0x8000359c#32
  let c8 := c7.goto 0x80003954#32
  let c9 := c8.wr 15 (401#32) 0x80003958#32
  let c10 := c9.goto 0x8000395c#32
  let c11 := c10.wr 15 (403#32) 0x80003960#32
  let c12 := c11.goto 0x80003e4a#32
  let c13 := c12.wr 11 (13#32) 0x80003e4c#32
  let c14 := c13.goto (c.get 1 &&& ~~~1)
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rp2147497348) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v10 : c.get 10=dst := by simp [Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,Core.get_zero,v10]
    rw [hp]
    change Observed.interp B img o (.done (c.wr 14 (alu .add 0#32 dst) 0x80003586#32)) ram 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show (0 : Word)=0#32 from rfl] : alu .add 0#32 dst=dst)];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80003586#32).getLsbD 0=false;decide) rp2147497350 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c1.wr 15 (alu .add 0#32 408#32) 0x8000358a#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 408#32=408#32)];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x8000358a#32).getLsbD 0=false;decide) rp2147497354 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c2.wr 10 (alu .add 0#32 1#32) 0x8000358c#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 1#32=1#32)];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x8000358c#32).getLsbD 0=false;decide) rp2147497356 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v15 : c3.get 15=408#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v13 : c3.get 13=(BitVec.ofNat 32 status) := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v15,v13,(by rw [HttpStatusMath.signed_lt 408 status (by omega) (by omega)];exact decide_eq_false (by omega) : taken .lt 408#32 (BitVec.ofNat 32 status)=false)]
    simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80003590#32).getLsbD 0=false;decide) rp2147497360 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c4.wr 15 (alu .add 0#32 400#32) 0x80003594#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 400#32=400#32)];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80003594#32).getLsbD 0=false;decide) rp2147497364 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v15 : c5.get 15=400#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v13 : c5.get 13=(BitVec.ofNat 32 status) := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v15,v13,(by rw [HttpStatusMath.signed_ge 400 status (by omega) (by omega)];exact decide_eq_false (by omega) : taken .ge 400#32 (BitVec.ofNat 32 status)=false)]
    simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x80003598#32).getLsbD 0=false;decide) rp2147497368 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c6.wr 15 (alu .add 0#32 403#32) 0x8000359c#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 403#32=403#32)];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x8000359c#32).getLsbD 0=false;decide) rp2147497372 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    have v15 : c7.get 15=403#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v13 : c7.get 13=(BitVec.ofNat 32 status) := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v15,v13,(by rw [HttpStatusMath.signed_ge 403 status (by omega) (by omega)];exact decide_eq_true (by omega) : taken .ge 403#32 (BitVec.ofNat 32 status)=true)]
    simp only [ite_true]
    rw [show c7.pc=2147497372#32 by rfl,show 2147497372#32+952#32=2147498324#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine Quiet.step_of (by change (0x80003954#32).getLsbD 0=false;decide) rp2147498324 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c8.wr 15 (alu .add 0#32 401#32) 0x80003958#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 401#32=401#32)];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine Quiet.step_of (by change (0x80003958#32).getLsbD 0=false;decide) rp2147498328 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) ram 0 [] [] = ⟨.ok c10 ram [],[]⟩
    have v13 : c9.get 13=(BitVec.ofNat 32 status) := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v15 : c9.get 15=401#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v13,v15,(HttpStatusMath.unequal status 401 (by omega) (by omega) (by omega))]
    simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine Quiet.step_of (by change (0x8000395c#32).getLsbD 0=false;decide) rp2147498332 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) ram 0 [] [] = ⟨.ok c11 ram [],[]⟩
    rw [exec_opimm,Core.get_zero]
    change Observed.interp B img o (.done (c10.wr 15 (alu .add 0#32 403#32) 0x80003960#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 403#32=403#32)];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine Quiet.step_of (by change (0x80003960#32).getLsbD 0=false;decide) rp2147498336 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) ram 0 [] [] = ⟨.ok c12 ram [],[]⟩
    have v13 : c11.get 13=(BitVec.ofNat 32 status) := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    have v15 : c11.get 15=403#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_branch,v13,v15,(HttpStatusMath.not_equal status 403 (by omega) (by omega) (by omega))]
    simp only [ite_true]
    rw [show c11.pc=2147498336#32 by rfl,show 2147498336#32+1258#32=2147499594#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t12 : Quiet.Step B img ⟨c12,ram⟩ ⟨c13,ram⟩ := by
    refine Quiet.step_of (by change (0x80003e4a#32).getLsbD 0=false;decide) rp2147499594 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) ram 0 [] [] = ⟨.ok c13 ram [],[]⟩
    have v12 : c12.get 12=13#32 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_op,Core.get_zero,v12]
    change Observed.interp B img o (.done (c12.wr 11 (alu .add 0#32 13#32) 0x80003e4c#32)) ram 0 [] [] = _
    rw [(by decide +kernel : alu .add 0#32 13#32=13#32)];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,ram⟩ ⟨c14,ram⟩ := by
    refine Quiet.step_of (by change (0x80003e4c#32).getLsbD 0=false;decide) rp2147499596 fun o => ?_
    change Observed.interp B img o (exec c13 _ _) ram 0 [] [] = ⟨.ok c14 ram [],[]⟩
    have v1 : c13.get 1=c.get 1 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
    rw [exec_jalr,v1,BitVec.add_zero]
    change Observed.interp B img o (jump c13 (c.get 1 &&& ~~~1)) ram 0 [] [] = _
    rw [jump_ok _ _ (clear_bit0 _)];first | rfl | (rw [hp];rfl)
  refine ⟨c14,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.single t13))))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13]
  · intro reg h14 h15 h10 h11;simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h13,h14,h15,h10,h11]
end E5R.Thermostat.ReasonBoardHttpReasonDefault402
