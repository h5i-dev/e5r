import Projects.thermostat.SendCode
import Projects.thermostat.QuietRam
import Projects.thermostat.HttpDecMath
import Projects.thermostat.ResponseHeadBodyMath
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.SendHeaderCall
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (dst body : Word) (status : Nat) (close : Bool) (hlo : 200≤status) (hhi : status≤599) (h19 : c.get 19=dst) (h20 : c.get 20=body) (h21 : c.get 21=BitVec.ofNat 32 status) (h22 : c.get 22=ResponseHeadBodyMath.boolWord close)
    (hp : c.pc=0x800003a2#32) :
    ∃ d, Quiet.Steps B img 9 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80003e4e#32 ∧
      d.get 10=dst ∧ d.get 16=ResponseHeadBodyMath.boolWord close ∧ d.get 11=192#32 ∧ d.get 12=BitVec.ofNat 32 status ∧ d.get 15=body ∧ d.get 1=0x800003c0#32 ∧ (∀ r : Reg, r≠10 → r≠16 → r≠11 → r≠12 → r≠15 → r≠1 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (200#32) 0x800003a6#32
  let c2 := c1.goto 0x800003aa#32
  let c3 := c2.wr 16 (ResponseHeadBodyMath.boolWord close) 0x800003ae#32
  let c4 := c3.wr 11 (192#32) 0x800003b2#32
  let c5 := c4.wr 10 (dst) 0x800003b4#32
  let c6 := c5.wr 12 (BitVec.ofNat 32 status) 0x800003b6#32
  let c7 := c6.wr 15 (body) 0x800003b8#32
  let c8 := c7.wr 1 (0x800043b8#32) 0x800003bc#32
  let c9 := c8.wr 1 (0x800003c0#32) 0x80003e4e#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact se2147484578) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x800003a6#32).getLsbD 0=false;decide) se2147484582 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v21 : c1.get 21=BitVec.ofNat 32 status := by simp [c1,Core.wr_get_ne,Core.wr_get,h19,h20,h21,h22]
    have v10 : c1.get 10=200#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h19,h20,h21,h22]
    rw [exec_branch,v21,v10,HttpDecMath.branch_ltu status 200 (by omega) (by decide),show decide (status<200)=false by simp [show ¬status<200 by omega]]
    simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x800003aa#32).getLsbD 0=false;decide) se2147484586 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v22 : c2.get 22=ResponseHeadBodyMath.boolWord close := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h19,h20,h21,h22]
    rw [exec_opimm,v22,(show alu .and (ResponseHeadBodyMath.boolWord close) 1#32=ResponseHeadBodyMath.boolWord close by cases close <;> decide +kernel)];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x800003ae#32).getLsbD 0=false;decide) se2147484590 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x800003b2#32).getLsbD 0=false;decide) se2147484594 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v19 : c4.get 19=dst := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h20,h21,h22]
    rw [exec_op,Core.get_zero,v19,(show alu .add (0 : Word) (dst)=dst from BitVec.zero_add _)];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x800003b4#32).getLsbD 0=false;decide) se2147484596 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v21 : c5.get 21=BitVec.ofNat 32 status := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h20,h21,h22]
    rw [exec_op,Core.get_zero,v21,(show alu .add (0 : Word) (BitVec.ofNat 32 status)=BitVec.ofNat 32 status from BitVec.zero_add _)];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x800003b6#32).getLsbD 0=false;decide) se2147484598 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v20 : c6.get 20=body := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h20,h21,h22]
    rw [exec_op,Core.get_zero,v20,(show alu .add (0 : Word) (body)=body from BitVec.zero_add _)];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x800003b8#32).getLsbD 0=false;decide) se2147484600 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    rw [exec_auipc,show c7.pc=0x800003b8#32 by rfl,show 0x800003b8#32+0x4000#32=0x800043b8#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine Quiet.step_of (by change (0x800003bc#32).getLsbD 0=false;decide) se2147484604 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 ram [],[]⟩
    have v1 : c8.get 1=0x800043b8#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h20,h21,h22]
    rw [exec_jalr,v1]
    change Observed.interp B img o (jump (c8.set 1 (0x800003bc#32+4#32)) ((0x800043b8#32+0xfffffa96#32) &&& ~~~1)) ram 0 [] [] = _
    rw [show (0x800043b8#32+0xfffffa96#32) &&& ~~~1=0x80003e4e#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c9,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.single t8)))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h20,h21,h22]
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h20,h21,h22]
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h20,h21,h22]
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h20,h21,h22]
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h20,h21,h22]
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h20,h21,h22]
  · intro reg h10 h16 h11 h12 h15 h1;simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h20,h21,h22,h10,h16,h11,h12,h15,h1]
end E5R.Thermostat.SendHeaderCall
