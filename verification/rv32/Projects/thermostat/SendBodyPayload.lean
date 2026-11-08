import Projects.thermostat.SendCode
import Projects.thermostat.QuietRam
import Projects.thermostat.SendBodyMath
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.SendBodyPayload
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (body : Word) (status : Nat) (hlo : 200≤status) (hhi : status≤599) (h10 : c.get 10=1#32) (h20 : c.get 20=body) (h21 : c.get 21=BitVec.ofNat 32 status) (h23 : c.get 23=0#32)
    (hp : c.pc=0x800003c0#32) :
    ∃ d, Quiet.Steps B img 12 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80000408#32 ∧
      d.get 12=ResponseHeadBodyMath.not304 status ∧ d.get 10=(if ResponseHeadSpec.hasBody status then body else 0#32) ∧ (∀ r : Reg, r≠12 → r≠10 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 12 (1#32) 0x800003c2#32
  let c2 := c1.goto 0x800003c6#32
  let c3 := c2.goto 0x800003ca#32
  let c4 := c3.wr 10 (BitVec.ofNat 32 status+0xffffff34#32) 0x800003ce#32
  let c5 := c4.wr 12 (BitVec.ofNat 32 status+0xfffffed0#32) 0x800003d2#32
  let c6 := c5.wr 10 (ResponseHeadBodyMath.not204 status) 0x800003d6#32
  let c7 := c6.wr 12 (ResponseHeadBodyMath.not304 status) 0x800003da#32
  let c8 := c7.wr 10 (SendBodyMath.flags status) 0x800003dc#32
  let c9 := c8.wr 10 ((SendBodyMath.flags status) <<< 31) 0x800003de#32
  let c10 := c9.wr 10 (SendBodyMath.mask status) 0x800003e0#32
  let c11 := c10.wr 10 ((if ResponseHeadSpec.hasBody status then body else 0#32)) 0x800003e4#32
  let c12 := c11.goto 0x80000408#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact se2147484608) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,Core.get_zero,hp];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x800003c2#32).getLsbD 0=false;decide) se2147484610 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v10 : c1.get 10=1#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h10,h20,h21,h23]
    have v12 : c1.get 12=1#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h10,h20,h21,h23]
    rw [exec_branch,v10,v12,show taken .ne 1#32 1#32=false by decide];simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x800003c6#32).getLsbD 0=false;decide) se2147484614 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v23 : c2.get 23=0#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h10,h20,h21,h23]
    rw [exec_branch,v23,Core.get_zero,show taken .ne 0#32 (0 : Word)=false by decide]
    simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x800003ca#32).getLsbD 0=false;decide) se2147484618 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v21 : c3.get 21=BitVec.ofNat 32 status := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h20,h21,h23]
    rw [exec_opimm,v21];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x800003ce#32).getLsbD 0=false;decide) se2147484622 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v21 : c4.get 21=BitVec.ofNat 32 status := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h20,h21,h23]
    rw [exec_opimm,v21];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x800003d2#32).getLsbD 0=false;decide) se2147484626 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v10 : c5.get 10=BitVec.ofNat 32 status+0xffffff34#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h20,h21,h23]
    rw [exec_op,Core.get_zero,v10];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x800003d6#32).getLsbD 0=false;decide) se2147484630 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v12 : c6.get 12=BitVec.ofNat 32 status+0xfffffed0#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h20,h21,h23]
    rw [exec_op,Core.get_zero,v12];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x800003da#32).getLsbD 0=false;decide) se2147484634 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    have v10 : c7.get 10=ResponseHeadBodyMath.not204 status := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h20,h21,h23]
    have v12 : c7.get 12=ResponseHeadBodyMath.not304 status := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h20,h21,h23]
    rw [exec_op,v10,v12];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine Quiet.step_of (by change (0x800003dc#32).getLsbD 0=false;decide) se2147484636 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 ram [],[]⟩
    have v10 : c8.get 10=SendBodyMath.flags status := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h20,h21,h23]
    rw [exec_opimm,v10];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine Quiet.step_of (by change (0x800003de#32).getLsbD 0=false;decide) se2147484638 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) ram 0 [] [] = ⟨.ok c10 ram [],[]⟩
    have v10 : c9.get 10=(SendBodyMath.flags status) <<< 31 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h20,h21,h23]
    rw [exec_opimm,v10];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine Quiet.step_of (by change (0x800003e0#32).getLsbD 0=false;decide) se2147484640 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) ram 0 [] [] = ⟨.ok c11 ram [],[]⟩
    have v10 : c10.get 10=SendBodyMath.mask status := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h20,h21,h23]
    have v20 : c10.get 20=body := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h20,h21,h23]
    rw [exec_op,v10,v20]
    change Observed.interp B img o (.done (c10.wr 10 (SendBodyMath.mask status &&& body) 0x800003e4#32)) ram 0 [] [] = _
    rw [SendBodyMath.length_value status body hhi hlo];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine Quiet.step_of (by change (0x800003e4#32).getLsbD 0=false;decide) se2147484644 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) ram 0 [] [] = ⟨.ok c12 ram [],[]⟩
    rw [exec_jal]
    change Observed.interp B img o (jump c11 (0x800003e4#32+36#32)) ram 0 [] [] = _
    rw [show 0x800003e4#32+36#32=0x80000408#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c12,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.single t11))))))))))),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h20,h21,h23]
  · simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h20,h21,h23]
  · intro reg h12 h10;simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h20,h21,h23,h12,h10]
end E5R.Thermostat.SendBodyPayload
