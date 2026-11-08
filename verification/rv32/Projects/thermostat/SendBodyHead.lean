import Projects.thermostat.SendCode
import Projects.thermostat.QuietRam
import Projects.thermostat.SendBodyMath
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.SendBodyHead
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (body : Word) (status : Nat) (hlo : 200≤status) (hhi : status≤599) (h10 : c.get 10=1#32) (h20 : c.get 20=body) (h21 : c.get 21=BitVec.ofNat 32 status) (h23 : c.get 23=1#32)
    (hp : c.pc=0x800003c0#32) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80000408#32 ∧
      d.get 12=1#32 ∧ d.get 10=0#32 ∧ (∀ r : Reg, r≠12 → r≠10 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 12 (1#32) 0x800003c2#32
  let c2 := c1.goto 0x800003c6#32
  let c3 := c2.goto 0x80000406#32
  let c4 := c3.wr 10 (0#32) 0x80000408#32
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
    have v23 : c2.get 23=1#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h10,h20,h21,h23]
    rw [exec_branch,v23,Core.get_zero,show taken .ne 1#32 (0 : Word)=true by decide]
    simp only [ite_true]
    rw [show c2.pc=0x800003c6#32 by rfl,show 0x800003c6#32+64#32=0x80000406#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80000406#32).getLsbD 0=false;decide) se2147484678 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  refine ⟨c4,.step t0 (.step t1 (.step t2 (.single t3))),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h20,h21,h23]
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h20,h21,h23]
  · intro reg h12 h10;simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h20,h21,h23,h12,h10]
end E5R.Thermostat.SendBodyHead
