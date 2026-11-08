import Projects.thermostat.ResponseHeadCode
import Projects.thermostat.QuietRam
import Projects.thermostat.ResponseHeadMath
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ResponseHeadGuard
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)  (status : Nat) (hu16 : status<65536) (h12 : c.get 12=BitVec.ofNat 32 status) (hv : 100≤status ∧ status≤599)
    (hp : c.pc=0x80003e4e#32) :
    ∃ d, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80003e66#32 ∧
      d.get 17=ResponseHeadMath.folded status ∧ d.get 5=65036#32 ∧ (∀ r : Reg, r≠17 → r≠5 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 17 (BitVec.ofNat 32 status+0xfffffda8#32) 0x80003e52#32
  let c2 := c1.wr 17 (((BitVec.ofNat 32 status+0xfffffda8#32) <<< 16)) 0x80003e54#32
  let c3 := c2.wr 5 (65536#32) 0x80003e56#32
  let c4 := c3.wr 17 (ResponseHeadMath.folded status) 0x80003e5a#32
  let c5 := c4.wr 5 (65036#32) 0x80003e5e#32
  let c6 := c5.goto 0x80003e66#32
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
    rw [exec_branch,v17,v5,ResponseHeadMath.range_guard status hu16,decide_eq_true hv]
    simp only [ite_true]
    rw [show c5.pc=0x80003e5e#32 by rfl,show 0x80003e5e#32+8#32=0x80003e66#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c6,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.single t5))))),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12]
  · intro reg h17 h5;simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h17,h5]
end E5R.Thermostat.ResponseHeadGuard
