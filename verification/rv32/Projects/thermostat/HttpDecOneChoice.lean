import Projects.thermostat.HttpDecCode
import Projects.thermostat.QuietRam
import Projects.thermostat.HttpDecTensMath
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HttpDecOneChoice
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)  (n : Nat) (hn : n≤832) (h16 : c.get 16=BitVec.ofNat 32 (n/10)) (hone : n<10)
    (hp : c.pc=0x8000450e#32) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800043a6#32 ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x80004512#32
  let c2 := c1.goto 0x800043a6#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact de2147501326) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_branch,h16,Core.get_zero,HttpDecTensMath.tens_test n hn,decide_eq_false (show ¬10≤n by omega)]
    simp only [Bool.false_eq_true,ite_false];rw [hp];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80004512#32).getLsbD 0=false;decide) de2147501330 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    rw [exec_jal]
    change Observed.interp B img o (jump c1 (0x80004512#32+4294966932#32)) ram 0 [] [] = _
    rw [show 0x80004512#32+4294966932#32=0x800043a6#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c2,.step t0 (.single t1),rfl,?_ ,by rfl⟩
  · intro reg ;simp [c2,c1,Core.wr_get_ne,Core.wr_get,h16]
end E5R.Thermostat.HttpDecOneChoice
