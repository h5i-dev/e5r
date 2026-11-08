import Projects.thermostat.HttpDecCode
import Projects.thermostat.QuietRam
import Projects.thermostat.HttpDecTensMath
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HttpDecHundredsBig
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)  (n : Nat) (hn : n≤832) (h14 : c.get 14=BitVec.ofNat 32 (n/100)) (hbig : 100≤n)
    (hp : c.pc=0x800044e0#32) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x8000435c#32 ∧
      d.get 15=0#32 ∧ (∀ r : Reg, r≠15 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x800044e2#32
  let c2 := c1.wr 15 (0#32) 0x800044e4#32
  let c3 := c2.goto 0x8000435c#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact de2147501280) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_branch,h14,Core.get_zero,HttpDecTensMath.hundreds_test n hn,decide_eq_false (show ¬n<100 by omega)]
    simp only [Bool.false_eq_true,ite_false];rw [hp];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x800044e2#32).getLsbD 0=false;decide) de2147501282 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x800044e4#32).getLsbD 0=false;decide) de2147501284 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    rw [exec_jal]
    change Observed.interp B img o (jump c2 (0x800044e4#32+4294966904#32)) ram 0 [] [] = _
    rw [show 0x800044e4#32+4294966904#32=0x8000435c#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c3,.step t0 (.step t1 (.single t2)),rfl,?_ ,?_ ,by rfl⟩
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h14]
  · intro reg h15;simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h14,h15]
end E5R.Thermostat.HttpDecHundredsBig
