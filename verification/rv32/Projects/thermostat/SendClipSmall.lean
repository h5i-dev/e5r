import Projects.thermostat.SendCode
import Projects.thermostat.QuietRam
import Projects.thermostat.HttpDecMath
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.SendClipSmall
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)  (body : Nat) (hbody : body<2^32) (hcmp : ¬832<body) (h20 : c.get 20=832#32) (h11 : c.get 11=BitVec.ofNat 32 body)
    (hp : c.pc=0x8000039c#32) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800003a2#32 ∧
      d.get 20=BitVec.ofNat 32 body ∧ (∀ r : Reg, r≠20 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x800003a0#32
  let c2 := c1.wr 20 (BitVec.ofNat 32 body) 0x800003a2#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact se2147484572) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v20 : c.get 20=832#32 := by simp [Core.wr_get_ne,Core.wr_get,h20,h11]
    have v11 : c.get 11=BitVec.ofNat 32 body := by simp [Core.wr_get_ne,Core.wr_get,h20,h11]
    rw [exec_branch,v20,v11,HttpDecMath.branch_ltu 832 body (by decide) hbody,show decide (832<body)=false by simp [hcmp]]
    simp only [Bool.false_eq_true,ite_false];rw [hp];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x800003a0#32).getLsbD 0=false;decide) se2147484576 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v11 : c1.get 11=BitVec.ofNat 32 body := by simp [c1,Core.wr_get_ne,Core.wr_get,h20,h11]
    rw [exec_op,Core.get_zero,v11,(show alu .add (0 : Word) (BitVec.ofNat 32 body)=BitVec.ofNat 32 body from BitVec.zero_add _)];first | rfl | (rw [hp];rfl)
  refine ⟨c2,.step t0 (.single t1),rfl,?_ ,?_ ,by rfl⟩
  · simp [c2,c1,Core.wr_get_ne,Core.wr_get,h20,h11]
  · intro reg h20;simp [c2,c1,Core.wr_get_ne,Core.wr_get,h20,h11,h20]
end E5R.Thermostat.SendClipSmall
