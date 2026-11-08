import Projects.thermostat.SendCode
import Projects.thermostat.QuietRam
import Projects.thermostat.HttpDecMath
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.SendClipBig
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)  (body : Nat) (hbody : body<2^32) (hcmp : 832<body) (h20 : c.get 20=832#32) (h11 : c.get 11=BitVec.ofNat 32 body)
    (hp : c.pc=0x8000039c#32) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800003a2#32 ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x800003a2#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact se2147484572) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v20 : c.get 20=832#32 := by simp [Core.wr_get_ne,Core.wr_get,h20,h11]
    have v11 : c.get 11=BitVec.ofNat 32 body := by simp [Core.wr_get_ne,Core.wr_get,h20,h11]
    rw [exec_branch,v20,v11,HttpDecMath.branch_ltu 832 body (by decide) hbody,show decide (832<body)=true by simp [hcmp]]
    simp only [ite_true]
    rw [hp,show 0x8000039c#32+6#32=0x800003a2#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c1,.single t0,rfl,?_ ,by rfl⟩
  · intro reg ;simp [c1,Core.wr_get_ne,Core.wr_get,h20,h11]
end E5R.Thermostat.SendClipBig
