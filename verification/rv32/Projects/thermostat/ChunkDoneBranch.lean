import Projects.thermostat.SuccessNextCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ChunkDoneBranch
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)  (h10 : c.get 10=2#32) (h18 : c.get 18=2#32)
    (hp : c.pc=0x8000106c#32) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80001070#32 ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x80001070#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact xn2147487852) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_branch,h10,h18,show taken .ne 2#32 2#32=false by decide +kernel,hp];first | rfl | (rw [hp];rfl)
  refine ⟨c1,.single t0,rfl,?_ ,by rfl⟩
  · intro reg ;simp [c1,Core.wr_get_ne,Core.wr_get,h10,h18]
end E5R.Thermostat.ChunkDoneBranch
