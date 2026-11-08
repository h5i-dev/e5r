import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadChunkedGuard1
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (remaining : Word) (h11 : c.get 11=remaining) (ht : taken .eq remaining 1#32=false) (h12 : c.get 12=1#32)
    (hp : c.pc=0x800032fe#32) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80003302#32 ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x80003302#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147496702) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v11 : c.get 11=remaining := by simp [Core.wr_get_ne,Core.wr_get,h11,h12]
    have v12 : c.get 12=1#32 := by simp [Core.wr_get_ne,Core.wr_get,h11,h12]
    rw [exec_branch,v11,v12,ht];first | rfl | (rw [hp];rfl)
  refine ⟨c1,.single t0,rfl,?_ ,by rfl⟩
  · intro reg ;simp [c1,Core.wr_get_ne,Core.wr_get,h11,h12]
end E5R.Thermostat.HeadChunkedGuard1
