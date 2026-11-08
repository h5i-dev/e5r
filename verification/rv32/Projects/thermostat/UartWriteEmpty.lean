import Projects.thermostat.UartWriteCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.UartWriteEmpty
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)  (h12 : c.get 12=0#32)
    (hp : c.pc=0x800007cc#32) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x8000081e#32 ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x8000081e#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact uw2147485644) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_branch,h12,Core.get_zero,show taken .eq 0#32 (0 : Word)=true by decide,hp]
    simp only [ite_true]
    change Observed.interp B img o (jump c (0x800007cc#32+82#32)) ram 0 [] [] = _
    rw [show 0x800007cc#32+82#32=0x8000081e#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c1,.single t0,rfl,?_ ,by rfl⟩
  · intro reg ;simp [c1,Core.wr_get_ne,Core.wr_get,h12]
end E5R.Thermostat.UartWriteEmpty
