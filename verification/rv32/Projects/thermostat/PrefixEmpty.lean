import Projects.thermostat.WritePrefixCode
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.PrefixEmpty
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (h18 : c.get 18 = 0#32)
    (hp : c.pc = 0x80004e2e#32) :
    ∃ d, DetSteps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80004e4e#32 ∧
      d.get 10 = 0#32 ∧ (∀ r : Reg, r ≠ 10 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x80004e4c#32
  let c2 := c1.wr 10 (0#32) 0x80004e4e#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact wp2147503662) fun o => ?_
    have hv : c.get 18 = 0#32 := by simp [Core.wr_get_ne,Core.wr_get,h18]
    rw [exec_branch,hv,Core.get_zero,show E5R.taken .eq (0#32) (0 : Word) = true by decide]
    simp only [ite_true,ite_false]
    try simp only [hp]
    rw [jump_ok _ _ (by change (0x80004e4c#32).getLsbD 0 = false;decide)];first | rfl | (rw [hp]; rfl)
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x80004e4c#32).getLsbD 0 = false;decide) wp2147503692 fun o => ?_
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp]; rfl)
  refine ⟨c2,.step s0 (.single s1),rfl,?_ ,?_ ,by rfl⟩
  · simp [c2,c1,Core.wr_get_ne,Core.wr_get,h18]
  · intro r h10
    simp [c2,c1,Core.wr_get_ne,Core.wr_get,h18,h10]
end E5R.Thermostat.PrefixEmpty
