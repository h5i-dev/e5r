import Projects.thermostat.FormatEngineCode
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.FormatArgumentReturn
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (idx : Nat) (h10 : c.get 10 = 0#32) (h24 : c.get 24 = BitVec.ofNat 32 idx)
    (hp : c.pc = 0x800049d8#32) :
    ∃ d, DetSteps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x800049de#32 ∧
      d.get 24 = BitVec.ofNat 32 (idx+1) ∧ (∀ r : Reg, r ≠ 24 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x800049dc#32
  let c2 := c1.wr 24 (BitVec.ofNat 32 (idx+1)) 0x800049de#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact fe2147502552) fun o => ?_
    have hv : c.get 10 = 0#32 := by simp [Core.wr_get_ne,Core.wr_get,h10,h24]
    rw [exec_branch,hv,Core.get_zero,show E5R.taken .ne (0#32) (0 : Word) = false by decide]
    simp only [ite_true,ite_false]
    first | rfl | (rw [hp]; rfl)
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x800049dc#32).getLsbD 0 = false;decide) fe2147502556 fun o => ?_
    have hv : c1.get 24 = BitVec.ofNat 32 idx := by simp [c1,Core.wr_get_ne,Core.wr_get,h10,h24]
    rw [exec_opimm,hv]
    change interp B img o (.done (c1.wr 24 ((BitVec.ofNat 32 idx)+1#32) 0x800049de#32)) ram 0 [] = _
    rw [←BitVec.ofNat_add];first | rfl | (rw [hp]; rfl)
  refine ⟨c2,.step s0 (.single s1),rfl,?_ ,?_ ,by rfl⟩
  · simp [c2,c1,Core.wr_get_ne,Core.wr_get,h10,h24]
  · intro r h24
    simp [c2,c1,Core.wr_get_ne,Core.wr_get,h10,h24,h24]
end E5R.Thermostat.FormatArgumentReturn
