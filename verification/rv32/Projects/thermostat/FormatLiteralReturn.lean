import Projects.thermostat.FormatEngineCode
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.FormatLiteralReturn
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (src : Word) (len : Nat)
    (h10 : c.get 10 = 0#32) (h20 : c.get 20 = src) (h21 : c.get 21 = BitVec.ofNat 32 len)
    (hp : c.pc = 0x800049fc#32) :
    ∃ d, DetSteps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x800049de#32 ∧
      d.get 20 = src+BitVec.ofNat 32 len ∧ (∀ r : Reg, r ≠ 20 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x80004a00#32
  let c2 := c1.wr 20 (src+BitVec.ofNat 32 len) 0x80004a02#32
  let c3 := c2.goto 0x800049de#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact fe2147502588) fun o => ?_
    have hv : c.get 10 = 0#32 := by simp [Core.wr_get_ne,Core.wr_get,h10,h20,h21]
    rw [exec_branch,hv,Core.get_zero,show E5R.taken .ne (0#32) (0 : Word) = false by decide]
    simp only [ite_true,ite_false]
    first | rfl | (rw [hp]; rfl)
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x80004a00#32).getLsbD 0 = false;decide) fe2147502592 fun o => ?_
    have hv0 : c1.get 20 = src := by simp [c1,Core.wr_get_ne,Core.wr_get,h10,h20,h21]
    have hv1 : c1.get 21 = BitVec.ofNat 32 len := by simp [c1,Core.wr_get_ne,Core.wr_get,h10,h20,h21]
    rw [exec_op,hv0,hv1];first | rfl | (rw [hp]; rfl)
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x80004a02#32).getLsbD 0 = false;decide) fe2147502594 fun o => ?_
    rw [exec_jal]
    change interp B img o (jump c2 (0x80004a02#32+0xffffffdc#32)) ram 0 [] = _
    rw [show 0x80004a02#32+0xffffffdc#32 = 0x800049de#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp]; rfl)
  refine ⟨c3,.step s0 (.step s1 (.single s2)),rfl,?_ ,?_ ,by rfl⟩
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h20,h21]
  · intro r h20
    simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h20,h21,h20]
end E5R.Thermostat.FormatLiteralReturn
