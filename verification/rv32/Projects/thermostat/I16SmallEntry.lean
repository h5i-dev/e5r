import Projects.thermostat.I16Code
import Projects.thermostat.ParamMath
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.I16SmallEntry
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (n : Nat) (hn : 10 ≤ n) (hb : n < 1000)
    (h14 : c.get 14 = BitVec.ofNat 32 n) (h16 : c.get 16 = 1000#32)
    (hp : c.pc = 0x80004e8a#32) :
    ∃ d, DetSteps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80004f04#32 ∧
      d.get 15 = 10#32 ∧ (∀ r : Reg, r ≠ 15 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x80004efe#32
  let c2 := c1.wr 15 (10#32) 0x80004f00#32
  let c3 := c2.goto 0x80004f04#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact di2147503754) fun o => ?_
    rw [exec_branch,h14,h16,ParamMath.ult n 1000 (by omega) (by decide),decide_eq_true hb,hp]
    simp only [ite_true]
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp]; rfl)
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x80004efe#32).getLsbD 0 = false;decide) di2147503870 fun o => ?_
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp]; rfl)
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x80004f00#32).getLsbD 0 = false;decide) di2147503872 fun o => ?_
    have hv0 : c2.get 14 = BitVec.ofNat 32 n := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h14,h16]
    have hv1 : c2.get 15 = 10#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h14,h16]
    rw [exec_branch,hv0,hv1,ParamMath.ult n 10 (by omega) (by decide),decide_eq_false (show ¬n < 10 by omega)]
    simp only [ite_false];first | rfl | (rw [hp]; rfl)
  refine ⟨c3,.step s0 (.step s1 (.single s2)),rfl,?_ ,?_ ,by rfl⟩
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h14,h16]
  · intro r h15
    simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h14,h16,h15]
end E5R.Thermostat.I16SmallEntry
