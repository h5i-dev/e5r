import Projects.thermostat.EncodeErrorCode
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ErrorCall
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (len : Word) (h8 : c.get 8=len)
    (hp : c.pc = 0x80001e8c#32) :
    ∃ d, DetSteps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80005182#32 ∧
      d.get 12 = len ∧ d.get 1 = 0x80001e96#32 ∧ (∀ r : Reg, r ≠ 12 → r ≠ 1 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 12 (len) 0x80001e8e#32
  let c2 := c1.wr 1 (0x80004e8e#32) 0x80001e92#32
  let c3 := c2.wr 1 (0x80001e96#32) 0x80005182#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact ee2147491468) fun o => ?_
    rw [exec_op,Core.get_zero,h8,hp];simp only [alu,show (0:Word)=0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x80001e8e#32).getLsbD 0 = false;decide) ee2147491470 fun o => ?_
    rw [exec_auipc];first | rfl | (rw [hp]; rfl)
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x80001e92#32).getLsbD 0 = false;decide) ee2147491474 fun o => ?_
    have hv : c2.get 1=0x80004e8e#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_jalr,hv]
    change interp B img o (.done ((c2.set 1 0x80001e96#32).goto 0x80005182#32)) ram 0 [] = _
    first | rfl | (rw [hp]; rfl)
  refine ⟨c3,.step s0 (.step s1 (.single s2)),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
  · intro r h12 h1
    simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h12,h1]
end E5R.Thermostat.ErrorCall
