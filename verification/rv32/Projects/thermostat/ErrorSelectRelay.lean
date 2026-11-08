import Projects.thermostat.EncodeErrorCode
import Projects.thermostat.Memory
import Projects.thermostat.ParamMath
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ErrorSelectRelay
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (cap : Nat) (h8 : c.get 8=BitVec.ofNat 32 cap) (h12 : c.get 12=1#32) (hcap : 33≤cap) (hbound : cap<2^32)
    (hp : c.pc = 0x80001e5a#32) :
    ∃ d, DetSteps B img 9 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80001e8c#32 ∧
      d.get 11 = 0x80005bc7#32 ∧ d.get 12 = 25#32 ∧ d.get 9 = 404#32 ∧ d.get 8 = 25#32 ∧ (∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 9 → r ≠ 8 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x80001e5c#32
  let c2 := c1.wr 11 (1#32) 0x80001e5e#32
  let c3 := c2.goto 0x80001e62#32
  let c4 := c3.wr 11 (0x80006000#32) 0x80001e66#32
  let c5 := c4.wr 11 (0x80005bc7#32) 0x80001e6a#32
  let c6 := c5.wr 12 (25#32) 0x80001e6c#32
  let c7 := c6.wr 9 (404#32) 0x80001e70#32
  let c8 := c7.goto 0x80001e8a#32
  let c9 := c8.wr 8 (25#32) 0x80001e8c#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact ee2147491418) fun o => ?_
    have hv : c.get 12 = 1#32 := by simp [Core.wr_get_ne,Core.wr_get,h8,h12]
    rw [exec_branch,hv,Core.get_zero,show E5R.taken .eq (1#32) (0:Word) = false by decide]
    simp only [ite_true,ite_false]
    first | rfl | (rw [hp]; rfl)
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x80001e5c#32).getLsbD 0 = false;decide) ee2147491420 fun o => ?_
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp]; rfl)
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x80001e5e#32).getLsbD 0 = false;decide) ee2147491422 fun o => ?_
    have hv12 : c2.get 12 = 1#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h12]
    have hv11 : c2.get 11 = 1#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h12]
    rw [exec_branch,hv12,hv11,show E5R.taken .ne (1#32) 1#32 = false by decide]
    simp only [ite_true,ite_false]
    first | rfl | (rw [hp]; rfl)
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine detStep_of (by change (0x80001e62#32).getLsbD 0 = false;decide) ee2147491426 fun o => ?_
    rw [exec_lui];first | rfl | (rw [hp]; rfl)
  have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine detStep_of (by change (0x80001e66#32).getLsbD 0 = false;decide) ee2147491430 fun o => ?_
    have hv : c4.get 11 = 0x80006000#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h12]
    rw [exec_opimm,hv];first | rfl | (rw [hp]; rfl)
  have s5 : DetStep B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine detStep_of (by change (0x80001e6a#32).getLsbD 0 = false;decide) ee2147491434 fun o => ?_
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp]; rfl)
  have s6 : DetStep B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine detStep_of (by change (0x80001e6c#32).getLsbD 0 = false;decide) ee2147491436 fun o => ?_
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp]; rfl)
  have s7 : DetStep B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine detStep_of (by change (0x80001e70#32).getLsbD 0 = false;decide) ee2147491440 fun o => ?_
    have hv8 : c7.get 8 = BitVec.ofNat 32 cap := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h12]
    have hv12 : c7.get 12 = 25#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h12]
    have ht : E5R.taken .geu (BitVec.ofNat 32 cap) (25#32) = true := by
      change (!E5R.taken .ltu (BitVec.ofNat 32 cap) (BitVec.ofNat 32 25)) = true
      rw [ParamMath.ult cap 25 hbound (by decide),decide_eq_false (show ¬cap<25 by omega)];first | rfl | (rw [hp]; rfl)
    rw [exec_branch,hv8,hv12,ht]
    simp only [ite_true,ite_false]
    change interp B img o (jump c7 0x80001e8a#32) ram 0 [] = _
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp]; rfl)
  have s8 : DetStep B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine detStep_of (by change (0x80001e8a#32).getLsbD 0 = false;decide) ee2147491466 fun o => ?_
    have hv : c8.get 12 = 25#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h12]
    rw [exec_op,Core.get_zero,hv];simp only [alu,show (0:Word)=0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  refine ⟨c9,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.single s8)))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h12]
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h12]
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h12]
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h12]
  · intro r h11 h12 h9 h8
    simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h12,h11,h12,h9,h8]
end E5R.Thermostat.ErrorSelectRelay
