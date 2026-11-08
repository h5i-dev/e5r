import Projects.thermostat.WriteErrorCode
import Projects.thermostat.ParamMath
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.WriteErrorReturn
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (status : Word) (len cap : Nat) (h10 : c.get 10=status) (h11 : c.get 11=BitVec.ofNat 32 len)
    (h18 : c.get 18=BitVec.ofNat 32 cap) (hc : cap<2^32) (hl : len≤cap)
    (hp : c.pc = 0x80000664#32) :
    ∃ d, DetSteps B img 7 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x800005ac#32 ∧
      d.get 20 = status ∧ d.get 18 = BitVec.ofNat 32 len ∧ d.get 12 = 0x800056a8#32 ∧ d.get 10 = 16#32 ∧ (∀ r : Reg, r ≠ 20 → r ≠ 18 → r ≠ 12 → r ≠ 10 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 20 (status) 0x80000666#32
  let c2 := c1.goto 0x8000066a#32
  let c3 := c2.wr 18 (BitVec.ofNat 32 len) 0x8000066c#32
  let c4 := c3.wr 12 (0x80005000#32) 0x80000670#32
  let c5 := c4.wr 12 (0x800056a8#32) 0x80000674#32
  let c6 := c5.wr 10 (16#32) 0x80000676#32
  let c7 := c6.goto 0x800005ac#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact er2147485284) fun o => ?_
    have hv : c.get 10=status := by simp [Core.wr_get_ne,Core.wr_get,h10,h11,h18]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word)=0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x80000666#32).getLsbD 0 = false;decide) er2147485286 fun o => ?_
    have v18 : c1.get 18=BitVec.ofNat 32 cap := by simp [c1,Core.wr_get_ne,Core.wr_get,h10,h11,h18]
    have v11 : c1.get 11=BitVec.ofNat 32 len := by simp [c1,Core.wr_get_ne,Core.wr_get,h10,h11,h18]
    rw [exec_branch,v18,v11,ParamMath.ult cap len hc (by omega),decide_eq_false (show ¬cap<len by omega)]
    simp only [ite_false];first | rfl | (rw [hp]; rfl)
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x8000066a#32).getLsbD 0 = false;decide) er2147485290 fun o => ?_
    have hv : c2.get 11=BitVec.ofNat 32 len := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h18]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word)=0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine detStep_of (by change (0x8000066c#32).getLsbD 0 = false;decide) er2147485292 fun o => ?_
    rw [exec_lui];first | rfl | (rw [hp]; rfl)
  have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine detStep_of (by change (0x80000670#32).getLsbD 0 = false;decide) er2147485296 fun o => ?_
    have hv : c4.get 12=0x80005000#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h18]
    rw [exec_opimm,hv];first | rfl | (rw [hp]; rfl)
  have s5 : DetStep B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine detStep_of (by change (0x80000674#32).getLsbD 0 = false;decide) er2147485300 fun o => ?_
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp]; rfl)
  have s6 : DetStep B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine detStep_of (by change (0x80000676#32).getLsbD 0 = false;decide) er2147485302 fun o => ?_
    rw [exec_jal]
    change interp B img o (jump c6 (0x80000676#32+0xffffff36#32)) ram 0 [] = _
    rw [show (0x80000676#32+0xffffff36#32)=0x800005ac#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp]; rfl)
  refine ⟨c7,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.single s6)))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h18]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h18]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h18]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h18]
  · intro r h20 h18 h12 h10
    simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h18,h20,h18,h12,h10]
end E5R.Thermostat.WriteErrorReturn
