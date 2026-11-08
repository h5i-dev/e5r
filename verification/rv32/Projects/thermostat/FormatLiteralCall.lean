import Projects.thermostat.FormatEngineCode
import Projects.thermostat.FormatBits
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.FormatLiteralCall
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (obj desc : Word) (len : Nat) (hn : len < 16)
    (h19 : c.get 19 = obj) (h12 : c.get 12 = desc) (h21 : c.get 21 = BitVec.ofNat 32 len)
    (h22 : c.get 22 = 0x800022a0#32)
    (hp : c.pc = 0x800049e8#32) :
    ∃ d, DetSteps B img 7 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x800022a0#32 ∧
      d.get 10 = obj ∧ d.get 20 = desc+1#32 ∧ d.get 11 = desc+1#32 ∧ d.get 12 = BitVec.ofNat 32 len ∧ d.get 1 = 0x800049fc#32 ∧ (∀ r : Reg, r ≠ 10 → r ≠ 20 → r ≠ 11 → r ≠ 12 → r ≠ 1 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 ((BitVec.ofNat 32 len) <<< 24) 0x800049ec#32
  let c2 := c1.wr 20 (desc+1#32) 0x800049f0#32
  let c3 := c2.goto 0x800049f4#32
  let c4 := c3.wr 10 (obj) 0x800049f6#32
  let c5 := c4.wr 11 (desc+1#32) 0x800049f8#32
  let c6 := c5.wr 12 (BitVec.ofNat 32 len) 0x800049fa#32
  let c7 := c6.wr 1 (0x800049fc#32) 0x800022a0#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact fe2147502568) fun o => ?_
    rw [exec_opimm,h21,hp];first | rfl | (rw [hp]; rfl)
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x800049ec#32).getLsbD 0 = false;decide) fe2147502572 fun o => ?_
    have hv : c1.get 12 = desc := by simp [c1,Core.wr_get_ne,Core.wr_get,h19,h12,h21,h22]
    rw [exec_opimm,hv];first | rfl | (rw [hp]; rfl)
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x800049f0#32).getLsbD 0 = false;decide) fe2147502576 fun o => ?_
    have hv : c2.get 10 = (BitVec.ofNat 32 len) <<< 24 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h19,h12,h21,h22]
    rw [exec_branch,hv,Core.get_zero,FormatBits.literal_nonnegative len hn]
    simp only [ite_false];first | rfl | (rw [hp]; rfl)
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine detStep_of (by change (0x800049f4#32).getLsbD 0 = false;decide) fe2147502580 fun o => ?_
    have hv : c3.get 19 = obj := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h12,h21,h22]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine detStep_of (by change (0x800049f6#32).getLsbD 0 = false;decide) fe2147502582 fun o => ?_
    have hv : c4.get 20 = desc+1#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h12,h21,h22]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  have s5 : DetStep B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine detStep_of (by change (0x800049f8#32).getLsbD 0 = false;decide) fe2147502584 fun o => ?_
    have hv : c5.get 21 = BitVec.ofNat 32 len := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h12,h21,h22]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  have s6 : DetStep B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine detStep_of (by change (0x800049fa#32).getLsbD 0 = false;decide) fe2147502586 fun o => ?_
    have hv : c6.get 22 = 0x800022a0#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h12,h21,h22]
    rw [exec_jalr,hv,BitVec.add_zero]
    change interp B img o (jump (c6.set 1 0x800049fc#32) (0x800022a0#32 &&& ~~~1)) ram 0 [] = _
    rw [show 0x800022a0#32 &&& ~~~1 = 0x800022a0#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp]; rfl)
  refine ⟨c7,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.single s6)))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h12,h21,h22]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h12,h21,h22]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h12,h21,h22]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h12,h21,h22]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h12,h21,h22]
  · intro r h10 h20 h11 h12 h1
    simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h12,h21,h22,h10,h20,h11,h12,h1]
end E5R.Thermostat.FormatLiteralCall
