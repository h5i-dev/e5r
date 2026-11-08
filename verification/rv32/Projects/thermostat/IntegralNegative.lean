import Projects.thermostat.IntegralCode
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.IntegralNegative
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (fmt len : Word) (h19 : c.get 19 = fmt) (h9 : c.get 9 = len)
    (hm : Memory.Block B fmt 14) (ha : fmt.toNat%4 = 0)
    (hz : ramRead ram (fmt+8#32) .w = 0#32) (h11 : c.get 11 = 0#32)
    (hp : c.pc = 0x8000453c#32) :
    ∃ d, DetSteps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x800045c6#32 ∧
      d.get 23 = 0#32 ∧ d.get 25 = len+1#32 ∧ d.get 22 = 45#32 ∧ d.get 10 = 0#32 ∧ (∀ r : Reg, r ≠ 23 → r ≠ 25 → r ≠ 22 → r ≠ 10 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x800045b2#32
  let c2 := c1.wr 23 (0#32) 0x800045b6#32
  let c3 := c2.wr 25 (len+1#32) 0x800045ba#32
  let c4 := c3.wr 22 (45#32) 0x800045be#32
  let c5 := c4.wr 10 (0#32) 0x800045c2#32
  let c6 := c5.goto 0x800045c6#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact pi2147501372) fun o => ?_
    have hv : c.get 11 = 0#32 := by simp [Core.wr_get_ne,Core.wr_get,h19,h9,h11]
    rw [exec_branch,hv,Core.get_zero,show E5R.taken .eq (0#32) (0 : Word) = true by decide]
    simp only [ite_true,ite_false]
    try simp only [hp]
    rw [jump_ok _ _ (by change (0x800045b2#32).getLsbD 0 = false;decide)];first | rfl | (rw [hp]; rfl)
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x800045b2#32).getLsbD 0 = false;decide) pi2147501490 fun o => ?_
    have hv : c1.get 19 = fmt := by simp [c1,Core.wr_get_ne,Core.wr_get,h19,h9,h11]
    rw [exec_load,hv,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned fmt 2 ha) (Memory.block_access hm (off := 8) (by decide) (by decide)),hz];first | rfl | (rw [hp]; rfl)
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x800045b6#32).getLsbD 0 = false;decide) pi2147501494 fun o => ?_
    have hv : c2.get 9 = len := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h19,h9,h11]
    rw [exec_opimm,hv];first | rfl | (rw [hp]; rfl)
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine detStep_of (by change (0x800045ba#32).getLsbD 0 = false;decide) pi2147501498 fun o => ?_
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp]; rfl)
  have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine detStep_of (by change (0x800045be#32).getLsbD 0 = false;decide) pi2147501502 fun o => ?_
    have hv : c4.get 23 = 0#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h9,h11]
    rw [exec_opimm,hv];first | rfl | (rw [hp]; rfl)
  have s5 : DetStep B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine detStep_of (by change (0x800045c2#32).getLsbD 0 = false;decide) pi2147501506 fun o => ?_
    have hv : c5.get 10 = 0#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h9,h11]
    rw [exec_branch,hv,Core.get_zero,show E5R.taken .lt (0#32) (0 : Word) = false by decide]
    simp only [ite_true,ite_false]
    first | rfl | (rw [hp]; rfl)
  refine ⟨c6,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.single s5))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h9,h11]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h9,h11]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h9,h11]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h9,h11]
  · intro r h23 h25 h22 h10
    simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h9,h11,h23,h25,h22,h10]
end E5R.Thermostat.IntegralNegative
