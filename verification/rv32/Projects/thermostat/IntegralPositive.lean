import Projects.thermostat.IntegralCode
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.IntegralPositive
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (fmt len : Word) (h19 : c.get 19 = fmt) (h9 : c.get 9 = len)
    (hm : Memory.Block B fmt 14) (ha : fmt.toNat%4 = 0)
    (hz : ramRead ram (fmt+8#32) .w = 0#32) (h11 : c.get 11 = 1#32)
    (hp : c.pc = 0x8000453c#32) :
    ∃ d, DetSteps B img 9 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x800045c6#32 ∧
      d.get 23 = 0#32 ∧ d.get 10 = 0#32 ∧ d.get 11 = 0xffffffff#32 ∧ d.get 22 = 0xffffffff#32 ∧ d.get 25 = len ∧ (∀ r : Reg, r ≠ 23 → r ≠ 10 → r ≠ 11 → r ≠ 22 → r ≠ 25 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x8000453e#32
  let c2 := c1.wr 23 (0#32) 0x80004542#32
  let c3 := c2.wr 10 (0#32) 0x80004546#32
  let c4 := c3.wr 10 (0#32) 0x80004548#32
  let c5 := c4.wr 11 (0xffffffff#32) 0x8000454c#32
  let c6 := c5.wr 22 (0xffffffff#32) 0x80004550#32
  let c7 := c6.wr 25 (len) 0x80004554#32
  let c8 := c7.wr 10 (0#32) 0x80004558#32
  let c9 := c8.goto 0x800045c6#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact pi2147501372) fun o => ?_
    have hv : c.get 11 = 1#32 := by simp [Core.wr_get_ne,Core.wr_get,h19,h9,h11]
    rw [exec_branch,hv,Core.get_zero,show E5R.taken .eq (1#32) (0 : Word) = false by decide]
    simp only [ite_true,ite_false]
    first | rfl | (rw [hp]; rfl)
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x8000453e#32).getLsbD 0 = false;decide) pi2147501374 fun o => ?_
    have hv : c1.get 19 = fmt := by simp [c1,Core.wr_get_ne,Core.wr_get,h19,h9,h11]
    rw [exec_load,hv,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned fmt 2 ha) (Memory.block_access hm (off := 8) (by decide) (by decide)),hz];first | rfl | (rw [hp]; rfl)
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x80004542#32).getLsbD 0 = false;decide) pi2147501378 fun o => ?_
    have hv : c2.get 23 = 0#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h19,h9,h11]
    rw [exec_opimm,hv];first | rfl | (rw [hp]; rfl)
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine detStep_of (by change (0x80004546#32).getLsbD 0 = false;decide) pi2147501382 fun o => ?_
    have hv : c3.get 10 = 0#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h9,h11]
    rw [exec_opimm,hv];first | rfl | (rw [hp]; rfl)
  have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine detStep_of (by change (0x80004548#32).getLsbD 0 = false;decide) pi2147501384 fun o => ?_
    have hv : c4.get 10 = 0#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h9,h11]
    rw [exec_opimm,hv];first | rfl | (rw [hp]; rfl)
  have s5 : DetStep B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine detStep_of (by change (0x8000454c#32).getLsbD 0 = false;decide) pi2147501388 fun o => ?_
    have hv : c5.get 11 = 0xffffffff#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h9,h11]
    rw [exec_opimm,hv];first | rfl | (rw [hp]; rfl)
  have s6 : DetStep B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine detStep_of (by change (0x80004550#32).getLsbD 0 = false;decide) pi2147501392 fun o => ?_
    have hv0 : c6.get 10 = 0#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h9,h11]
    have hv1 : c6.get 9 = len := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h9,h11]
    rw [exec_op,hv0,hv1]
    simp only [alu,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  have s7 : DetStep B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine detStep_of (by change (0x80004554#32).getLsbD 0 = false;decide) pi2147501396 fun o => ?_
    have hv : c7.get 23 = 0#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h9,h11]
    rw [exec_opimm,hv];first | rfl | (rw [hp]; rfl)
  have s8 : DetStep B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine detStep_of (by change (0x80004558#32).getLsbD 0 = false;decide) pi2147501400 fun o => ?_
    have hv : c8.get 10 = 0#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h9,h11]
    rw [exec_branch,hv,Core.get_zero,show E5R.taken .ge (0#32) (0 : Word) = true by decide]
    simp only [ite_true,ite_false]
    try simp only [hp]
    rw [jump_ok _ _ (by change (0x800045c6#32).getLsbD 0 = false;decide)];first | rfl | (rw [hp]; rfl)
  refine ⟨c9,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.single s8)))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h9,h11]
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h9,h11]
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h9,h11]
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h9,h11]
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h9,h11]
  · intro r h23 h10 h11 h22 h25
    simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h9,h11,h23,h10,h11,h22,h25]
end E5R.Thermostat.IntegralPositive
