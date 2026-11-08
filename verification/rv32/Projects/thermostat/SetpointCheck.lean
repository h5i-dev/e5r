import Projects.thermostat.Arithmetic

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.SetpointCheck
open E5R E5R.Thermostat

theorem decision (dc : BitVec 16) :
    taken .geu (Arithmetic.biased dc) 65285#32 = decide (50 ≤ dc.toInt ∧ dc.toInt ≤ 300) := by
  have he := Arithmetic.setpoint_range dc
  by_cases h : 50 ≤ dc.toInt ∧ dc.toInt ≤ 300
  · have hl : ¬(Arithmetic.biased dc).toNat < 65285 := by have := he.mpr h;omega
    simp [taken,BitVec.ult,h,hl]
  · have hl : (Arithmetic.biased dc).toNat < 65285 := by
      have hn : ¬65285 ≤ (Arithmetic.biased dc).toNat := fun hn => h (he.mp hn)
      omega
    simp [taken,BitVec.ult,h,hl]

/-- The actual five instructions implementing the biased unsigned range check. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (dc : BitVec 16)
    (hp : c.pc = 0x800000e0) (hv : c.get 8 = dc.signExtend 32) :
    ∃ d, DetSteps B img 5 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x800000ee ∧
      taken .geu (d.get 11) (d.get 13) = decide (50 ≤ dc.toInt ∧ dc.toInt ≤ 300) ∧
      (∀ r : Reg, r ≠ 11 → r ≠ 13 → d.get r = c.get r) ∧ d.sameCsr c := by
  let v := dc.signExtend 32 + 0xfffffed3#32
  let c1 := c.wr 11 v 0x800000e4
  let c2 := c1.wr 11 (v <<< 16) 0x800000e6
  let c3 := c2.wr 13 65536#32 0x800000e8
  let c4 := c3.wr 11 (Arithmetic.biased dc) 0x800000ea
  let d := c4.wr 13 65285#32 0x800000ee
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact d2147483872) fun o => ?_
    rw [exec_opimm,hv,hp]
    rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    have h : c1.get 11 = v := by simp [c1,Core.wr_get]
    refine detStep_of (by change (0x800000e4 : Word).getLsbD 0 = false;decide) d2147483876 fun o => ?_
    rw [exec_opimm,h]
    rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x800000e6 : Word).getLsbD 0 = false;decide) d2147483878 fun o => ?_
    rw [exec_lui]
    rfl
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    have h : c3.get 11 = v <<< 16 := by simp [c3,c2,Core.wr_get]
    refine detStep_of (by change (0x800000e8 : Word).getLsbD 0 = false;decide) d2147483880 fun o => ?_
    rw [exec_opimm,h]
    rfl
  have s4 : DetStep B img ⟨c4,ram⟩ ⟨d,ram⟩ := by
    have h : c4.get 13 = 65536#32 := by simp [c4,c3,Core.wr_get]
    refine detStep_of (by change (0x800000ea : Word).getLsbD 0 = false;decide) d2147483882 fun o => ?_
    rw [exec_opimm,h]
    rfl
  refine ⟨d,.step s0 (.step s1 (.step s2 (.step s3 (.single s4)))),rfl,?_,?_,?_⟩
  · have h11 : d.get 11 = Arithmetic.biased dc := by simp [d,c4,Core.wr_get]
    have h13 : d.get 13 = 65285#32 := by simp [d,Core.wr_get]
    rw [h11,h13]
    exact decision dc
  · intro r h11 h13
    simp [d,c4,c3,c2,c1,Core.wr_get_ne,h11,h13]
  · exact (Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans
      ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans (Core.sameCsr_wr _ _ _ _))))

theorem branch (B : Board) (c : Core) (ram : Word → BitVec 8) (dc : BitVec 16)
    (hp : c.pc = 0x800000ee)
    (ht : taken .geu (c.get 11) (c.get 13) = decide (50 ≤ dc.toInt ∧ dc.toInt ≤ 300)) :
    DetStep B img ⟨c,ram⟩ ⟨c.goto (if 50 ≤ dc.toInt ∧ dc.toInt ≤ 300 then 0x8000027a else 0x800000f2),ram⟩ := by
  refine detStep_of (by rw [hp];decide) (by rw [hp];exact d2147483886) fun o => ?_
  rw [exec_branch,ht]
  by_cases h : 50 ≤ dc.toInt ∧ dc.toInt ≤ 300
  · rw [show decide (50 ≤ dc.toInt ∧ dc.toInt ≤ 300) = true by simp [h]]
    simp only [ite_eq_left (Eq.refl true),ite_eq_left h]
    have he : c.pc + 396#32 = 0x8000027a#32 := by rw [hp];decide +kernel
    rw [he,jump_ok c 0x8000027a#32 (by decide)]
    rfl
  · rw [show decide (50 ≤ dc.toInt ∧ dc.toInt ≤ 300) = false by simp [h]]
    simp only [Bool.false_eq_true,ite_false,ite_eq_right h]
    rw [hp]
    rfl

end E5R.Thermostat.SetpointCheck
