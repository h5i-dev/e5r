import Projects.thermostat.KernelCode
import Projects.thermostat.Memory

set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.RelayCheck
open E5R E5R.Thermostat

theorem decision (idx : BitVec 8) :
    taken .geu 3#32 (BitVec.ofNat 32 idx.toNat) = decide (idx.toNat < 4) := by
  have hb := idx.isLt
  have hn : (BitVec.ofNat 32 idx.toNat).toNat = idx.toNat := by rw [BitVec.toNat_ofNat];omega
  unfold taken BitVec.ult
  rw [hn]
  change (!decide (3 < idx.toNat)) = decide (idx.toNat < 4)
  by_cases h : idx.toNat < 4
  · have hn : ¬3 < idx.toNat := by omega
    simp [h,hn]
  · have hn : 3 < idx.toNat := by omega
    simp [h,hn]

/-- Exact index load and bound branch; no out-of-range index reaches the patch. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (idx : BitVec 8)
    (hp : c.pc = 0x80000104) (hr : B.inRam (c.get 13+1#32) 1 = true)
    (hi : ram (c.get 13+1#32) = idx) :
    ∃ d, DetSteps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = (if idx.toNat < 4 then 0x800001be else 0x8000010e) ∧
      d.get 11 = BitVec.ofNat 32 idx.toNat ∧
      (∀ r : Reg, r ≠ 11 → r ≠ 14 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 11 (BitVec.ofNat 32 idx.toNat) 0x80000108
  let c2 := c1.wr 14 3#32 0x8000010a
  let d := c2.goto (if idx.toNat < 4 then 0x800001be else 0x8000010e)
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact d2147483908) fun o => ?_
    rw [exec_load,interp_load_ram (B := B) (img := img) (w := .b) (a := c.get 13+1#32)
      o (by exact Nat.mod_one _) hr,Memory.load_byte]
    dsimp only
    rw [hi,hp]
    rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x80000108 : Word).getLsbD 0 = false;decide) d2147483912 fun o => ?_
    rw [exec_opimm]
    rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨d,ram⟩ := by
    have h11 : c2.get 11 = BitVec.ofNat 32 idx.toNat := by simp [c2,c1,Core.wr_get]
    have h14 : c2.get 14 = 3#32 := by simp [c2,Core.wr_get]
    refine detStep_of (by change (0x8000010a : Word).getLsbD 0 = false;decide) d2147483914 fun o => ?_
    rw [exec_branch,h11,h14,decision]
    by_cases h : idx.toNat < 4
    · rw [show decide (idx.toNat < 4) = true by simp [h]]
      simp only [ite_eq_left (Eq.refl true),ite_eq_left h]
      rw [jump_ok _ _ (by change (0x800001be : Word).getLsbD 0 = false;decide)]
      simp only [d,ite_eq_left h,ite_true]
      rfl
    · rw [show decide (idx.toNat < 4) = false by simp [h]]
      simp only [d,Bool.false_eq_true,ite_false,ite_eq_right h]
      rfl
  refine ⟨d,.step s0 (.step s1 (.single s2)),rfl,?_,?_,?_⟩
  · simp [d,c2,c1,Core.wr_get]
  · intro r h11 h14;simp [d,c2,c1,Core.wr_get_ne,h11,h14]
  · exact (Core.sameCsr_goto _ _).trans ((Core.sameCsr_wr _ _ _ _).trans (Core.sameCsr_wr _ _ _ _))

end E5R.Thermostat.RelayCheck
