import Projects.thermostat.Proof
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat
open E5R
theorem heater_full_contract (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80000036) (hm : c.get 10 = 0#32 ∨ c.get 10 = 1#32 ∨ c.get 10 = 2#32) :
    ∃ n d, n ≤ 8 ∧ DetSteps B img n ⟨c, ram⟩ ⟨d, ram⟩ ∧
      d.pc = c.get 1 &&& ~~~1 ∧ d.get 10 = spec (c.get 10) (c.get 11) (c.get 12) ∧
      (∀ r : Reg, r ≠ 10 → r ≠ 13 → d.get r = c.get r) ∧ d.sameCsr c := by
  by_cases ht : (c.get 11).slt 350#32 = true
  · have hc : (349#32).slt (c.get 11) = false := by rw [cmp, ht]; rfl
    rcases hm with hm | hm | hm
    all_goals
      let n : Nat := if c.get 10 = 0#32 then 4 else if c.get 10 = 1#32 then 7 else 8
      have hr : ∃ d, run img n c = some d := by
        simp [n, run, hp, i0, i1, i2, i3, i4, i5, i6, i7, i8, i9,
          exec_opimm, exec_op, exec_branch, exec_jalr, alu, taken, jump,
          Core.wr, Core.goto, Core.get_set, Core.get_zero, hm, hc]
      obtain ⟨d, hr⟩ := hr
      refine ⟨n, d, by simp [n, hm], run_sound hr ram, ?_⟩
      simp [n, run, hp, i0, i1, i2, i3, i4, i5, i6, i7, i8, i9,
        exec_opimm, exec_op, exec_branch, exec_jalr, alu, taken, jump,
        Core.wr, Core.goto, Core.get_set, Core.get_zero, hm, hc] at hr
      subst d
      refine ⟨rfl, ?_, ?_, rfl⟩
      · simp [Core.get_set, hm, spec, ht]
      · intro r h10 h13
        simp [Core.get_set, Core.get, Core.set, h10, h13]
  · have ht' : (c.get 11).slt 350#32 = false := Bool.eq_false_iff.mpr ht
    have hc : (349#32).slt (c.get 11) = true := by rw [cmp, ht']; rfl
    have hr : ∃ d, run img 4 c = some d := by
      simp [run, hp, i0, i1, i2, i3, i4, i5, i6, i7, i8, i9,
        exec_opimm, exec_op, exec_branch, exec_jalr, alu, taken, jump,
        Core.wr, Core.goto, Core.get_set, Core.get_zero, hc]
    obtain ⟨d, hr⟩ := hr
    refine ⟨4, d, by decide, run_sound hr ram, ?_⟩
    simp [run, hp, i0, i1, i2, i3, i4, i5, i6, i7, i8, i9,
      exec_opimm, exec_op, exec_branch, exec_jalr, alu, taken, jump,
      Core.wr, Core.goto, Core.get_set, Core.get_zero, hc] at hr
    subst d
    refine ⟨rfl, ?_, ?_, rfl⟩
    · simp [Core.get_set, spec, ht']
    · intro r h10 h13
      simp [Core.get_set, Core.get, Core.set, h10, h13]


end E5R.Thermostat
