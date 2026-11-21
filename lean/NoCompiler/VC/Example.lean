import NoCompiler.VC.Tactic

/-
A loop through cut points, milestone 4c: each cut point's segment is run by
`vc_run` (kernel-checked), and `Reach.cutpoints` composes them. What is left
after `vc_run` is the segment's end state as data, and the successors' goals
over the denotations of its symbolic values (here closed by hand; automating
that is the next step).
-/
namespace NoCompiler.VC.M.Example

/-- `loop: addi a0, a0, -1; bne a0, zero, loop`, then `ret`, at 0x1000. -/
def segs : List (List (BitVec 32)) := [[0xfff50513#32, 0xfe051ee3#32], [0x00008067#32]]
def D : Dom := [(0x1000#64, 12)]

/-- Counts a0 down to zero, then returns. -/
theorem countdown {P : Perm} (s : State) (hpc : s.pc = 0x1000#64) (ha : s.reg 10 ≠ 0)
    (hra : aligned (s.reg 1 &&& ~~~1) 4) (hx : s.exit = none) :
    Reach (Code.ofSegs 0x1000#64 segs) P D (fun s' => s'.reg 10 = 0 ∧ s'.pc = s.reg 1 &&& ~~~1) s := by
  refine Reach.cutpoints
    (fun pc u => u.exit = none ∧ u.reg 1 = s.reg 1 ∧
      ((pc = 0x1000#64 ∧ u.reg 10 ≠ 0) ∨ (pc = 0x1008#64 ∧ u.reg 10 = 0)))
    (fun pc u => if pc = 0x1000#64 then (u.reg 10).toNat + 1 else 0) ?_ ?_
  · intro R hR; subst hR; exact .done (.inr ⟨hx, rfl, .inl ⟨hpc, ha⟩⟩)
  · intro u ⟨hux, hur, hcase⟩ R hR; subst hR
    rcases hcase with ⟨hp, hu⟩ | ⟨hp, hu⟩
    · refine Reach.of_segAt (i := 0) (facts := []) (by decide) (by simpa [segOffset] using hp)
        (by decide) hux (by simp) ?_
      unfold segVC; vc_run; simp only
      refine ⟨rfl, ?_⟩
      simp only [Term.Next]
      intro s' ⟨_, hpc', hreg, _⟩ hx'
      have h10 : s'.reg 10 = u.reg 10 + 18446744073709551615#64 := by rw [hreg 10]; rfl
      have h1 : s'.reg 1 = u.reg 1 := by rw [hreg 1]; rfl
      have hd : (Sym.iop .addi (.var 10) 18446744073709551615#64).den (ρOf u) u.mem
          = u.reg 10 + 18446744073709551615#64 := rfl
      have hz : (Sym.const 0#64).den (ρOf u) u.mem = 0#64 := rfl
      rw [hd, hz, hpc']
      refine ⟨fun hc => ⟨by decide, .inr ⟨⟨by simpa using hx', by simpa [h1] using hur, ?_⟩, ?_⟩⟩,
        fun hc => .inr ⟨⟨by simpa using hx', by simpa [h1] using hur, ?_⟩, ?_⟩⟩
      · simp only [evalBr, bne_iff_ne, ne_eq] at hc
        simp only [State.setPc_pc, State.setPc_reg, h10]
        exact .inl ⟨trivial, hc⟩
      · simp only [evalBr, bne_iff_ne, ne_eq] at hc
        simp only [State.setPc_pc, State.setPc_reg, h10, hp, ite_true]
        bv_omega
      · simp only [evalBr, bne_eq_false_iff_eq] at hc
        simp only [State.setPc_pc, State.setPc_reg, h10, hc]
        exact .inr ⟨rfl, rfl⟩
      · simp only [State.setPc_pc, hp, ite_true]
        have hne : ¬(4100#64 + 4 = 4096#64) := by decide
        simp only [hne, ite_false]
        omega
    · refine Reach.of_segAt (i := 1) (facts := []) (by decide) (by rw [hp]; decide)
        (by decide) hux (by simp) ?_
      unfold segVC; vc_run; simp only
      refine ⟨rfl, ?_⟩
      simp only [Term.Next]
      intro s' ⟨_, hpc', hreg, _⟩ hx'
      have h10 : s'.reg 10 = u.reg 10 := by rw [hreg 10]; rfl
      have hd : (Sym.var 1).den (ρOf u) u.mem = s.reg 1 := by rw [← hur]; rfl
      rw [hd]
      exact ⟨hra, .inl ⟨by simpa [h10] using hu, by simp⟩⟩

end NoCompiler.VC.M.Example
