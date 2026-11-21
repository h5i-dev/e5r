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

/-! ### Paths through branches (`explore`) -/

/-- `abs`: `bge a0, zero, +8; sub a0, zero, a0; ret`, at 0x2000. -/
def absCode : Code := ⟨0x2000#64, #[0x00055463#32, 0x40a00533#32, 0x00008067#32]⟩
def absD : Dom := [(0x2000#64, 12)]

/-- Two paths, both to the return; no cut point. -/
theorem abs_spec {P : Perm} (s : State) (hpc : s.pc = 0x2000#64) (hx : s.exit = none)
    (hra : aligned (s.reg 1 &&& ~~~1) 4) :
    Reach absCode P absD (fun s' => s'.pc = s.reg 1 &&& ~~~1 ∧
      s'.reg 10 = if (s.reg 10).slt 0 then 0 - s.reg 10 else s.reg 10) s := by
  refine Reach.of_exploreAt (facts := []) (cuts := []) (fuel := 10) (k := 0) (by decide) (by decide)
    hpc hx (by simp) ?_
  unfold exploreVC; vc_run; simp only
  refine ⟨rfl, ?_, ?_, trivial⟩
  · simp only [PEnd.Next]
    intro hc s' ⟨_, _, hreg, _⟩ _
    have hc' : evalBr .bge (s.reg 10) 0 = true := hc _ (List.mem_singleton_self _)
    have h10 : s'.reg 10 = s.reg 10 := by rw [hreg 10]; rfl
    refine ⟨hra, rfl, ?_⟩
    rw [State.setPc_reg, h10]
    simp only [evalBr, Bool.not_eq_true'] at hc'
    simp only [hc', Bool.false_eq_true, ite_false]
  · simp only [PEnd.Next]
    intro hc s' ⟨_, _, hreg, _⟩ _
    have hc' : evalBr .bge (s.reg 10) 0 = false := hc _ (List.mem_singleton_self _)
    have h10 : s'.reg 10 = 0 - s.reg 10 := by rw [hreg 10]; rfl
    refine ⟨hra, rfl, ?_⟩
    rw [State.setPc_reg, h10]
    simp only [evalBr, Bool.not_eq_false'] at hc'
    simp only [hc', ite_true]

/-- The countdown again, with `explore`: one cut point (the loop head) covers
    the back edge and the return, where `countdown` needed a segment for each. -/
theorem countdown' {P : Perm} (s : State) (hpc : s.pc = 0x1000#64) (ha : s.reg 10 ≠ 0)
    (hra : aligned (s.reg 1 &&& ~~~1) 4) (hx : s.exit = none) :
    Reach (Code.ofSegs 0x1000#64 segs) P D (fun s' => s'.reg 10 = 0 ∧ s'.pc = s.reg 1 &&& ~~~1) s := by
  refine Reach.cutpoints (fun pc u => pc = 0x1000#64 ∧ u.exit = none ∧ u.reg 1 = s.reg 1 ∧ u.reg 10 ≠ 0)
    (fun _ u => (u.reg 10).toNat) ?_ ?_
  · intro R hR; subst hR; exact .done (.inr ⟨hpc, hx, rfl, ha⟩)
  · intro u ⟨hp, hux, hur, hu⟩ R hR; subst hR
    refine Reach.of_exploreAt (facts := []) (cuts := [0x1000#64]) (fuel := 10) (k := 0) (by decide)
      (by decide) hp hux (by simp) ?_
    unfold exploreVC; vc_run; simp only
    refine ⟨rfl, ?_, ?_, trivial⟩
    · -- the back edge
      simp only [PEnd.Next]
      intro hc s' ⟨_, hpc', hreg, _⟩ hx'
      have hd : (Sym.iop .addi (.var 10) 18446744073709551615#64).den (ρOf u) u.mem
          = u.reg 10 + 18446744073709551615#64 := rfl
      have hz : (Sym.const 0#64).den (ρOf u) u.mem = 0#64 := rfl
      have hc' := hc _ (List.mem_singleton_self _)
      simp only [Cond.den, hd, hz] at hc'
      have h10 : s'.reg 10 = u.reg 10 + 18446744073709551615#64 := by rw [hreg 10]; rfl
      have h1 : s'.reg 1 = u.reg 1 := by rw [hreg 1]; rfl
      simp only [evalBr, bne_iff_ne, ne_eq] at hc'
      refine .inr ⟨⟨hpc', hx', h1.trans hur, by rw [h10]; exact hc'⟩, ?_⟩
      rw [h10]; bv_omega
    · -- the return
      simp only [PEnd.Next]
      intro hc s' ⟨_, _, hreg, _⟩ _
      have hd : (Sym.iop .addi (.var 10) 18446744073709551615#64).den (ρOf u) u.mem
          = u.reg 10 + 18446744073709551615#64 := rfl
      have hz : (Sym.const 0#64).den (ρOf u) u.mem = 0#64 := rfl
      have hc' := hc _ (List.mem_singleton_self _)
      simp only [Cond.den, hd, hz] at hc'
      have h10 : s'.reg 10 = u.reg 10 + 18446744073709551615#64 := by rw [hreg 10]; rfl
      simp only [evalBr, bne_eq_false_iff_eq] at hc'
      have hra' : aligned (u.reg 1 &&& ~~~1) 4 := by rw [hur]; exact hra
      refine ⟨hra', .inl ⟨by rw [State.setPc_reg, h10]; exact hc', ?_⟩⟩
      show u.reg 1 &&& ~~~1 = s.reg 1 &&& ~~~1
      rw [hur]

end NoCompiler.VC.M.Example
