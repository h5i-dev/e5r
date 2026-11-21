import NoCompiler.VC.Tactic
import NoCompiler.Mem
import NoCompiler.Arith
import NoCompiler.Tactic

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
  refine ⟨trivial, ?_, ?_, trivial⟩
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
    refine ⟨trivial, ?_, ?_, trivial⟩
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

/-! ### A loop over an array, as clang compiled it -/

/-- `sum` from examples/sum.c, the first 9 words of Examples/Sum/Image.lean at 0x11190
    (copied: that module imports all of `NoCompiler`, this file included).
    `li a2,0; beqz a1,+24; L: ld a3,0(a0); add a2,a3,a2; addi a1,a1,-1; addi a0,a0,8; bnez a1,L;
    mv a0,a2; ret`. -/
def sumCode : Code := ⟨0x11190#64, #[0x00000613#32, 0x00058c63#32, 0x00053683#32, 0x00c68633#32,
  0xfff58593#32, 0x00850513#32, 0xfe0598e3#32, 0x00060513#32, 0x00008067#32]⟩
def sumD : Dom := [(0x11190#64, 36)]
def sumW (xs : List Word) : Word := xs.foldl (· + ·) 0

theorem sumW_take_succ (xs : List Word) (k : Nat) (h : k < xs.length) :
    sumW (xs.take (k + 1)) = sumW (xs.take k) + xs[k] := by
  simp only [sumW, List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

theorem ofNat_eq_zero {m : Nat} (h : m < 2 ^ 64) : BitVec.ofNat 64 m = 0#64 ↔ m = 0 := by
  constructor
  · intro e; have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  · rintro rfl; rfl

theorem add_ofNat_succ8 (a : Word) {k : Nat} (_h : 8 * (k + 1) < 2 ^ 64) :
    a + BitVec.ofNat 64 (8 * k) + 8#64 = a + BitVec.ofNat 64 (8 * (k + 1)) := by
  rw [BitVec.add_assoc]; congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- `sum`: from the entry, with read permission on the array only, every run
    reaches the return with the sum in a0. -/
theorem sum_reach (a : Word) (xs : List Word) (s : State) (hpc : s.pc = 0x11190#64) (hx : s.exit = none)
    (ha0 : s.reg 10 = a) (ha1 : s.reg 11 = BitVec.ofNat 64 xs.length) (hlen : 8 * xs.length < 2 ^ 64)
    (hal : aligned a 8) (harr : arr64 s.mem a xs) (hra : aligned (s.reg 1 &&& ~~~1) 4) :
    Reach sumCode ⟨[arrRegion a xs], []⟩ sumD (fun s' => s'.pc = s.reg 1 &&& ~~~1 ∧ s'.reg 10 = sumW xs) s := by
  refine Reach.cutpoints (fun pc u => pc = 0x11198#64 ∧ u.exit = none ∧ u.reg 1 = s.reg 1 ∧ u.mem = s.mem ∧
      ∃ k, k < xs.length ∧ u.reg 10 = a + BitVec.ofNat 64 (8 * k) ∧
        u.reg 11 = BitVec.ofNat 64 (xs.length - k) ∧ u.reg 12 = sumW (xs.take k))
    (fun _ u => (u.reg 11).toNat) ?_ ?_
  · intro R hR; subst hR
    refine Reach.of_exploreAt (facts := []) (cuts := [0x11198#64]) (fuel := 20) (k := 0) (by decide)
      (by decide) hpc hx (by simp) ?_
    unfold exploreVC; vc_run; simp only
    have hn : xs.length < 2 ^ 64 := by omega
    have h11 : (Sym.var 11).den (ρOf s) s.mem = s.reg 11 := rfl
    have hz : (Sym.const 0#64).den (ρOf s) s.mem = 0#64 := rfl
    refine ⟨trivial, ?_, ?_, trivial⟩
    · -- n = 0: straight to the return
      simp only [PEnd.Next]
      intro hc s' ⟨_, _, hreg, _⟩ _
      have hc' := hc _ (List.mem_singleton_self _)
      simp only [Cond.den, h11, hz, evalBr, beq_iff_eq, ha1, ofNat_eq_zero hn] at hc'
      have h10 : s'.reg 10 = 0#64 + 0#64 := by rw [hreg 10]; rfl
      refine ⟨hra, .inl ⟨rfl, ?_⟩⟩
      rw [State.setPc_reg, h10, List.eq_nil_of_length_eq_zero hc']; rfl
    · -- n ≠ 0: to the loop head with k = 0
      simp only [PEnd.Next]
      intro hc s' ⟨_, hpc', hreg, hmem⟩ hx'
      have hc' := hc _ (List.mem_singleton_self _)
      simp only [Cond.den, h11, hz, evalBr, beq_eq_false_iff_ne, ne_eq, ha1, ofNat_eq_zero hn] at hc'
      refine .inr ⟨hpc', hx', by rw [hreg 1]; rfl, hmem, 0, by omega, ?_, ?_, ?_⟩
      · rw [hreg 10]; show s.reg 10 = _; rw [ha0]; simp
      · rw [hreg 11]; show s.reg 11 = _; rw [ha1]; simp
      · rw [hreg 12]; show (0#64 : Word) + 0#64 = _; rfl
  · intro u ⟨hp, hux, hur, hum, k, hk, h10, h11, h12⟩ R hR; subst hR
    refine Reach.of_exploreAt (facts := []) (cuts := [0x11198#64]) (fuel := 20) (k := 2) (by decide)
      (by decide) hp hux (by simp) ?_
    unfold exploreVC; vc_run; simp only
    have hn : xs.length < 2 ^ 64 := by omega
    have hd : (Sym.iop .addi (.var 11) 18446744073709551615#64).den (ρOf u) u.mem
        = u.reg 11 + 18446744073709551615#64 := rfl
    have hz : (Sym.const 0#64).den (ρOf u) u.mem = 0#64 := rfl
    have hsub : u.reg 11 + 18446744073709551615#64 = BitVec.ofNat 64 (xs.length - (k + 1)) := by
      rw [h11, ofNat_add_allOnes _ (by omega) (by omega)]; rfl
    have hld : read64 u.mem (u.reg 10 + 0#64) = xs[k] := by
      rw [hum, h10, BitVec.add_zero]; exact harr k hk
    have h12' : read64 u.mem (u.reg 10 + 0#64) + u.reg 12 = sumW (xs.take (k + 1)) := by
      rw [hld, h12, sumW_take_succ xs k hk, BitVec.add_comm]
    refine ⟨⟨?_, ?_, trivial⟩, ?_, ?_, trivial⟩
    · -- the load is aligned
      show aligned (u.reg 10 + 0#64) 8
      rw [h10, BitVec.add_zero]; exact aligned_add_ofNat hal (by omega) (by decide)
    · -- and inside the array
      refine .inr ⟨arrRegion a xs, by simp, ?_⟩
      show (u.reg 10 + 0#64 - a).toNat + 8 ≤ 8 * xs.length
      rw [h10, BitVec.add_zero, add_ofNat_sub_toNat a (by omega)]; omega
    · -- the back edge, with k + 1
      simp only [PEnd.Next]
      intro hc s' ⟨_, hpc', hreg, hmem⟩ hx'
      have hc' := hc _ (List.mem_singleton_self _)
      simp only [Cond.den, hd, hz, hsub, evalBr, bne_iff_ne, ne_eq,
        ofNat_eq_zero (m := xs.length - (k + 1)) (by omega)] at hc'
      have e10 : s'.reg 10 = u.reg 10 + 8#64 := by rw [hreg 10]; rfl
      have e11 : s'.reg 11 = u.reg 11 + 18446744073709551615#64 := by rw [hreg 11]; rfl
      have e12 : s'.reg 12 = read64 u.mem (u.reg 10 + 0#64) + u.reg 12 := by rw [hreg 12]; rfl
      refine .inr ⟨⟨hpc', hx', by rw [hreg 1]; exact hur, hmem.trans hum, k + 1, by omega, ?_, ?_, ?_⟩, ?_⟩
      · rw [e10, h10, add_ofNat_succ8 a (by omega)]
      · rw [e11, hsub]
      · rw [e12, h12']
      · rw [e11, hsub, h11]; simp only [BitVec.toNat_ofNat]; omega
    · -- the return, after the last element
      simp only [PEnd.Next]
      intro hc s' ⟨_, _, hreg, _⟩ _
      have hc' := hc _ (List.mem_singleton_self _)
      simp only [Cond.den, hd, hz, hsub, evalBr, bne_eq_false_iff_eq,
        ofNat_eq_zero (m := xs.length - (k + 1)) (by omega)] at hc'
      have e10 : s'.reg 10 = read64 u.mem (u.reg 10 + 0#64) + u.reg 12 + 0#64 := by rw [hreg 10]; rfl
      have hra' : aligned (u.reg 1 &&& ~~~1) 4 := by rw [hur]; exact hra
      refine ⟨hra', .inl ⟨?_, ?_⟩⟩
      · show u.reg 1 &&& ~~~1 = s.reg 1 &&& ~~~1
        rw [hur]
      · rw [State.setPc_reg, e10, BitVec.add_zero, h12', show k + 1 = xs.length by omega, List.take_length]

/-! ### The same three with `vc_ends` -/

set_option maxRecDepth 4000 in
theorem abs_spec2 {P : Perm} (s : State) (hpc : s.pc = 0x2000#64) (hx : s.exit = none)
    (hra : aligned (s.reg 1 &&& ~~~1) 4) :
    Reach absCode P absD (fun s' => s'.pc = s.reg 1 &&& ~~~1 ∧
      s'.reg 10 = if (s.reg 10).slt 0 then 0 - s.reg 10 else s.reg 10) s := by
  refine Reach.of_exploreAt (facts := []) (cuts := []) (fuel := 10) (k := 0) (by decide) (by decide)
    hpc hx (by simp) ?_
  vc_ends
  all_goals simp_all
theorem countdown3 {P : Perm} (s : State) (hpc : s.pc = 0x1000#64) (ha : s.reg 10 ≠ 0)
    (hra : aligned (s.reg 1 &&& ~~~1) 4) (hx : s.exit = none) :
    Reach (Code.ofSegs 0x1000#64 segs) P D (fun s' => s'.reg 10 = 0 ∧ s'.pc = s.reg 1 &&& ~~~1) s := by
  refine Reach.cutpoints (fun pc u => pc = 0x1000#64 ∧ u.exit = none ∧ u.reg 1 = s.reg 1 ∧ u.reg 10 ≠ 0)
    (fun _ u => (u.reg 10).toNat) ?_ ?_
  · intro R hR; subst hR; exact .done (.inr ⟨hpc, hx, rfl, ha⟩)
  · intro u ⟨hp, hux, hur, hu⟩ R hR; subst hR
    refine Reach.of_exploreAt (facts := []) (cuts := [0x1000#64]) (fuel := 10) (k := 0) (by decide)
      (by decide) hp hux (by simp) ?_
    vc_ends
    · simp only [bne_iff_ne, ne_eq] at hc
      refine .inr ⟨⟨hur, ?_⟩, ?_⟩
      · exact hc
      · bv_omega
    · simp only [bne_eq_false_iff_eq] at hc
      exact ⟨hur ▸ hra, .inl ⟨hc, by rw [hur]⟩⟩
theorem sum_reach2 (a : Word) (xs : List Word) (s : State) (hpc : s.pc = 0x11190#64) (hx : s.exit = none)
    (ha0 : s.reg 10 = a) (ha1 : s.reg 11 = BitVec.ofNat 64 xs.length) (hlen : 8 * xs.length < 2 ^ 64)
    (hal : aligned a 8) (harr : arr64 s.mem a xs) (hra : aligned (s.reg 1 &&& ~~~1) 4) :
    Reach sumCode ⟨[arrRegion a xs], []⟩ sumD (fun s' => s'.pc = s.reg 1 &&& ~~~1 ∧ s'.reg 10 = sumW xs) s := by
  have hn : xs.length < 2 ^ 64 := by omega
  refine Reach.cutpoints (fun pc u => pc = 0x11198#64 ∧ u.exit = none ∧ u.reg 1 = s.reg 1 ∧ u.mem = s.mem ∧
      ∃ k, k < xs.length ∧ u.reg 10 = a + BitVec.ofNat 64 (8 * k) ∧
        u.reg 11 = BitVec.ofNat 64 (xs.length - k) ∧ u.reg 12 = sumW (xs.take k))
    (fun _ u => (u.reg 11).toNat) ?_ ?_
  · intro R hR; subst hR
    refine Reach.of_exploreAt (facts := []) (cuts := [0x11198#64]) (fuel := 20) (k := 0) (by decide)
      (by decide) hpc hx (by simp) ?_
    vc_ends
    · simp only [beq_iff_eq, ha1, ofNat_eq_zero hn] at hc
      exact ⟨hra, .inl (by rw [List.eq_nil_of_length_eq_zero hc]; rfl)⟩
    · simp only [beq_eq_false_iff_ne, ne_eq, ha1, ofNat_eq_zero hn] at hc
      exact .inr ⟨0, by omega, by rw [ha0]; simp, by rw [ha1]; simp, rfl⟩
  · intro u ⟨hp, hux, hur, hum, k, hk, h10, h11, h12⟩ R hR; subst hR
    refine Reach.of_exploreAt (facts := []) (cuts := [0x11198#64]) (fuel := 20) (k := 2) (by decide)
      (by decide) hp hux (by simp) ?_
    have hsub : u.reg 11 + 18446744073709551615#64 = BitVec.ofNat 64 (xs.length - (k + 1)) := by
      rw [h11, ofNat_add_allOnes _ (by omega) (by omega)]; rfl
    have h12' : read64 u.mem (u.reg 10 + 0#64) + u.reg 12 = sumW (xs.take (k + 1)) := by
      rw [hum, h10, BitVec.add_zero, harr k hk, h12, sumW_take_succ xs k hk, BitVec.add_comm]
    vc_ends
    · rw [h10, BitVec.add_zero]; exact aligned_add_ofNat hal (by omega) (by decide)
    · refine .inr ⟨arrRegion a xs, by simp, ?_⟩
      simp only [Region.covers, arrRegion]
      rw [h10, BitVec.add_zero, add_ofNat_sub_toNat a (by omega)]; omega
    · simp only [hsub, bne_iff_ne, ne_eq, ofNat_eq_zero (m := xs.length - (k + 1)) (by omega)] at hc
      refine .inr ⟨⟨hur, hum, k + 1, by omega, by rw [h10, add_ofNat_succ8 a (by omega)], hsub, h12'⟩, ?_⟩
      rw [hsub, h11]; simp only [BitVec.toNat_ofNat]; omega
    · simp only [hsub, bne_eq_false_iff_eq, ofNat_eq_zero (m := xs.length - (k + 1)) (by omega)] at hc
      refine ⟨hur ▸ hra, .inl ⟨by rw [hur], ?_⟩⟩
      rw [BitVec.add_zero, h12', show k + 1 = xs.length by omega, List.take_length]

/-! ### A call: the callee's entry is a cut point -/

/-- `auipc ra, 0; jalr ra, 8(ra)` at 0x3000 calls 0x3008 (`addi zero, zero, 0; ret`). -/
def callCode : Code := ⟨0x3000#64, #[0x00000097#32, 0x008080e7#32, 0x00000013#32, 0x00008067#32]⟩

/-- The path from 0x3000 ends at the callee's entry, with the return address in ra. -/
example : ((exploreR callCode [(0x3000#64, 16)] [0x3008#64] (fun k => callCode.words.toList.drop k) 10 0
    0x3000#64 []).map fun r =>
    r.1.map fun e => match e with | .cut S _ => (S.pc, S.reg 1) | .ret S _ => (S.pc, S.reg 1)) =
    some [(0x3008#64, .const 0x3008#64)] := by decide +kernel

/-- `jal ra, +8` at 0x3000 calls 0x3008 the same way. -/
example : ((exploreR ⟨0x3000#64, #[0x008000ef#32, 0x00000013#32, 0x00000013#32, 0x00008067#32]⟩
    [(0x3000#64, 16)] [0x3008#64] (fun k => [0x008000ef#32, 0x00000013#32, 0x00000013#32, 0x00008067#32].drop k)
    10 0 0x3000#64 []).map fun r =>
    r.1.map fun e => match e with | .cut S _ => (S.pc, S.reg 1) | .ret S _ => (S.pc, S.reg 1)) =
    some [(0x3008#64, .const 0x3004#64)] := by decide +kernel

/-! ### A tail call through the callee's specification -/

/-- `f: addi a0,a0,1; jal zero, g` at 0x3000 and `g: addi a0,a0,1; ret` at 0x3008. -/
def tcCode : Code := ⟨0x3000#64, #[0x00150513#32, 0x0040006f#32, 0x00150513#32, 0x00008067#32]⟩
def gD : Dom := [(0x3008#64, 8)]
def fD : Dom := [(0x3000#64, 16)]
def gSpec : Spec Word := { pre := fun x s => s.reg 10 = x, post := fun x _ s' => s'.reg 10 = x + 1 }
def fSpec : Spec Word := { pre := fun x s => s.reg 10 = x, post := fun x _ s' => s'.reg 10 = x + 2 }

theorem g_verified : VerifiedImg tcCode gD 0x3008#64 gSpec := by
  intro x s he hpre
  unfold Exec
  refine Reach.of_exploreAt (facts := []) (cuts := []) (fuel := 10) (k := 2) (by decide) (by decide)
    he.pc he.live (by simp) ?_
  have hpre' : s.reg 10 = x := hpre
  have hm : s.reg 1 &&& ~~~1 = s.reg 1 := and_not_one_of_aligned he.retAligned
  vc_ends
  rw [hm]
  refine ⟨he.retAligned, .inl (by simpa using he.ret), .inl ⟨by simpa using hx', rfl, ?_, ?_⟩⟩
  · intro r hr
    simp only [preservedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [State.setPc_reg, hreg r]
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · show (s'.setPc _).reg 10 = x + 1
    rw [State.setPc_reg, hreg 10, ← hpre']; rfl

theorem gD_sub : gD.sub fD := by
  intro y hy
  simp only [Dom.mem, gD, fD, List.any_cons, List.any_nil, Bool.or_false, decide_eq_true_eq] at hy ⊢
  bv_omega

/-- `f` from `g`'s specification alone: a tail call. -/
theorem f_verified : VerifiedImg tcCode fD 0x3000#64 fSpec := by
  intro x s he hpre
  have hpre' : s.reg 10 = x := hpre
  unfold Exec
  refine Reach.trans (Q₁ := fun u => u.pc = 0x3008#64 ∧ u.exit = none ∧ u.reg 10 = x + 1 ∧
      ∀ r ∈ (1 : Reg) :: preservedRegs, u.reg r = s.reg r) ?_ ?_
  · refine Reach.of_exploreAt (facts := []) (cuts := [0x3008#64]) (fuel := 10) (k := 0) (by decide)
      (by decide) he.pc he.live (by simp) ?_
    vc_ends
    refine ⟨by rw [← hpre']; rfl, ?_⟩
    simp only [preservedRegs, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff,
      and_true, symDen]
  · intro u ⟨hp, hux, hu10, hsame⟩
    have h1 : u.reg 1 = s.reg 1 := hsame 1 (by simp)
    have h2 : u.reg 2 = s.reg 2 := hsame 2 (by simp [preservedRegs])
    have hP : (gSpec.perm (x + 1) u).le (fSpec.perm x s) := by
      have : gSpec.perm (x + 1) u = fSpec.perm x s := by
        simp only [Spec.perm, gSpec, fSpec, Spec.stackRegion, Reg.sp]; rw [h2]
      rw [this]; exact Perm.le_refl _
    have heg : Entry gD 0x3008#64 u :=
      ⟨hp, hux, fun h => he.ret (by rw [← h1]; exact gD_sub _ h), by rw [Reg.ra, h1]; exact he.retAligned,
        by rw [Reg.sp, h2]; exact he.sp⟩
    refine VerifiedImg.call g_verified (x + 1) heg hu10 gD_sub hP fun s' hd _ => ?_
    rcases hd with ⟨hx', hpc', hpres, hpost⟩ | ⟨_, hex⟩
    · refine .done ⟨.inl ?_, .inl ⟨hx', by rw [hpc', h1], fun r hr => ?_, ?_⟩⟩
      · rw [hpc']; show ¬ fD.mem (u.reg 1); rw [h1]; exact he.ret
      · rw [hpres r hr]
        exact hsame r (List.mem_cons_of_mem _ hr)
      · show s'.reg 10 = x + 2
        rw [hpost]; show x + 1 + 1 = x + 2; bv_omega
    · exact hex.elim

/-! ### A call that returns: ra saved in a stack frame across the call -/

/-- `f` at 0x4000: `addi sp,sp,-16; sd ra,8(sp); jal ra,g; ld ra,8(sp); addi sp,sp,16; ret`;
    `g` at 0x4018: `addi a0,a0,1; ret`. -/
def frCode : Code := ⟨0x4000#64, #[0xff010113#32, 0x00113423#32, 0x010000ef#32, 0x00813083#32,
  0x01010113#32, 0x00008067#32, 0x00150513#32, 0x00008067#32]⟩
def g2D : Dom := [(0x4018#64, 8)]
def f2D : Dom := [(0x4000#64, 32)]
def f2Spec : Spec Word := { pre := fun x s => s.reg 10 = x, post := fun x _ s' => s'.reg 10 = x + 1, stack := 16 }

def g2Spec : Spec Word := { pre := fun x s => s.reg 10 = x, post := fun x _ s' => s'.reg 10 = x + 1 }

theorem g2_verified : VerifiedImg frCode g2D 0x4018#64 g2Spec := by
  intro x s he hpre
  have hpre' : s.reg 10 = x := hpre
  have hm : s.reg 1 &&& ~~~1 = s.reg 1 := and_not_one_of_aligned he.retAligned
  unfold Exec
  refine Reach.of_exploreAt (facts := []) (cuts := []) (fuel := 10) (k := 6) (by decide) (by decide)
    he.pc he.live (by simp) ?_
  vc_ends
  rw [hm]
  refine ⟨he.retAligned, .inl (by simpa using he.ret), .inl ⟨by simpa using hx', rfl, ?_, ?_⟩⟩
  · intro r hr
    simp only [preservedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [State.setPc_reg, hreg r]
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · show (s'.setPc _).reg 10 = x + 1
    rw [State.setPc_reg, hreg 10, ← hpre']; rfl

/-- The registers `f` keeps without saving them: the preserved ones except sp. -/
def keep : List Reg := [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

theorem f2_verified : VerifiedImg frCode f2D 0x4000#64 f2Spec := by
  intro x s he hpre
  have hpre' : s.reg 10 = x := hpre
  have hsp : aligned (s.reg 2) 16 := he.sp
  have hra : aligned (s.reg 1) 4 := he.retAligned
  have hslot : s.reg 2 + 18446744073709551600#64 + 8#64 - (s.reg Reg.sp - BitVec.ofNat 64 16) = 8#64 := by
    simp only [Reg.sp]; bv_omega
  unfold Exec
  -- From the entry to the call.
  refine Reach.trans (Q₁ := fun u => u.pc = 0x4018#64 ∧ u.exit = none ∧ u.reg 10 = x ∧
      u.reg 1 = 0x400c#64 ∧ u.reg 2 = s.reg 2 + 18446744073709551600#64 ∧
      (∀ r ∈ keep, u.reg r = s.reg r) ∧
      u.mem = writeLE s.mem (s.reg 2 + 18446744073709551600#64 + 8#64) (s.reg 1).toNat 8) ?_ ?_
  · refine Reach.of_exploreAt (facts := []) (cuts := [0x4018#64]) (fuel := 10) (k := 0) (by decide)
      (by decide) he.pc he.live (by simp) ?_
    vc_ends
    · unfold aligned at hsp ⊢; bv_omega
    · refine .inr ⟨Spec.stackRegion s 16, by simp [Spec.perm, f2Spec], ?_⟩
      simp only [Region.covers, Spec.stackRegion, hslot]; decide
    · simp only [keep, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true,
        symDen, hpre']
  -- The call, from g's specification.
  · intro u ⟨hp, hux, hu10, hu1, hu2, hkeep, humem⟩
    have hP : (g2Spec.perm (x + 0) u).le (f2Spec.perm x s) := by
      refine ⟨fun a n h => ?_, fun a n h => ?_⟩ <;>
      · rcases h with h0 | ⟨r, hr, hc⟩
        · exact .inl h0
        · simp only [Spec.perm, g2Spec, List.nil_append,
            List.mem_cons, List.not_mem_nil, or_false] at hr
          subst hr
          simp only [Region.covers, Spec.stackRegion] at hc
          exact .inl (by omega)
    have heg : Entry g2D 0x4018#64 u :=
      ⟨hp, hux, by rw [Reg.ra, hu1]; decide, by rw [Reg.ra, hu1]; decide,
        by rw [Reg.sp, hu2]; unfold aligned at hsp ⊢; bv_omega⟩
    refine VerifiedImg.call g2_verified (x + 0) heg (by show u.reg 10 = x + 0; rw [hu10]; bv_omega)
      (fun y hy => by simp only [Dom.mem, g2D, f2D, List.any_cons, List.any_nil, Bool.or_false,
        decide_eq_true_eq] at hy ⊢; bv_omega) hP fun t hd hm => ?_
    rcases hd with ⟨htx, htpc, hpres, hpost⟩ | ⟨_, hex⟩
    case inr => exact hex.elim
    have hpost' : t.reg 10 = x + 0 + 1 := hpost
    -- g writes nothing: its only writable region is 0 bytes of stack.
    have hmem' : t.mem = u.mem := funext fun y => hm y fun ⟨r, hr, hy⟩ => by
      simp only [Spec.perm, g2Spec, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; simp only [Region.mem, Spec.stackRegion] at hy; omega
    have hs2 : t.reg 2 = u.reg 2 := hpres 2 (by simp [preservedRegs])
    have hld : read64 t.mem (t.reg 2 + 8#64) = s.reg 1 := by
      rw [hmem', humem, hs2, hu2, read64, Fast.readLE_writeLE_same (by decide)]
      apply BitVec.eq_of_toNat_eq
      have := (s.reg 1).isLt
      simp only [BitVec.toNat_ofNat]; omega
    have hslot' : t.reg 2 + 8#64 - (s.reg Reg.sp - BitVec.ofNat 64 16) = 8#64 := by
      rw [hs2, hu2]; simp only [Reg.sp]; bv_omega
    -- From the return address to f's return.
    refine Reach.of_exploreAt (facts := []) (cuts := []) (fuel := 10) (k := 3) (p := 0x400c#64) (by decide)
      (by decide) (by rw [htpc, Reg.ra, hu1]) htx (by simp) ?_
    vc_ends
    · rw [hs2, hu2]; unfold aligned at hsp ⊢; bv_omega
    · refine .inr ⟨Spec.stackRegion s 16, by simp [Spec.perm, f2Spec], ?_⟩
      simp only [Region.covers, Spec.stackRegion, hslot']; decide
    · have hmk : s.reg 1 &&& ~~~1 = s.reg 1 := and_not_one_of_aligned hra
      rw [hld, hmk]
      refine ⟨hra, .inl (by simpa using he.ret), .inl ⟨by simpa using hx', rfl, fun r hr => ?_, ?_⟩⟩
      · simp only [preservedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rw [State.setPc_reg, hreg r]
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [symDen, evalI] <;>
        first
          | (rw [hs2, hu2]; bv_omega)
          | (rw [hpres _ (by decide), hkeep _ (by decide)])
      · show (s'.setPc _).reg 10 = x + 1
        rw [State.setPc_reg, hreg 10]
        show t.reg 10 = x + 1
        rw [hpost']; bv_omega

end NoCompiler.VC.M.Example
