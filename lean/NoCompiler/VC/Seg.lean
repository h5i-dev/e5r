import NoCompiler.VC.Ob

/-
Per-segment checking, milestone 4a (docs/design/prior-art-others.md,
"Implementation plan"): one lemma per segment, so a proof's memory is bounded
by a segment, not by the function.

A function's code is built from its segments (`Code.ofSegs`), so that the
words from segment `i`'s offset are segment `i`'s words, then the rest
(`ofSegs_drop`, proved once by induction): a segment's lemma runs its own
words and never walks the words before it.
-/
namespace NoCompiler.VC.M

/-- The code of a function given as its segments, in order. -/
def Code.ofSegs (base : Word) (segs : List (List (BitVec 32))) : Code := ⟨base, segs.flatten.toArray⟩

/-- Where segment `i` starts, in words. -/
def segOffset (segs : List (List (BitVec 32))) (i : Nat) : Nat := ((segs.take i).map List.length).sum

theorem ofSegs_drop (base : Word) :
    ∀ (segs : List (List (BitVec 32))) (i : Nat),
      (Code.ofSegs base segs).words.toList.drop (segOffset segs i) = (segs.drop i).flatten
  | [], i => by simp [Code.ofSegs, segOffset]
  | s :: ss, 0 => by simp [Code.ofSegs, segOffset]
  | s :: ss, i + 1 => by
    have ih := ofSegs_drop base ss i
    simp only [Code.ofSegs, segOffset] at ih ⊢
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.flatten_cons, List.drop_succ_cons]
    try simp only [List.toList_toArray] at ih ⊢
    rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
      show s.length + (List.map List.length (List.take i ss)).sum - s.length =
        (List.map List.length (List.take i ss)).sum by omega, ih]

theorem drop_flatten_get (segs : List (List (BitVec 32))) (i : Nat) (hi : i < segs.length) :
    (segs.drop i).flatten = segs[i] ++ (segs.drop (i + 1)).flatten := by
  rw [List.drop_eq_getElem_cons hi, List.flatten_cons]

/-- One segment's lemma: segment `i`'s run, its obligations checked, gives the
    trusted `Reach` from a state at the segment's start. -/
theorem Reach.of_seg {ρ : Nat → Word} {μ : Word → Byte} {base : Word} {segs : List (List (BitVec 32))}
    {i : Nat} (hi : i < segs.length) {P : Perm} {D : Dom} {Q : State → Prop} {facts : List Fact}
    {S S' : SState} {obs : List Ob} {s : State}
    (hpc : S.pc = base + BitVec.ofNat 64 (4 * segOffset segs i))
    (hb : 4 * (segOffset segs i + segs[i].length) < 2 ^ 64) (hm : Matches ρ μ S s) (hx : s.exit = none)
    (h : runW D segs[i] S = some (S', obs)) (hchk : obs.all (Ob.check facts) = true)
    (hf : ∀ f ∈ facts, f.den ρ P) (hQ : ∀ s', Matches ρ μ S' s' → s'.exit = none → Q s') :
    Reach (Code.ofSegs base segs) P D Q s :=
  Reach.of_runW (k := segOffset segs i) (rest := (segs.drop (i + 1)).flatten)
    (by rw [ofSegs_drop, drop_flatten_get segs i hi]) hb hpc hm hx h
    (fun o ho => Ob.check_sound hf (List.all_eq_true.1 hchk o ho)) hQ

/-! ## Segments that end in a branch, a jump or a return (milestone 4b) -/

/-- How a segment ends. -/
inductive Term
  /-- Runs off its words, at pc `p`. -/
  | fall (p : Word)
  /-- A conditional branch at pc `at_`: to `taken` when `evalBr op a b`, else to `at_ + 4`. -/
  | branch (op : BrOp) (a b : Sym) (at_ taken : Word)
  /-- `jal zero`: to `t`. -/
  | jump (at_ t : Word)
  /-- `jalr zero, 0(ra)`: to the value of ra (cleared low bit). -/
  | ret (at_ : Word) (ra : Sym)

/-- Run a segment's words: straight-line instructions, then possibly one terminator as the last word. -/
def runSeg (D : Dom) : List (BitVec 32) → SState → Option (SState × List Ob × Term)
  | [], S => some (S, [], .fall S.pc)
  | w :: ws, S =>
    if D.mem S.pc then
      match decode w, ws with
      | some (.branch op rs1 rs2 off), [] =>
        some (S, [], .branch op (S.reg rs1) (S.reg rs2) S.pc (S.pc + off.signExtend 64))
      | some (.jal rd off), [] => if rd = 0 then some (S, [], .jump S.pc (S.pc + off.signExtend 64)) else none
      | some (.jalr rd rs1 off), [] =>
        if rd = 0 ∧ rs1 = 1 ∧ off = 0 then some (S, [], .ret S.pc (S.reg 1)) else none
      | some i, _ => match sstep i S with
        | some (S₁, o₁) => (runSeg D ws S₁).map fun (S', o, t) => (S', o₁ ++ o, t)
        | none => none
      | none, _ => none
    else none

/-- What the successors of a segment must satisfy, from every state `s'` the
    end state describes (at the terminator's pc for branches, jumps, returns). -/
def Term.Next (ρ : Nat → Word) (μ : Word → Byte) (Q : State → Prop) (S' : SState) : Term → Prop
  | .fall _ => ∀ s', Matches ρ μ S' s' → s'.exit = none → Q s'
  | .branch op a b _ taken =>
    ∀ s', Matches ρ μ S' s' → s'.exit = none →
      (evalBr op (a.den ρ μ) (b.den ρ μ) = true → aligned taken 4 ∧ Q (s'.setPc taken)) ∧
      (evalBr op (a.den ρ μ) (b.den ρ μ) = false → Q (s'.setPc (s'.pc + 4)))
  | .jump _ t => aligned t 4 ∧ ∀ s', Matches ρ μ S' s' → s'.exit = none → Q (s'.setPc t)
  | .ret _ ra => ∀ s', Matches ρ μ S' s' → s'.exit = none →
      aligned (ra.den ρ μ &&& ~~~1) 4 ∧ Q (s'.setPc (ra.den ρ μ &&& ~~~1))

theorem setReg_x0' (s : State) (v : Word) : s.setReg 0 v = s := by simp [State.setReg]

/-- A segment's run, sound: when its obligations hold and its successors
    satisfy `Q` (`Term.Next`), every execution from a described state reaches `Q`. -/
theorem Reach.of_runSeg {ρ : Nat → Word} {μ : Word → Byte} {c : Code} {P : Perm} {D : Dom}
    {Q : State → Prop} :
    ∀ {ws rest : List (BitVec 32)} {k : Nat} {S S' : SState} {obs : List Ob} {t : Term} {s : State},
      c.words.toList.drop k = ws ++ rest → 4 * (k + ws.length) < 2 ^ 64 →
      S.pc = c.base + BitVec.ofNat 64 (4 * k) → Matches ρ μ S s → s.exit = none →
      runSeg D ws S = some (S', obs, t) → (∀ o ∈ obs, o.den ρ μ P) → t.Next ρ μ Q S' → Reach c P D Q s
  | [], _, _, S, S', obs, t, s, _, _, _, hm, hx, h, _, hN => by
    simp only [runSeg, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
    exact .done (hN s hm hx)
  | w :: ws, rest, k, S, S', obs, t, s, hd, hb, hpc, hm, hx, h, hob, hN => by
    simp only [runSeg] at h
    split at h
    · rename_i hD
      have hD' : D.mem s.pc := by rw [hm.2.1]; exact hD
      have hw : c.words.toList[k]? = some w := by rw [← List.head?_drop, hd]; rfl
      have hfetch : ∀ i, decode w = some i → c.instr s.pc = some i := fun i hi => by
        rw [hm.2.1, hpc]; unfold Code.instr
        rw [Code.fetch_index c k (by simp at hb; omega), hw]; exact hi
      have hpcS : s.pc = S.pc := hm.2.1
      split at h
      · -- a branch, last
        rename_i op rs1 rs2 off hi
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
        have hN' := hN s hm hx
        have hra := (hm.2.2.1 rs1).symm
        have hrb := (hm.2.2.1 rs2).symm
        rw [hra, hrb] at hN'
        refine Reach.exec_step hD' hx (hfetch _ hi) trivial ?_
        simp only [exec, jumpTo]
        cases hc : evalBr op (s.reg rs1) (s.reg rs2)
        · simp only [Bool.false_eq_true, ite_false, Reach.opt_some]
          exact .done (hN'.2 hc)
        · obtain ⟨hal, hq⟩ := hN'.1 hc
          rw [← hpcS] at hal hq
          simp only [ite_true, hal, Reach.opt_some]
          exact .done hq
      · -- jal
        rename_i rd off hi
        split at h
        · rename_i hrd; subst hrd
          simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
          obtain ⟨hal, hq⟩ := hN
          rw [← hpcS] at hal hq
          refine Reach.exec_step hD' hx (hfetch _ hi) trivial ?_
          simp only [exec, jumpTo, setReg_x0', hal, ite_true, Reach.opt_some]
          exact .done (hq s hm hx)
        · simp at h
      · -- jalr zero, 0(ra)
        rename_i rd rs1 off hi
        split at h
        · rename_i hc; obtain ⟨rfl, rfl, rfl⟩ := hc
          simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
          obtain ⟨hal, hq⟩ := hN s hm hx
          have h1 := (hm.2.2.1 1).symm
          rw [h1] at hal hq
          refine Reach.exec_step hD' hx (hfetch _ hi) trivial ?_
          have hz : s.reg 1 + BitVec.signExtend 64 (0 : BitVec 12) = s.reg 1 := by
            rw [show BitVec.signExtend 64 (0 : BitVec 12) = 0 by decide]; bv_omega
          simp only [exec, jumpTo, setReg_x0', hz, hal, ite_true, Reach.opt_some]
          exact .done hq
        · simp at h
      · -- a straight-line instruction
        rename_i wsL _ _ i hi _ _ _
        split at h
        · rename_i S₁ o₁ hst
          cases hr : runSeg D wsL S₁ with
          | none => rw [hr] at h; simp at h
          | some p =>
            obtain ⟨S₂, o₂, t₂⟩ := p
            rw [hr] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            obtain ⟨s₁, he, hok, hm₁⟩ := sstep_sound (P := P) hm hst
              (fun o ho => hob o (List.mem_append_left _ ho))
            have hpc₁ : S₁.pc = c.base + BitVec.ofNat 64 (4 * (k + 1)) := by
              cases i <;> simp only [sstep, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hst <;>
                (try obtain ⟨rfl, rfl⟩ := hst) <;> simp_all <;> bv_omega
            have hd₁ : c.words.toList.drop (k + 1) = wsL ++ rest := by rw [← List.drop_drop, hd]; rfl
            have hrest : Reach c P D Q s₁ :=
              Reach.of_runSeg hd₁ (by simp at hb ⊢; omega) hpc₁ hm₁ ((exec_exit he).trans hx) hr
                (fun o ho => hob o (List.mem_append_right _ ho)) hN
            exact NoCompiler.Reach.exec_step hD' hx (hfetch _ hi) hok
              (by rw [he, NoCompiler.Reach.opt_some]; exact hrest)
        · simp at h
      · simp at h
    · simp at h

/-- Floyd's method on `Reach.loop`: an invariant at every cut point (`inv pc`)
    and a measure (`μ pc`) that every path from one cut point to the next
    decreases. With the loop heads as cut points, every path from the start or
    from a cut point reaches the end (`Q`) or a cut point without passing
    another. The postconditions are given as equations so that a proof can
    keep them abstract while it runs. -/
theorem _root_.NoCompiler.Reach.cutpoints {c : Code} {P : Perm} {D : Dom} {Q : State → Prop}
    (inv : Word → State → Prop) (μ : Word → State → Nat) {s : State}
    (start : ∀ R : State → Prop, R = (fun s' => Q s' ∨ inv s'.pc s') → Reach c P D R s)
    (body : ∀ u, inv u.pc u → ∀ R : State → Prop,
      R = (fun s' => Q s' ∨ (inv s'.pc s' ∧ μ s'.pc s' < μ u.pc u)) → Reach c P D R u) :
    Reach c P D Q s :=
  Reach.trans (start _ rfl) fun s' h => h.elim .done fun hi =>
    Reach.loop (fun u => inv u.pc u) (fun u => μ u.pc u) (fun u hu => body u hu _ rfl) s' hi

/-! ## Cut points (milestone 4c)

At a cut point nothing is known symbolically: the segment from there runs from
`SState.init`, whose variables are the state's registers (`ρOf`) and whose base
memory is the state's memory. `segVC` is what one cut point's segment leaves to
prove, and `Reach.of_segAt` is its soundness, so a function's proof is
`Reach.cutpoints` with one `segVC` per cut point. -/

/-- A state's registers as the variables of `SState.init`. -/
def ρOf (s : State) (n : Nat) : Word := if h : n < 32 then s.reg ⟨n, h⟩ else 0

theorem matches_init {s : State} {p : Word} (h : s.pc = p) :
    Matches (ρOf s) s.mem (SState.init p) s := by
  refine ⟨by simp [SState.init], h, fun r => ?_, by simp [SState.init, SMem.den]⟩
  by_cases hr : r.val = 0
  · have : r = 0 := Fin.ext hr
    subst this; simp [SState.reg, Sym.den]
  · simp [SState.reg, SState.init, hr, Sym.den, ρOf, r.isLt]

/-- One cut point's verification condition: the segment's run, its obligations
    checked from the facts, and what its successors must satisfy. -/
def segVC (ρ : Nat → Word) (μ : Word → Byte) (Q : State → Prop) (facts : List Fact) (D : Dom)
    (ws : List (BitVec 32)) (S : SState) : Prop :=
  match runSeg D ws S with
  | some (S', obs, t) => obs.all (Ob.check facts) = true ∧ t.Next ρ μ Q S'
  | none => False

theorem Reach.of_segAt {base : Word} {segs : List (List (BitVec 32))} {i : Nat} (hi : i < segs.length)
    {P : Perm} {D : Dom} {Q : State → Prop} {facts : List Fact} {s : State}
    (hpc : s.pc = base + BitVec.ofNat 64 (4 * segOffset segs i))
    (hb : 4 * (segOffset segs i + segs[i].length) < 2 ^ 64) (hx : s.exit = none)
    (hf : ∀ f ∈ facts, f.den (ρOf s) P)
    (hvc : segVC (ρOf s) s.mem Q facts D segs[i]
      (SState.init (base + BitVec.ofNat 64 (4 * segOffset segs i)))) :
    Reach (Code.ofSegs base segs) P D Q s := by
  unfold segVC at hvc
  split at hvc
  · rename_i S' obs t h
    exact Reach.of_runSeg (rest := (segs.drop (i + 1)).flatten)
      (by rw [ofSegs_drop, drop_flatten_get segs i hi]) hb rfl (matches_init hpc) hx h
      (fun o ho => Ob.check_sound hf (List.all_eq_true.1 hvc.1 o ho)) hvc.2
  · exact hvc.elim

end NoCompiler.VC.M
