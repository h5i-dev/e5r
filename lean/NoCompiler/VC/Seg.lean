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

end NoCompiler.VC.M
