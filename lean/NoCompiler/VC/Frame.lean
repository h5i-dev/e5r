import NoCompiler.Spec
import NoCompiler.Tactic
import NoCompiler.VC.Explore

/-
The registers a path leaves alone, for `vc_auto` (NoCompiler/Auto.lean).

At a path's end the registers are known only through `Matches`: register `r`
of the end state is the denotation of the symbolic value `S.reg r`. A loop
invariant and a return both need `Same s0 s' rs` (every register outside `rs`
holds its entry value). `sameOk rs S` is a closed check on the symbolic state,
evaluated by the kernel: each register outside `rs` still holds its own
variable. Then `Same.of_den` gives `Same` at the end from `Same` at the cut
point, with no step per register.
-/
namespace NoCompiler.VC.M

/-- Register `n` is in `rs`, or `x0`, or still holds its own variable. -/
def regOk (rs : List Nat) (n : Nat) (x : Sym) : Bool :=
  n == 0 || rs.contains n ||
    match x with
    | .var m => m == n
    | _ => false

/-- `regOk` along the register list from index `n`: one pass (an indexed
    lookup per register made the kernel's check quadratic, 64 ms measured). -/
def sameGo (rs : List Nat) : Nat → List Sym → Bool
  | _, [] => true
  | n, x :: xs => regOk rs n x && sameGo rs (n + 1) xs

/-- Every register outside `rs` (and not `x0`) still holds its own variable. -/
def sameOk (rs : List Nat) (S : SState) : Bool := S.regs.length == 32 && sameGo rs 0 S.regs

theorem sameGo_spec {rs : List Nat} : ∀ {n : Nat} {l : List Sym}, sameGo rs n l = true →
    ∀ i (h : i < l.length), regOk rs (n + i) l[i] = true
  | _, [], _, i, h => absurd h (by simp)
  | n, x :: xs, hg, i, h => by
    simp only [sameGo, Bool.and_eq_true] at hg
    cases i with
    | zero => simpa using hg.1
    | succ i =>
      have := sameGo_spec hg.2 i (by simp at h; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

theorem sameOk_spec {rs : List Nat} {S : SState} (hc : sameOk rs S = true) (n : Nat) (hn : n < 32) :
    regOk rs n (S.regs.getD n (.const 0)) = true := by
  simp only [sameOk, Bool.and_eq_true, beq_iff_eq] at hc
  have h := sameGo_spec hc.2 n (by omega)
  simp only [Nat.zero_add] at h
  have e : S.regs.getD n (.const 0) = S.regs[n]'(by omega) := by
    simp [List.getD, List.getElem?_eq_getElem (show n < S.regs.length by omega)]
  rw [e]; exact h

theorem Same.of_den {s0 u s' : State} {rs : List Nat} {S : SState} {μ : Word → Byte}
    (hS : Same s0 u rs) (hc : sameOk rs S = true)
    (hreg : ∀ r : Reg, s'.reg r = (S.reg r).den (ρOf u) μ) : Same s0 s' rs := by
  intro r hr
  rw [hreg r]
  have h := sameOk_spec hc r.val r.isLt
  unfold regOk at h
  by_cases h0 : r.val = 0
  · have : r = 0 := Fin.ext h0
    subst this
    simp [SState.reg, Sym.den]
  · have hc' : (List.contains rs r.val) = false := by
      cases hh : rs.contains r.val
      · rfl
      · exact absurd (List.contains_iff_mem.1 hh) hr
    have h1 : (r.val == 0) = false := by simp [h0]
    rw [h1, hc', Bool.false_or, Bool.false_or] at h
    have hr' : S.reg r = S.regs.getD r.val (.const 0) := by simp [SState.reg, h0]
    rw [hr']
    split at h
    · rename_i m hm
      rw [hm]
      have hmn : m = r.val := by simpa using h
      show ρOf u m = _
      rw [hmn]
      simp only [ρOf, r.isLt, dite_true]
      exact hS r hr
    · exact absurd h (by simp)

/-! ### Calls

A path that reaches a callee's entry stops there, as at a cut point, and what
is due is the rest of the run from there (`Reach`), which the callee's
`VerifiedImg` theorem gives (`VerifiedImg.call`). The other ends are due `Q`. -/

/-- At a callee's entry the rest of the run, elsewhere `Q`. -/
def CallQ (c : Code) (P : Perm) (D : Dom) (Q : State → Prop) (ces : List Word) (s : State) : Prop :=
  if s.pc ∈ ces then Reach c P D Q s else Q s

theorem Reach.of_exploreCalls {c : Code} {P : Perm} {D : Dom} {Q : State → Prop} {facts : List Fact}
    {cuts ces : List Word} {fuel k : Nat} {p : Word} {s : State} (hb : 4 * c.words.size < 2 ^ 64)
    (hk : p = c.base + BitVec.ofNat 64 (4 * k)) (hpc : s.pc = p) (hx : s.exit = none)
    (hf : ∀ f ∈ facts, f.den (ρOf s) P)
    (hvc : exploreVC (ρOf s) s.mem P (CallQ c P D Q ces) facts c D (cuts ++ ces) fuel k p) :
    Reach c P D Q s :=
  Reach.trans (Reach.of_exploreAt hb hk hpc hx hf hvc) fun s' h => by
    unfold CallQ at h
    split at h
    · exact h
    · exact .done h

theorem CallQ.call {c : Code} {P : Perm} {D : Dom} {Q : State → Prop} {ces : List Word} {s : State}
    (h : s.pc ∈ ces) (hr : Reach c P D Q s) : CallQ c P D Q ces s := by
  simp only [CallQ, h, ite_true]; exact hr

theorem CallQ.other {c : Code} {P : Perm} {D : Dom} {Q : State → Prop} {ces : List Word} {s : State}
    (h : s.pc ∉ ces) (hq : Q s) : CallQ c P D Q ces s := by
  simp only [CallQ, h, ite_false]; exact hq

/-- A return end: the return address is the entry's `ra`, which is outside the
    function, so not a callee's entry. -/
theorem CallQ.ret {c : Code} {P : Perm} {D Dc : Dom} {Q : State → Prop} {ces : List Word}
    {entry : Word} {s0 s' : State} {X : Word} (he : Entry D entry s0)
    (hcalls : ces.all (fun x => decide (D.mem x)) = true) (hX : X = s0.reg 1)
    (hq : Q (s'.setPc (s0.reg 1))) :
    NoCompiler.aligned (X &&& ~~~1) 4 ∧ CallQ c P Dc Q ces (s'.setPc (X &&& ~~~1)) := by
  have hm : s0.reg 1 &&& ~~~1 = s0.reg 1 := and_not_one_of_aligned he.retAligned
  subst hX
  rw [hm]
  refine ⟨he.retAligned, CallQ.other (fun hm' => he.ret ?_) hq⟩
  exact of_decide_eq_true (List.all_eq_true.1 hcalls _ hm')

end NoCompiler.VC.M
