import NoCompiler.Spec
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

/-- Every register outside `rs` (and not `x0`) still holds its own variable. -/
def sameOk (rs : List Nat) (S : SState) : Bool :=
  (List.range 32).all fun n => n == 0 || rs.contains n ||
    match S.regs.getD n (.const 0) with
    | .var m => m == n
    | _ => false

theorem Same.of_den {s0 u s' : State} {rs : List Nat} {S : SState} {μ : Word → Byte}
    (hS : Same s0 u rs) (hc : sameOk rs S = true)
    (hreg : ∀ r : Reg, s'.reg r = (S.reg r).den (ρOf u) μ) : Same s0 s' rs := by
  intro r hr
  rw [hreg r]
  have h := List.all_eq_true.1 hc r.val (List.mem_range.2 r.isLt)
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

end NoCompiler.VC.M
