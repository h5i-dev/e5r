/-
M4: tactic pieces for phase obligations (shared memory, barriers, shifts of
symbolic strides). They extend the M3 ones (Ptx/Auto/Tactic.lean) and leave
those untouched, so the 102 map proofs are not affected.

* `ptx_cond_simp4 h` normalises a branch condition, like `ptx_cond_simp`,
  and also turns shifts and `min` into natural-number arithmetic so `omega`
  can use strides such as `B / 2^k`.
* `ptx_branches4` splits every undecided branch with it.

As in M3, these only build proof terms; a failure leaves a goal open.
-/
import Ptx.Auto.Tactic
import Ptx.Tactics.EvalR
import Ptx.Logic.Cells

namespace Ptx.Auto

theorem toNat_lo32_zero : (lo32 (0#64)).toNat = 0 := rfl

end Ptx.Auto

open Lean Meta Elab Tactic in
/-- Arithmetic normalisation for M4 address and register goals: `ptx_nat`'s
set, plus literal `min` and `if`. -/
macro "ptx_nat4" : tactic => `(tactic| (
  simp (config := { failIfUnchanged := false }) only [Ptx.Auto.toNat_elem', Ptx.Auto.toNat_lo32,
    Ptx.Auto.toNat_ext32, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat, BitVec.toNat_signExtend, BitVec.msb_eq_decide, BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofInt,
    Nat.reducePow, Nat.reduceMod, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv,
    Int.reduceMod, Int.reduceToNat, Int.reduceNeg, decide_eq_true_eq, Nat.min_def, Nat.reduceLeDiff,
    ↓reduceIte, Nat.add_mod_mod, Nat.mod_mod_of_dvd, BitVec.toNat_and, BitVec.toNat_or,
    BitVec.reduceOfInt, BitVec.reduceSetWidth, BitVec.reduceSignExtend, BitVec.reduceMul,
    BitVec.reduceAdd, BitVec.add_zero, BitVec.reduceToNat, Nat.pow_one, Nat.div_one]
  all_goals ((repeat' split) <;> omega)))

/-- Prove `a = elem b i` through `toNat`, with `ptx_nat4`. -/
macro "ptx_addr_eq4" : tactic => `(tactic| (apply BitVec.eq_of_toNat_eq; ptx_nat4))

/-- A register equation, as `ptx_reg`, with `ptx_nat4`. -/
macro "ptx_reg4" : tactic => `(tactic| first
  | rfl
  | (apply BitVec.eq_of_toNat_eq; ptx_nat4))

open Lean Meta Elab Tactic in
/-- `ptx_addrs4 [b₁, …] [i₁, …]`: `ptx_addrs` with `ptx_addr_eq4`. -/
elab "ptx_addrs4" " [" bs:term,* "]" " [" is:term,* "]" : tactic => withMainContext do
  let bases ← bs.getElems.mapM fun b => elabTerm b (some (mkConst ``Ptx.Addr))
  let idxs ← is.getElems.mapM fun i => elabTerm i (some (mkConst ``Nat))
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  let ((), found) ← (Ptx.Auto.collectAddrs ty).run #[]
  let mut eqs : Array Expr := #[]
  for a in found do
    let mut done := false
    for b in bases do
      for i in idxs do
        if done then continue
        let rhs ← mkAppM ``Ptx.elem #[b, i]
        let eqTy ← mkEq a rhs
        let mv ← mkFreshExprMVar eqTy
        let saved ← saveState
        try
          let gs ← Term.withoutErrToSorry <| Lean.Elab.Tactic.run mv.mvarId!
            (evalTactic (← `(tactic| ptx_addr_eq4)))
          let pf ← instantiateMVars mv
          if gs.isEmpty && !pf.hasSorry && !pf.hasExprMVar then
            eqs := eqs.push pf
            done := true
          else
            restoreState saved
        catch _ =>
          restoreState saved
  if eqs.isEmpty then return
  let mut g := goal
  for p in eqs do
    let r ← g.rewrite (← g.getType) p
    let g' ← g.replaceTargetEq r.eNew r.eqProof
    g := g'
  replaceMainGoal [g]

/-- The comparison lemmas a branch condition is normalised with, including
shifts. -/
macro "ptx_cond_simp4" h:ident : tactic => `(tactic|
  simp (disch := ptx_disch) only [Ptx.Auto.sle_small, Ptx.Auto.slt_small, Ptx.Auto.ule_toNat,
    Ptx.Auto.ult_toNat, Ptx.Auto.beq_toNat, bne_iff_ne, ne_eq, Bool.not_eq_false, Bool.not_eq_true,
    decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Ptx.Auto.toNat_lo32,
    Ptx.Auto.toNat_ext32, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, beq_iff_eq, Bool.false_eq_true,
    not_false_eq_true, Bool.true_eq_false, not_true_eq_false, Decidable.not_not,
    BitVec.reduceOfInt, BitVec.reduceToNat, Nat.reduceEqDiff, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.min_def,
    ← BitVec.toNat_inj, Ptx.Auto.toNat_lo32_zero, Nat.reduceLeDiff, Nat.lt_irrefl, Nat.le_refl,
    ite_true, ite_false] at $h:ident)

/-- Split every branch the symbolic run could not decide, normalising each
condition for `omega`. -/
macro "ptx_branches4" : tactic => `(tactic|
  repeat' (split <;> (rename_i hc; try ptx_cond_simp4 hc)))
