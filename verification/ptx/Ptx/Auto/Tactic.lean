/-
M3: the tactics that discharge a per-thread obligation of the map class.

After `simp only [ptx_eval, …]` has run the kernel symbolically (Tactics/Eval),
what is left is: branch conditions, the legality and footprint of each
access, and the postcondition, all over symbolic register values. These
tactics close them without any per-kernel hint beyond the spec:

* `ptx_addrs [bases] [indices]` finds every address the goal mentions (the
  address argument of `rd`, `wr`, `accessOk` and `InFoot`) and, for each,
  tries to prove it equal to `elem base i` for one of the candidate bases
  and indices. The proof is by `toNat`: both sides are reduced to natural
  number arithmetic modulo `2^64` and `omega` decides it from the
  hypotheses in context (thread-index bounds, launch range, array fit).
  Each address that is proved is rewritten to its `elem` form.
* `ptx_branches` splits every branch condition and turns each into linear
  facts about `toNat` (`ptx_cond` lemmas, side conditions by `omega`).
* `ptx_vcs` closes access legality and footprints with the class lemmas
  (Map.lean), the memory reads with `rd32_wr_same` and the frame, and the
  value with `grind`, which knows commutative ring laws on `BitVec`.

Every step produces a proof term the kernel checks; a step that fails leaves
the goal open, so the check fails and reports `unknown`, it never assumes.
-/
import Lean
import Ptx.Auto.Map

namespace Ptx.Auto
open Ptx

theorem toNat_elem' (b : Addr) (i : Nat) : (elem b i).toNat = (b.toNat + (4 * i) % 2 ^ 64) % 2 ^ 64 := by
  simp [elem, BitVec.toNat_add]

/-! ### Comparisons as `toNat` facts -/

theorem sle_small {w : Nat} {x y : BitVec w} (hx : 2 * x.toNat < 2 ^ w) (hy : 2 * y.toNat < 2 ^ w) :
    x.sle y = decide (x.toNat ≤ y.toNat) := by
  rw [BitVec.sle_eq_decide, BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond]
  simp [hx, hy]

theorem slt_small {w : Nat} {x y : BitVec w} (hx : 2 * x.toNat < 2 ^ w) (hy : 2 * y.toNat < 2 ^ w) :
    x.slt y = decide (x.toNat < y.toNat) := by
  rw [BitVec.slt_eq_decide, BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond]
  simp [hx, hy]

theorem ule_toNat {w : Nat} (x y : BitVec w) : x.ule y = decide (x.toNat ≤ y.toNat) := rfl
theorem ult_toNat {w : Nat} (x y : BitVec w) : x.ult y = decide (x.toNat < y.toNat) := rfl
theorem beq_toNat {w : Nat} (x y : BitVec w) : (x == y) = decide (x.toNat = y.toNat) := by
  by_cases h : x = y
  · subst h; simp
  · have : x.toNat ≠ y.toNat := fun e => h (BitVec.eq_of_toNat_eq e)
    simp [h, this]

/-- `toNat` of a 32-bit value that was zero-extended and truncated. -/
theorem toNat_lo32 (v : Val) : (lo32 v).toNat = v.toNat % 2 ^ 32 := by simp [lo32]
theorem toNat_ext32 (v : BitVec 32) : (ext32 v).toNat = v.toNat := by
  simp [ext32, Nat.mod_eq_of_lt (Nat.lt_trans v.isLt (by decide : 2 ^ 32 < 2 ^ 64))]

theorem lo32_not (v : Val) : lo32 (~~~ v) = ~~~ (lo32 v) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [lo32, hi]

/-- A left shift by a constant is a multiplication, so `grind`'s ring
normalisation can compare `(x <<< 2) + x` with `5 * x`. -/
theorem shl_mul (x : BitVec 32) (k : Nat) : x <<< k = x * BitVec.ofNat 32 (2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_mul, BitVec.toNat_ofNat,
    Nat.mul_mod_mod]

end Ptx.Auto

open Lean Meta Elab Tactic

namespace Ptx.Auto

/-- Arithmetic normalisation used by every `toNat` proof. -/
macro "ptx_nat" : tactic => `(tactic| (
  simp (config := { failIfUnchanged := false }) only [toNat_elem', toNat_lo32, toNat_ext32,
    BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    BitVec.toNat_signExtend, BitVec.msb_eq_decide, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofInt, Nat.reducePow,
    Nat.reduceMod, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd, Int.reduceMod, Int.reduceToNat,
    Int.reduceNeg, decide_eq_true_eq, Nat.min_def, Nat.add_mod_mod, Nat.mod_mod_of_dvd,
    BitVec.toNat_and, BitVec.toNat_or, BitVec.reduceOfInt, BitVec.reduceSetWidth,
    BitVec.reduceSignExtend, BitVec.reduceMul, BitVec.reduceAdd, BitVec.add_zero, BitVec.reduceToNat]
  all_goals ((repeat' split) <;> omega)))

/-- Side conditions of the comparison lemmas. -/
macro "ptx_disch" : tactic => `(tactic| ptx_nat)

/-- Prove `a = elem b i` through `toNat`. -/
macro "ptx_addr_eq" : tactic => `(tactic| (apply BitVec.eq_of_toNat_eq; ptx_nat))

/-- The address arguments in `e`. -/
partial def collectAddrs (e : Expr) : StateT (Array Expr) MetaM Unit := do
  let add (a : Expr) : StateT (Array Expr) MetaM Unit :=
    unless a.hasLooseBVars || a.isAppOf ``Ptx.elem do
      modify fun s => if s.contains a then s else s.push a
  if e.isAppOfArity ``Ptx.rd 3 || e.isAppOfArity ``Ptx.accessOk 3 then add (e.getArg! 1)
  if e.isAppOfArity ``Ptx.wr 4 then add (e.getArg! 1)
  if e.isAppOfArity ``Ptx.InFoot 3 then
    let acc := e.getArg! 2
    if acc.isAppOfArity ``Prod.mk 4 then add (acc.getArg! 2)
  match e with
  | .app f a => collectAddrs f; collectAddrs a
  | .lam _ t b _ | .forallE _ t b _ => collectAddrs t; collectAddrs b
  | .letE _ t v b _ => collectAddrs t; collectAddrs v; collectAddrs b
  | .mdata _ b => collectAddrs b
  | .proj _ _ b => collectAddrs b
  | _ => pure ()

/-- `ptx_addrs [b₁, …] [i₁, …]`: rewrite every address of the goal that is
provably `elem bⱼ iₖ` to that form. -/
elab "ptx_addrs" " [" bs:term,* "]" " [" is:term,* "]" : tactic => withMainContext do
  let bases ← bs.getElems.mapM fun b => elabTerm b (some (mkConst ``Ptx.Addr))
  let idxs ← is.getElems.mapM fun i => elabTerm i (some (mkConst ``Nat))
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  let ((), found) ← (collectAddrs ty).run #[]
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
          -- no error-to-sorry: a failed proof must fail, not be admitted
          let gs ← Term.withoutErrToSorry <| Lean.Elab.Tactic.run mv.mvarId!
            (evalTactic (← `(tactic| ptx_addr_eq)))
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

end Ptx.Auto

/-- The comparison lemmas a branch condition is normalised with. -/
macro "ptx_cond_simp" h:ident : tactic => `(tactic|
  simp (disch := ptx_disch) only [Ptx.Auto.sle_small, Ptx.Auto.slt_small, Ptx.Auto.ule_toNat,
    Ptx.Auto.ult_toNat, Ptx.Auto.beq_toNat, bne_iff_ne, ne_eq, Bool.not_eq_false, Bool.not_eq_true,
    decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Ptx.Auto.toNat_lo32,
    Ptx.Auto.toNat_ext32, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, beq_iff_eq, Bool.false_eq_true,
    not_false_eq_true, Bool.true_eq_false, not_true_eq_false, Decidable.not_not] at $h:ident)

/-- Split every branch the symbolic run could not decide. -/
macro "ptx_branches" : tactic => `(tactic|
  repeat' (split <;> (rename_i hc; try ptx_cond_simp hc)))

/-- The membership and parameter facts the symbolic run needs. -/
macro "ptx_spec_simp" : tactic => `(tactic|
  simp (config := { failIfUnchanged := false }) only [ptx_spec, List.mem_cons, List.not_mem_nil,
    or_false, false_or, or_true, true_or, String.reduceEq, ite_true, ite_false, reduceIte,
    Ptx.Auto.MapSpec.params, Ptx.Auto.MapSpec.launch_params, Ptx.Auto.MapSpec.launch_grid,
    Ptx.Auto.MapSpec.launch_block])

/-- The value equation of a map obligation: fold 32-bit views, reduce
constants, turn constant shifts into multiplications, then `grind`. -/
macro "ptx_value" : tactic => `(tactic| (
  all_goals (try simp only [Ptx.Auto.MapSpec.val, ptx_spec, Ptx.lo32_ext32, Ptx.lo32_rd_b4,
    Ptx.Auto.lo32_not])
  all_goals first
    | done
    | grind
    | (simp (config := { failIfUnchanged := false }) only [Ptx.lo32, BitVec.reduceOfInt,
        BitVec.reduceSetWidth, BitVec.reduceToNat, Nat.min_def, Nat.reduceLeDiff, reduceIte]
       first
         | done
         | grind
         | (simp only [Ptx.Auto.shl_mul, Nat.reducePow]; grind))))

set_option hygiene false in
/-- One verification condition of a map obligation. The names `hpre` and the
spec lemmas tagged `ptx_spec` come from the generated proof. -/
macro "ptx_leaf" : tactic => `(tactic| first
  | done
  | (with_reducible exact Ptx.Auto.MapSpec.accessOk_elem hpre (by ptx_spec_simp) (by omega))
  | (with_reducible exact Ptx.Auto.MapSpec.infoot_load (by ptx_spec_simp) (by omega))
  | (with_reducible exact Ptx.Auto.MapSpec.infoot_store (by ptx_spec_simp) (by omega))
  | (intro hi; exfalso; omega)
  | (simp only [Ptx.Auto.MapSpec.EPost]; intro hi; exfalso; omega)
  | (simp only [Ptx.Auto.MapSpec.EPost, ptx_spec]
     intro hi
     rw [rd32_wr_same]
     ptx_value))

set_option hygiene false in
/-- `ptx_guarded K fuel [bases]`: the whole `GuardedOk` obligation of a
kernel `K` with no backward branch, run for at most `fuel` steps. -/
macro "ptx_guarded" K:ident fuel:num " [" bs:term,* "]" : tactic => `(tactic| (
  intro A hpre m₀ t ht r p
  obtain ⟨⟨hcx, htx, hcy, hcz, hty, htz⟩, hg⟩ := Ptx.Auto.thread_facts ht
  have hsch := hpre.2.2.2
  simp only [ptx_spec, Ptx.Auto.MapSpec.SchedOk] at hsch
  refine (wp_sound (f := $fuel) (cut := fun _ => false) ?_).weaken
    fun s m h => ⟨h.2.resolve_left (by simp), h.1⟩
  simp only [ptx_eval, $K:ident]
  ptx_spec_simp
  unfold gid at *
  ptx_addrs [$bs,*] [t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat]
  ptx_branches
  all_goals (try and_intros)
  all_goals ptx_leaf))

set_option hygiene false in
/-- A register equation at a loop head, or the head itself. -/
macro "ptx_reg" : tactic => `(tactic| first
  | rfl
  | (apply BitVec.eq_of_toNat_eq; ptx_nat))

set_option hygiene false in
/-- The facts about the launch every obligation starts from. -/
macro "ptx_launch_facts" : tactic => `(tactic| (
  obtain ⟨⟨hcx, htx, hcy, hcz, hty, htz⟩, hg⟩ := Ptx.Auto.thread_facts ht
  have hsch := hpre.2.2.2
  simp only [ptx_spec, Ptx.Auto.MapSpec.SchedOk] at hsch
  have hGB := Ptx.Auto.mul32_le A.G A.B
  have hcB := Ptx.Auto.mul32_le t.ctaid.x A.B
  unfold gid at *))

set_option hygiene false in
/-- `ptx_stride_entry K head fuel`: the `EntryOk` obligation. -/
macro "ptx_stride_entry" K:ident head:num fuel:num : tactic => `(tactic| (
  intro A hpre m₀ t ht r p
  ptx_launch_facts
  refine (wp_sound (f := $fuel) (cut := fun pc => pc == $head) ?_).weaken fun s m h => h.1
  simp only [ptx_eval, $K:ident]
  ptx_spec_simp
  simp only [Ptx.Auto.Loop.At, ptx_spec, Ptx.Auto.RegsOk, and_true,
    true_and, Ptx.upd, String.reduceEq, ite_true, ite_false, reduceIte, Ptx.Auto.Role.eval,
    Ptx.lo32_ext32]
  all_goals (try and_intros)
  all_goals ptx_reg))

set_option hygiene false in
/-- `ptx_stride_body K head fuel [bases]`: the `BodyOk` obligation. -/
macro "ptx_stride_body" K:ident head:num fuel:num " [" bs:term,* "]" : tactic => `(tactic| (
  intro A hpre m₀ t ht i hio hiN ⟨pc, rr, pp⟩ m hat hin
  ptx_launch_facts
  simp only [Ptx.Auto.Loop.At, ptx_spec, Ptx.Auto.RegsOk, and_true,
    Ptx.Auto.Role.eval] at hat
  obtain ⟨hpc, hregs⟩ := hat
  subst hpc
  refine (wp_sound (f := $fuel) (cut := fun pc => pc == $head) ?_).weaken fun s m h => h.1
  simp only [ptx_eval, $K:ident, hregs]
  ptx_spec_simp
  ptx_addrs [$bs,*] [i]
  ptx_branches
  all_goals (try and_intros)
  all_goals first
    | ptx_leaf
    | (right; left
       refine ⟨by omega, ?_, ?_⟩ <;> first | trivial | rfl | simp only [ptx_eval, $K:ident])
    | (right; right
       have hi : i < A.n.toNat := by omega
       refine ⟨hi, by omega, ?_, ?_, fun x hx => wr_outside hx⟩
       · first | trivial | rfl | simp only [ptx_eval, $K:ident]
       · rw [rd32_wr_same]
         simp only [ptx_spec, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
           forall_eq, hi, true_implies] at hin
         simp (config := { failIfUnchanged := false }) only [hin]
         ptx_value)
    | (left
       refine ⟨by omega, ?_, ?_, ?_⟩
       · simp only [Ptx.Auto.Loop.At, ptx_spec, Ptx.Auto.RegsOk, and_true, true_and, Ptx.upd,
           String.reduceEq, ite_true, ite_false, reduceIte, Ptx.Auto.Role.eval, Ptx.lo32_ext32,
           hregs]
         all_goals (try and_intros)
         all_goals ptx_reg
       · have hi : i < A.n.toNat := by omega
         rw [rd32_wr_same]
         simp only [ptx_spec, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
           forall_eq, hi, true_implies] at hin
         simp (config := { failIfUnchanged := false }) only [hin]
         ptx_value
       · intro x hx; exact wr_outside hx)))
