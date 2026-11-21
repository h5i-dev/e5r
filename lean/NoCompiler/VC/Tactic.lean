import Lean
import NoCompiler.VC.Explore

/-
`vc_run`: evaluate a segment's symbolic run in a goal, milestone 4c
(docs/design/prior-art-others.md, "Implementation plan").

A cut point's condition (`segVC`) mentions `runSeg D ws S` on closed data.
`vc_run` finds that term, computes its value with compiled code (`evalExpr`),
and rewrites the goal with `runSeg D ws S = v`, proved by `decide` on the
derived `DecidableEq`: the kernel checks it by evaluating `runSeg` itself and
comparing, so the compiled evaluation is only a way to find `v` and is not
trusted. The proof goes into the theorem as it is, unchecked by the elaborator
(building it as an auxiliary theorem first made the elaborator check it, and a
proof by `rfl` made the kernel compare by unfolding; both were measured slower,
docs/design/prior-art-others.md).
-/
namespace NoCompiler.VC.M
open Lean Meta Elab Tactic

deriving instance ToExpr for NoCompiler.IOp
deriving instance ToExpr for NoCompiler.ROp
deriving instance ToExpr for NoCompiler.LdOp
deriving instance ToExpr for NoCompiler.BrOp
deriving instance ToExpr for NoCompiler.ShOp
deriving instance ToExpr for NoCompiler.ShWOp
deriving instance ToExpr for NoCompiler.RWOp
deriving instance ToExpr for NoCompiler.UOp
deriving instance ToExpr for NoCompiler.VC.M.Sym, NoCompiler.VC.M.SMem
deriving instance ToExpr for NoCompiler.VC.M.Ob
deriving instance ToExpr for NoCompiler.VC.M.Term
deriving instance ToExpr for NoCompiler.VC.M.SState
deriving instance ToExpr for NoCompiler.VC.M.Cond
deriving instance ToExpr for NoCompiler.VC.M.PEnd
deriving instance DecidableEq for NoCompiler.VC.M.Sym, NoCompiler.VC.M.SMem
deriving instance DecidableEq for NoCompiler.VC.M.Ob
deriving instance DecidableEq for NoCompiler.VC.M.Term
deriving instance DecidableEq for NoCompiler.VC.M.SState
deriving instance DecidableEq for NoCompiler.VC.M.Cond
deriving instance DecidableEq for NoCompiler.VC.M.PEnd

/-- The value of a closed `runSeg` term, by compiled evaluation. -/
unsafe def evalRunSegImpl (e : Expr) : MetaM (Option (SState × List Ob × Term)) := do
  evalExpr (Option (SState × List Ob × Term)) (← inferType e) e

@[implemented_by evalRunSegImpl]
opaque evalRunSeg (e : Expr) : MetaM (Option (SState × List Ob × Term))

/-- The value of a closed `explore` term, by compiled evaluation. -/
unsafe def evalExploreImpl (e : Expr) : MetaM (Option (List PEnd × List Ob)) := do
  evalExpr (Option (List PEnd × List Ob)) (← inferType e) e

@[implemented_by evalExploreImpl]
opaque evalExplore (e : Expr) : MetaM (Option (List PEnd × List Ob))

/-- Rewrite the first closed `runSeg D ws S` or `explore …` in the goal to its
    value, with a kernel-checked equation (`decide`). -/
elab "vc_run" : tactic => withMainContext do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let closed (t : Expr) := !t.hasFVar && !t.hasMVar
  let some t := tgt.find? fun t =>
      (t.isAppOfArity ``runSeg 3 || t.isAppOfArity ``explore 9) && closed t
    | throwError "vc_run: no closed `runSeg` or `explore` term in the goal"
  let v ← if t.isAppOf ``runSeg then pure (toExpr (← evalRunSeg t)) else pure (toExpr (← evalExplore t))
  let eq ← mkEq t v
  let inst ← synthInstance (mkApp (mkConst ``Decidable) eq)
  let pf := mkApp3 (mkConst ``of_decide_eq_true) eq inst
    (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))
  let r ← g.rewrite tgt pf
  let g' ← g.replaceTargetEq r.eNew r.eqProof
  replaceMainGoal (g' :: r.mvarIds)

end NoCompiler.VC.M
