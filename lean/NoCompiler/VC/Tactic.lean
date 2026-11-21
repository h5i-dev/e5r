import Lean
import NoCompiler.VC.Seg

/-
`vc_run`: evaluate a segment's symbolic run in a goal, milestone 4c
(docs/design/prior-art-others.md, "Implementation plan").

A cut point's condition (`segVC`) mentions `runSeg D ws S` on closed data.
`vc_run` finds that term, computes its value with compiled code (`evalExpr`),
and rewrites the goal with `runSeg D ws S = v`. That equation is added as an
auxiliary theorem whose proof is `rfl`, so the kernel checks it by evaluating
`runSeg` itself: the compiled evaluation is only a way to find `v` and is not
trusted.
-/
namespace NoCompiler.VC.M
open Lean Meta Elab Tactic

deriving instance ToExpr for NoCompiler.IOp
deriving instance ToExpr for NoCompiler.ROp
deriving instance ToExpr for NoCompiler.LdOp
deriving instance ToExpr for NoCompiler.BrOp
deriving instance ToExpr for NoCompiler.VC.M.Sym, NoCompiler.VC.M.SMem
deriving instance ToExpr for NoCompiler.VC.M.Ob
deriving instance ToExpr for NoCompiler.VC.M.Term
deriving instance ToExpr for NoCompiler.VC.M.SState

/-- The value of a closed `runSeg` term, by compiled evaluation. -/
unsafe def evalRunSegImpl (e : Expr) : MetaM (Option (SState × List Ob × Term)) := do
  evalExpr (Option (SState × List Ob × Term)) (← inferType e) e

@[implemented_by evalRunSegImpl]
opaque evalRunSeg (e : Expr) : MetaM (Option (SState × List Ob × Term))

/-- Rewrite the first closed `runSeg D ws S` in the goal to its value, with a
    kernel-checked equation. -/
elab "vc_run" : tactic => withMainContext do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let some t := tgt.find? fun t => t.isAppOfArity ``runSeg 3 && !t.hasFVar && !t.hasMVar
    | throwError "vc_run: no closed `runSeg` term in the goal"
  let v := toExpr (← evalRunSeg t)
  let pf ← mkAuxTheorem (← mkEq t v) (← mkEqRefl v)
  let r ← g.rewrite tgt pf
  let g' ← g.replaceTargetEq r.eNew r.eqProof
  replaceMainGoal (g' :: r.mvarIds)

end NoCompiler.VC.M
