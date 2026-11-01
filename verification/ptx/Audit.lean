/-
Axiom audit (scripts/check-lean-ptx.sh).

Every declaration of every `Ptx.*` module, not a hand-picked list, is checked:
its transitive axioms must be among `propext`, `Quot.sound` and
`Classical.choice`. That excludes `sorryAx`, `Lean.ofReduceBool` and
`Lean.trustCompiler` (what `native_decide` and `bv_decide` add), and any
axiom declared here. The audit fails the build if anything else appears, and
prints the axioms of the main theorems for the log.
-/
import Ptx
import Lean

open Lean Elab Command

elab "#audit_ptx" : command => do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Quot.sound, ``Classical.choice]
  let mut checked : Nat := 0
  let mut bad : Array String := #[]
  for (name, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`Ptx).isPrefixOf mod do continue
    if let .axiomInfo _ := ci then
      bad := bad.push s!"{name} is an axiom declared in {mod}"
    let axs ← liftCoreM (collectAxioms name)
    for a in axs do
      unless allowed.contains a do
        bad := bad.push s!"{name} ({mod}) depends on {a}"
    checked := checked + 1
  if checked < 500 then
    throwError "axiom audit: only {checked} declarations found; is the library imported?"
  unless bad.isEmpty do
    throwError "axiom audit failed:\n{String.intercalate "\n" bad.toList}"
  logInfo m!"axiom audit: {checked} declarations in Ptx.*, standard axioms only"

#audit_ptx

#print axioms Ptx.grid_sound
#print axioms Ptx.Phased.phase_sound
#print axioms Ptx.Run.frame
#print axioms Ptx.Run.step
#print axioms Ptx.wp_sound
#print axioms Ptx.Safe.solo
#print axioms Ptx.Safe.loop
#print axioms Ptx.Auto.correct_of_threadOk
#print axioms Ptx.Auto.threadOk_of_guardedOk
#print axioms Ptx.Auto.threadOk_of_stride
#print axioms Ptx.Auto.Reduce32.correct_of
#print axioms Ptx.Auto.Reduce32.Atomic.correct_of
#print axioms Ptx.Auto.Scan32.correct_of
#print axioms Ptx.exec_reach
#print axioms Ptx.race_of_exec
#print axioms Ptx.Examples.VectorAdd.vadd_correct
#print axioms Ptx.Examples.Sum.sum_correct
#print axioms Ptx.Examples.Map.saxpy_correct
#print axioms Ptx.Examples.Buggy.nobound_faults
#print axioms Ptx.Examples.Buggy.tid_races
#print axioms Ptx.Examples.Buggy.sub_wrong
#print axioms Ptx.Examples.Reduce.reduce_correct
#print axioms Ptx.Examples.Scan.scan_correct
#print axioms Ptx.Examples.ReduceAtomic.reduce_atomic_correct
