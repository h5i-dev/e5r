/-
Axiom audit of the cross-check (scripts/check-ptx-ieee-crosscheck.sh): every
declaration of lean-ieee754 (`FP.*`), of the rounding core under test
(`Ptx.*`) and of the cross-check (`Crosscheck.*`) may depend only on
`propext`, `Quot.sound` and `Classical.choice`, and none may be an axiom.
-/
import Crosscheck
import Lean
open Lean Elab Command

elab "#audit_crosscheck" : command => do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Quot.sound, ``Classical.choice]
  let prefixes : List Name := [`FP, `Ptx, `Crosscheck]
  let mut checked : Nat := 0
  let mut bad : Array String := #[]
  for (name, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless prefixes.any (·.isPrefixOf mod) do continue
    if let .axiomInfo _ := ci then
      bad := bad.push s!"{name} is an axiom declared in {mod}"
    for a in (← liftCoreM (collectAxioms name)) do
      unless allowed.contains a do
        bad := bad.push s!"{name} ({mod}) depends on {a}"
    checked := checked + 1
  unless bad.isEmpty do
    throwError "axiom audit failed:\n{String.intercalate "\n" (bad.toList.take 30)}"
  logInfo m!"axiom audit: {checked} declarations in FP.*, Ptx.*, Crosscheck.*, standard axioms only"

#audit_crosscheck
