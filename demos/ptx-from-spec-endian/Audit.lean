import E5rProof
import Lean

open Lean Elab Command

partial def dependencyClosure (env : Environment) (n : Name) : StateM NameSet Unit := do
  if (← get).contains n then return
  modify (·.insert n)
  if let some ci := env.find? n then
    for dep in ci.getUsedConstantsAsSet do
      dependencyClosure env dep

elab "#audit_endian" : command => do
  let env ← getEnv
  let allowed := [``propext, ``Quot.sound, ``Classical.choice]
  let roots := [``E5rProof.correct, ``E5rProof.contract_layout, ``E5rProof.implementation_layout]
  let mut deps : NameSet := {}
  for n in roots do
    deps := (dependencyClosure env n).run deps |>.2
  let mut rows : Array Json := #[]
  for n in deps.toList do
    let some ci := env.find? n | throwError "missing dependency {n}"
    if let .axiomInfo _ := ci then
      unless allowed.contains n do throwError "forbidden axiom {n}"
    let modName := (env.getModuleIdxFor? n).map (env.header.moduleNames[·.toNat]!)
    rows := rows.push <| Json.mkObj [("name", toJson n.toString),
      ("module", toJson (modName.map Name.toString)),
      ("dependencies", toJson (ci.getUsedConstantsAsSet.toList.map Name.toString))]
  -- Audit unused proof/statement declarations too, not only the public roots.
  let mut localCount := 0
  for (n, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let modName := env.header.moduleNames[idx.toNat]!
    unless modName == `E5rProof || modName == `E5rSpec do continue
    if let .axiomInfo _ := ci then throwError "declared axiom {n}"
    for ax in (← liftCoreM (collectAxioms n)) do
      unless allowed.contains ax do throwError "{n} depends on forbidden axiom {ax}"
    localCount := localCount + 1
  let axioms ← liftCoreM (collectAxioms ``E5rProof.correct)
  logInfo <| Json.compress <| Json.mkObj [
    ("schema", toJson "e5r.endian.axiom-audit.v1"),
    ("theorem", toJson "E5rProof.correct"),
    ("axioms", toJson (axioms.map Name.toString)),
    ("proof_and_statement_declarations_checked", toJson localCount),
    ("transitive_dependencies", Json.arr rows)]

#audit_endian
