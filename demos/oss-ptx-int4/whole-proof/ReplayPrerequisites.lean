/- Independent kernel replay and transitive axiom audit for prerequisite
modules. This is not the official FP4 statement/checker acceptance. -/
import Lean
open Lean

private def allowed : List Name := [``propext, ``Quot.sound, ``Classical.choice]

private partial def axiomsOf (env : Environment) (n : Name) : StateM (NameSet × NameSet) Unit := do
  let (seen, _) ← get
  if seen.contains n then return
  modify fun (s,a) => (s.insert n,a)
  match env.find? n with
  | some (.axiomInfo _) => modify fun (s,a) => (s,a.insert n)
  | some ci => for m in ci.getUsedConstantsAsSet do axiomsOf env m
  | none => pure ()

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then IO.eprintln "expected prerequisite module names"; return 2
  initSearchPath (← findSysroot)
  for arg in args do
    let mod := arg.toName
    let env ← importModules #[{ module := mod }] {} (trustLevel := 0)
    let some idx := env.getModuleIdx? mod | IO.eprintln s!"missing {mod}"; return 1
    let imports := env.header.moduleData[idx.toNat]!.imports
    let mut mine : Std.HashMap Name ConstantInfo := {}
    let mut state : NameSet × NameSet := ({}, {})
    for (n,ci) in env.constants.map₁.toList do
      if env.getModuleIdxFor? n == some idx then
        if let .axiomInfo _ := ci then IO.eprintln s!"new axiom {n}"; return 1
        mine := mine.insert n ci
        state := ((axiomsOf env n).run state).2
    let bad := state.2.toList.filter (fun a => !allowed.contains a)
    if !bad.isEmpty then IO.eprintln s!"forbidden axioms {bad}"; return 1
    let base ← importModules imports {} (trustLevel := 0)
    try
      discard <| base.toKernelEnv.replay mine
    catch e =>
      IO.eprintln s!"replay failed for {mod}: {e}"; return 1
    IO.println (Json.compress (Json.mkObj [
      ("module", toJson arg), ("declarations", toJson mine.size),
      ("axioms", toJson (state.2.toList.map toString)),
      ("kernel_replay", toJson true), ("fp4_whole_kernel_acceptance", toJson false)]))
  return 0
