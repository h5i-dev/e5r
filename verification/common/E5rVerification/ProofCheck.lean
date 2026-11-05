/- Shared acceptance primitives. Only Lean core; no ISA or platform semantics. -/
import Lean
namespace E5rVerification
open Lean

def allowedAxioms : List Name := [``propext, ``Quot.sound, ``Classical.choice]

/-- Every axiom `n` depends on. -/
partial def axiomsOf (env : Environment) (n : Name) : StateM (NameSet × Array Name) Unit := do
  let (seen, _) ← get
  if seen.contains n then return
  modify fun (s, a) => (s.insert n, a)
  match env.find? n with
  | some (.axiomInfo _) => modify fun (s, a) => (s, a.push n)
  | some ci =>
    for m in ci.getUsedConstantsAsSet do
      axiomsOf env m
  | none => pure ()

def jstr (s : String) : String := Json.compress (Json.str s)

def fail (why : String) : IO UInt32 := do
  IO.println s!"\{\"ok\": false, \"reason\": {jstr why}}"
  return 1


/-- Replay a module's own declarations against its imports, rejecting axioms. -/
def replayModule (env : Environment) (mod : Name) : IO (Except String Nat) := do
  let some idx := env.getModuleIdx? mod | return .error s!"module {mod} not loaded"
  let mut mine : Std.HashMap Name ConstantInfo := {}
  for (n, ci) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some idx then
      if let .axiomInfo _ := ci then
        return .error s!"the proof declares the axiom {n}"
      mine := mine.insert n ci
  let base ← importModules env.header.moduleData[idx.toNat]!.imports {} (trustLevel := 0)
  try
    discard <| base.toKernelEnv.replay mine
  catch e =>
    return .error s!"the kernel rejects a declaration of the proof: {e}"
  return .ok mine.size

/-- An audited name is a theorem, with only the standard transitive axioms. -/
def auditTheorem (env : Environment) (thm : Name) : Except String (Array Name) := do
  let some (.thmInfo _) := env.find? thm | .error s!"no theorem {thm}"
  let ((), (_, axs)) := (axiomsOf env thm).run ({}, #[])
  let bad := axs.filter (fun a => !allowedAxioms.contains a)
  unless bad.isEmpty do
    .error s!"axioms outside the allowed set: {bad.toList}"
  return axs
end E5rVerification
