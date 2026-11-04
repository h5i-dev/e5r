/-
The checker for supplied proofs (`e5r ptx check --proof`).

  proofcheck STATEMENT_MODULE PROOF_MODULE THEOREM STATEMENT

`e5r` generates STATEMENT_MODULE (the kernel, the spec and
`STATEMENT : Prop`) and compiles it and the supplied PROOF_MODULE to
`.olean` files. This program then, independently of how the proof module
was elaborated:

1. refuses imports other than the statement module, `Ptx.*`, `Init.*`,
   `Std.*` and `Lean.*` (the `Ptx` library is audited by `Audit.lean`);
2. refuses any `axiom` declared in the proof module;
3. sends every declaration of the proof module to the kernel again
   (`Kernel.Environment.replay`) on top of an environment that has only the
   proof module's imports, so options such as `debug.skipKernelTC` or
   elaborator extensions cannot let an unchecked declaration through;
4. requires THEOREM to be a theorem whose type is the constant STATEMENT,
   syntactically, so the proof is of exactly the generated statement;
5. requires the axioms THEOREM depends on, transitively, to be among
   `propext`, `Quot.sound` and `Classical.choice` (this excludes `sorryAx`
   and the `Lean.ofReduceBool` / `Lean.trustCompiler` that `native_decide`
   adds).

It prints one JSON object and exits 0 only when every check passes.
-/
import Lean

open Lean

def allowedAxioms : List Name := [``propext, ``Quot.sound, ``Classical.choice]

def allowedImport (stmt : Name) (m : Name) : Bool :=
  m == stmt || (`Ptx).isPrefixOf m || (`Init).isPrefixOf m || (`Std).isPrefixOf m ||
    (`Lean).isPrefixOf m || m == `Init || m == `Std || m == `Lean

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

def main (args : List String) : IO UInt32 := do
  let [stmtMod, proofMod, thm, stmt] := args
    | fail "usage: proofcheck STATEMENT_MODULE PROOF_MODULE THEOREM STATEMENT"
  let stmtMod := stmtMod.toName
  let proofMod := proofMod.toName
  let thm := thm.toName
  let stmt := stmt.toName
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := proofMod }] {} (trustLevel := 0)
  let some idx := env.getModuleIdx? proofMod | fail s!"module {proofMod} not loaded"
  let imports := env.header.moduleData[idx.toNat]!.imports
  for i in imports do
    unless allowedImport stmtMod i.module do
      return ← fail s!"the proof imports {i.module}; only the statement module, Ptx.*, Init, Std and Lean are allowed"
  unless imports.any (·.module == stmtMod) do
    return ← fail s!"the proof does not import the statement module {stmtMod}"
  -- the proof module's own declarations
  let mut mine : Std.HashMap Name ConstantInfo := {}
  for (n, ci) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some idx then
      if let .axiomInfo _ := ci then
        return ← fail s!"the proof declares the axiom {n}"
      mine := mine.insert n ci
  -- 3: the kernel checks every one of them again
  let base ← importModules imports {} (trustLevel := 0)
  try
    discard <| base.toKernelEnv.replay mine
  catch e =>
    return ← fail s!"the kernel rejects a declaration of the proof: {e}"
  -- 4: exactly the generated statement
  let some ci := env.find? thm | fail s!"the proof has no theorem {thm}"
  unless env.getModuleIdxFor? thm == some idx do
    return ← fail s!"{thm} is not declared by the proof module"
  let .thmInfo tv := ci | fail s!"{thm} is not a theorem"
  unless tv.type == mkConst stmt do
    return ← fail s!"{thm} does not state {stmt}: its type is {tv.type}"
  unless (env.find? stmt).isSome && env.getModuleIdxFor? stmt == env.getModuleIdx? stmtMod do
    return ← fail s!"{stmt} is not the generated statement"
  -- 5: the axioms
  let ((), (_, axs)) := (axiomsOf env thm).run ({}, #[])
  let bad := axs.filter (fun a => !allowedAxioms.contains a)
  let axj := Json.arr (axs.map fun a => Json.str a.toString)
  unless bad.isEmpty do
    IO.println s!"\{\"ok\": false, \"reason\": {jstr s!"axioms outside the allowed set: {bad.toList}"}, \"axioms\": {axj.compress}}"
    return 1
  IO.println s!"\{\"ok\": true, \"declarations\": {mine.size}, \"axioms\": {axj.compress}}"
  return 0
