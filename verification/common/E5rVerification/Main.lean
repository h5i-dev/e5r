import E5rVerification.ProofCheck
open Lean E5rVerification

-- Exact mode is for tool-generated statements. Named mode audits reviewed
-- firmware claims after the backend has replayed its complete source closure.
def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  match args with
  | "exact" :: stmtMod :: proofMod :: thm :: stmt :: prefixes =>
    let stmtMod := stmtMod.toName
    let proofMod := proofMod.toName
    let thm := thm.toName
    let stmt := stmt.toName
    let env ← importModules #[{ module := proofMod }] {} (trustLevel := 0)
    let some idx := env.getModuleIdx? proofMod | fail s!"module {proofMod} not loaded"
    let imports := env.header.moduleData[idx.toNat]!.imports
    for i in imports do
      unless i.module == stmtMod || prefixes.any (fun p => p.toName.isPrefixOf i.module) do
        return ← fail s!"the proof imports {i.module}; only the statement module and configured trusted prefixes are allowed"
    unless imports.any (·.module == stmtMod) do
      return ← fail s!"the proof does not import the statement module {stmtMod}"
    let statementReplay ← replayModule env stmtMod
    if let .error why := statementReplay then return ← fail s!"generated statement: {why}"
    let replay ← replayModule env proofMod
    if let .error why := replay then return ← fail why
    let count := replay.toOption.getD 0
    let some (.thmInfo tv) := env.find? thm | fail s!"the proof has no theorem {thm}"
    unless env.getModuleIdxFor? thm == some idx do
      return ← fail s!"{thm} is not declared by the proof module"
    unless tv.type == mkConst stmt do
      return ← fail s!"{thm} does not state {stmt}: its type is {tv.type}"
    unless (env.find? stmt).isSome && env.getModuleIdxFor? stmt == env.getModuleIdx? stmtMod do
      return ← fail s!"{stmt} is not the generated statement"
    let audited := auditTheorem env thm
    if let .error why := audited then return ← fail why
    let axs := audited.toOption.getD #[]
    let axj := Json.arr (axs.map fun a => Json.str a.toString)
    IO.println s!"\{\"ok\": true, \"declarations\": {count}, \"axioms\": {axj.compress}, \"binding\": \"exact_generated_statement\"}"
    return 0
  | "named" :: rest =>
    let mods := rest.takeWhile (· != "--")
    let names := (rest.dropWhile (· != "--")).drop 1
    if mods.isEmpty || names.isEmpty then return ← fail "no modules or requested theorems"
    let env ← importModules (mods.toArray.map fun m => { module := m.toName }) {} (trustLevel := 0)
    -- Validate actual olean headers as well as the backend's source scan.
    -- Init is Lean's implicit trusted prelude; all other imports must precede
    -- this module in the checked closure supplied by the backend.
    let mut earlier : List Name := [`Init]
    for mod in mods do
      let some idx := env.getModuleIdx? mod.toName | return ← fail s!"module {mod} not loaded"
      for i in env.header.moduleData[idx.toNat]!.imports do
        unless earlier.contains i.module do
          return ← fail s!"{mod} imports unchecked module {i.module}"
      earlier := mod.toName :: earlier
    let mut reports : Array Json := #[]
    for name in names do
      let audited := auditTheorem env name.toName
      if let .error why := audited then return ← fail why
      let axs := audited.toOption.getD #[]
      reports := reports.push <| Json.mkObj [("name", Json.str name),
        ("axioms", Json.arr (axs.map fun a => Json.str a.toString))]
    IO.println <| (Json.mkObj [("ok", Json.bool true), ("theorems", Json.arr reports),
      ("binding", Json.str "reviewed_theorem_names")]).compress
    return 0
  | _ => fail "usage: proofcheck exact STATEMENT_MODULE PROOF_MODULE THEOREM STATEMENT PREFIX... | named MODULE THEOREM..."
