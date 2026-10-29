import tools.Analyze
import Projects.hifive1.Config
open E5R E5R.AI Analyze

def main (args : List String) : IO UInt32 := do
  let su : Setup := { cfg := E5R.Hifive1.Job.cfg, boot := E5R.Hifive1.Job.boot }
  let st ← fixG su none 0 false
  let shown := if (← IO.getEnv "E5R_ALL_ERRORS").isSome then st.errors.size else 30
  for e in st.errors.toList.take shown do IO.eprintln e
  IO.eprintln s!"{st.errors.size} errors"
  -- Debug aid: `E5R_LOST_ADDR=<addr>` lists nodes with no plain fact there.
  if let some as ← IO.getEnv "E5R_LOST_ADDR" then
    if let some a := as.toNat? then
      let lost := (List.range st.nodes.size).filter fun j =>
        let s := st.nodes[j]!
        match plain s.mem .abs a .w with
        | none => s.pc ≥ 0x20010084
        | some .top => true
        | some _ => false
      IO.eprintln s!"lost {lost.length}: {(lost.map fun j => (j, st.nodes[j]!.pc, st.nodes[j]!.hnd)).take 400}"
  -- Debug aid: `E5R_DUMP_PC=<pc>` prints every node at that pc.
  if let some pcs ← IO.getEnv "E5R_DUMP_PC" then
    if let some pc := pcs.toNat? then
      for s in st.nodes.toList.filter (·.pc == pc) do IO.eprintln s!"dump: {brief s}"
  -- `--force` writes the certificate even with errors (it will not check),
  -- for measuring the checker.
  if !st.errors.isEmpty && !args.contains "--force" then return 1
  let sigma := norm (st.nodes.toList.filterMap fun s =>
    if !s.hnd && !(irqCodesAbs s).isEmpty then
      match s.get 2 with | .vals [sp] => some sp | _ => none
    else none)
  IO.FS.writeFile args[0]! (certSource "E5R.Hifive1.Cert" st sigma)
  IO.println s!"{st.nodes.size} nodes, G has {(st.G.getD []).length} cells, sigma {sigma}"
  return 0
