import tools.Analyze
import Projects.hifive1.Config
open E5R E5R.AI Analyze

def main (args : List String) : IO UInt32 := do
  let su : Setup := { cfg := E5R.Hifive1.Job.cfg, boot := E5R.Hifive1.Job.boot }
  let st ← fixG su none 0 false
  for e in st.errors.toList.take 30 do IO.eprintln e
  IO.eprintln s!"{st.errors.size} errors"
  if !st.errors.isEmpty then return 1
  let sigma := norm (st.nodes.toList.filterMap fun s =>
    if !s.hnd && !(irqCodesAbs s).isEmpty then
      match s.get 2 with | .vals [sp] => some sp | _ => none
    else none)
  IO.FS.writeFile args[0]! (certSource "E5R.Hifive1.Cert" st sigma)
  IO.println s!"{st.nodes.size} nodes, G has {(st.G.getD []).length} cells, sigma {sigma}"
  return 0
