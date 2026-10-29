/-
  Run the untrusted analyzer (tools/Analyze.lean) on the hybrid demo and
  write its certificate. Not part of any proof: the certificate is checked
  by the kernel in Proof.lean.

  `lake env lean --run Projects/hifive1/hybrid/demo/AnalyzeDemo.lean OUT [--from-boot]`
  `--from-boot` analyzes the whole program from boot instead of from the
  region's exit (the negative control: abstract interpretation alone).
-/
import tools.Analyze
import Projects.hifive1.hybrid.demo.Config
open E5R E5R.AI Analyze

def main (args : List String) : IO UInt32 := do
  let fromBoot := args.contains "--from-boot"
  let start := if fromBoot then E5R.HybridDemo.Job.boot else E5R.HybridDemo.Job.handover
  let su : Setup := { cfg := E5R.HybridDemo.Job.cfg, boot := start }
  let st ← fixG su none 0 false
  for e in st.errors.toList.take 30 do IO.eprintln e
  IO.eprintln s!"{st.errors.size} errors, {st.nodes.size} nodes"
  if !st.errors.isEmpty then return 1
  let sigma := norm (st.nodes.toList.filterMap fun s =>
    if !s.hnd && !(irqCodesAbs s).isEmpty then
      match s.get 2 with | .vals [sp] => some sp | _ => none
    else none)
  IO.FS.writeFile args[0]! (certSource "E5R.HybridDemo.Cert" st sigma)
  return 0
