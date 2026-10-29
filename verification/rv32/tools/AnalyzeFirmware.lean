import tools.Analyze
import Projects.hifive1.hybrid.RingAI
import Projects.hifive1.Config
open E5R E5R.AI Analyze

def main (args : List String) : IO UInt32 := do
  let opts : Opts := {
    addrSplit := (← IO.getEnv "E5R_ADDR_SPLIT") == some "1"
    tagDepth := ((← IO.getEnv "E5R_TAG_DEPTH").bind String.toNat?).getD 0
    keepAll := (← IO.getEnv "E5R_KEEP_ALL").isSome
    keepGuarded := (← IO.getEnv "E5R_KEEP_GUARDED").isSome
    traceLoss := (← IO.getEnv "E5R_TRACE_LOSS").bind String.toNat?
    tracePc := (← IO.getEnv "E5R_TRACE_PC").bind String.toNat? }
  -- `E5R_RING=1`: use the proved channel ring-head summary (RingAI.spec_sound); a certificate
  -- that relies on it checks with `checkHybrid` and `check_sound_hybrid`, not plain `check`.
  let sums := if (← IO.getEnv "E5R_RING") == some "1" then [E5R.Hifive1.Hybrid.RingAI.spec] else []
  let su : Setup := { cfg := { E5R.Hifive1.Job.cfg with sums }, boot := E5R.Hifive1.Job.boot, opts }
  -- `E5R_KEEP=1` derives kept intervals (Cert.hkeep) from the handler's footprint.
  let st ← if (← IO.getEnv "E5R_KEEP") == some "1" then analyzeKeep su [] else fixG su none 0 false
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
  -- Debug aid: `E5R_HSTORES=1` lists the handler's store addresses.
  if (← IO.getEnv "E5R_HSTORES").isSome then
    for s in st.nodes.toList.filter (·.hnd) do
      match successors.fetchDecode' su.cfg.img s.pc with
      | some (.store wd rs1 _ off, _) => IO.eprintln s!"hstore {s.pc} {reprStr wd} {reprStr (addC (s.get rs1) off.toNat)}"
      | some (.amo _ _ rs1 _, _) => IO.eprintln s!"hstore {s.pc} amo {reprStr (s.get rs1)}"
      | some (.sc _ rs1 _, _) => IO.eprintln s!"hstore {s.pc} sc {reprStr (s.get rs1)}"
      | _ => pure ()
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
