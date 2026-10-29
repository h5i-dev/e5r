/-
  Evidence runner (untrusted, not a proof): main's firmware analyzer
  (tools/Analyze.lean, options as tools/AnalyzeFirmware.lean) with both
  proved channel summaries, RingAI.spec and TailAI.spec. For every node at
  the tail summary's pc it prints whether `TailAI.enterOk` accepts the
  state and, if not, which part fails, then the remaining analyzer reports.

  Original e5r code, Apache-2.0.

  Usage (from verification/rv32, after the modules are built):
    E5R_KEEP=1 E5R_KEEP_GUARDED=1 E5R_ADDR_SPLIT=1 lake env lean --run \
      Projects/hifive1/hybrid/AnalyzeTail.lean [--no-tail]
-/
import tools.Analyze
import Projects.hifive1.hybrid.TailAI
import Projects.hifive1.Config
open E5R E5R.AI Analyze
open E5R.Hifive1.Hybrid

def why (s : AState) : String :=
  let c := RingAI.chan s
  let tl := lookup s.mem .abs (c + 0x18) .w
  s!"pc={s.pc} hnd={s.hnd} mie={reprStr s.mie} wf={s.wf RingAI.cfg} noSym={noSym s} s1={reprStr (s.get 9)} " ++
  s!"tailFact={reprStr tl} tailOk={TailAI.tailOk s c}"

def main (args : List String) : IO UInt32 := do
  let opts : Opts := {
    addrSplit := (← IO.getEnv "E5R_ADDR_SPLIT") == some "1"
    tagDepth := ((← IO.getEnv "E5R_TAG_DEPTH").bind String.toNat?).getD 0
    keepAll := (← IO.getEnv "E5R_KEEP_ALL").isSome
    keepGuarded := (← IO.getEnv "E5R_KEEP_GUARDED").isSome
    freezeG := (← IO.getEnv "E5R_FREEZE_G").isSome }
  let sums := if args.contains "--no-tail" then [RingAI.spec] else [RingAI.spec, TailAI.spec]
  let su : Setup := { cfg := { E5R.Hifive1.Job.cfg with sums }, boot := E5R.Hifive1.Job.boot, opts }
  let st ← if (← IO.getEnv "E5R_KEEP") == some "1" then analyzeKeep su [] else fixG su none 0 false
  let here := st.nodes.toList.filter (·.pc == TailAI.spec.pc)
  IO.println s!"nodes at {TailAI.spec.pc}: {here.length}, accepted by TailAI.enterOk: {(here.filter TailAI.enterOk).length}"
  for s in here do
    IO.println s!"  {if TailAI.enterOk s then "ACCEPT" else "reject"} {why s}"
  for e in st.errors.toList do IO.println s!"report: {e}"
  IO.println s!"{st.errors.size} reports, {st.nodes.size} nodes"
  return 0
