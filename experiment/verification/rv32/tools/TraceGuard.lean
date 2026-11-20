import tools.Analyze
import Projects.hifive1.Config
open E5R E5R.AI Analyze

/-- Debug aid: find the first transition that loses a given guarded fact. -/
def main (args : List String) : IO UInt32 := do
  let addr := args[0]!.toNat!
  let gaddr := args[1]!.toNat!
  let su : Setup := { cfg := E5R.Hifive1.Job.cfg, boot := E5R.Hifive1.Job.boot }
  let st0 ← fixG su none 0 true
  let st := runOnce su (some (proposeGuards (st0.G.getD [])))
  let P := proposeGuards (st0.G.getD [])
  IO.println s!"P has it: {P.any fun c => c.addr == addr && (c.guard.map (·.1)) == some gaddr}; final G has it: {(st.G.getD []).any fun c => c.addr == addr && (c.guard.map (·.1)) == some gaddr}; nodes {st.nodes.size}"
  for l in st.log do
    if (l.splitOn s!"{addr} if {gaddr}").length > 1 then IO.println (l.take 400)
  let has (s : AState) : Bool := s.mem.any fun c => c.addr == addr && (c.guard.map (·.1)) == some gaddr
  let mut shown := 0
  for i in [0:st.nodes.size] do
    let s := st.nodes[i]!
    if !has s then continue
    match successors.fetchDecode' su.cfg.img s.pc with
    | some (ins, len) =>
      match absExec su.cfg s len ins with
      | some ts =>
        for t in ts do
          if !has t && shown < 12 then
            shown := shown + 1
            IO.println s!"node {i} pc {s.pc} hnd {s.hnd}: {reprStr ins} drops it; regs {brief s}"
      | none => pure ()
    | none => pure ()
  return 0
