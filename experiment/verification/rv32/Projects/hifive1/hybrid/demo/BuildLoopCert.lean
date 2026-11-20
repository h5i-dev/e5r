/-
  Untrusted certificate builder for the loop demo: explores the program
  with the checker's own transfer function (`absExec`), stops at the
  delegated region entry (a node with no successors), and continues from the
  region's abstract exit state (`Job.post`). Nothing here is trusted: the
  certificate is evaluated by the kernel in LoopProof.lean.

  `lake env lean --run Projects/hifive1/hybrid/demo/BuildLoopCert.lean OUT [--no-delegate]`
  `--no-delegate` explores the region too (abstract interpretation alone).
-/
import tools.Analyze
import Projects.hifive1.hybrid.demo.LoopConfig
open E5R E5R.AI E5R.HybridLoop.Job

def main (args : List String) : IO UInt32 := do
  let delegate := !args.contains "--no-delegate"
  let mut nodes : Array AState := #[boot]
  let mut edges : Array (List Edge) := #[[]]
  let mut work : Array Nat := #[0]
  let mut errors := 0
  let find (nodes : Array AState) (t : AState) : Option Nat :=
    (List.range nodes.size).find? fun j => t.leq nodes[j]!
  while h : work.size > 0 do
    let j := work[work.size - 1]
    work := work.pop
    let s := nodes[j]!
    if nodes.size > 2000 then IO.eprintln "node cap"; return 2
    let succs : List AState ←
      if delegate && s.pc == regionEntry && !s.hnd then
        if !enterOk s then
          IO.eprintln s!"node {j}: region entry not accepted: wf {s.wf cfg} noSym {noSym s} mie {reprStr s.mie} a2 {reprStr (s.get 12)} a0 {reprStr (s.get 10)}"
          errors := errors + 1
        -- The delegated node keeps no edges; the exit state is a new root.
        pure [post s]
      else match successors.fetchDecode' cfg.img s.pc with
        | some (i, len) => match absExec cfg s len i with
          | some ts => pure ts
          | none => IO.eprintln s!"node {j} pc {s.pc}: {reprStr i} may fault: regs {reprStr s.regs}"
                    errors := errors + 1; pure []
        | none => IO.eprintln s!"node {j} pc {s.pc}: no instruction"; errors := errors + 1; pure []
    let mut es : List Edge := []
    for t in succs do
      let k ← match find nodes t with
        | some k => pure k
        | none => do
          nodes := nodes.push t; edges := edges.push []; work := work.push (nodes.size - 1)
          pure (nodes.size - 1)
      es := es ++ [⟨[k], none, false⟩]
    if !(delegate && s.pc == regionEntry && !s.hnd) then edges := edges.set! j es
  IO.eprintln s!"{nodes.size} nodes, {errors} errors"
  if errors > 0 then return 1
  let st : Analyze.St := { nodes := nodes, edges := edges }
  let src := Analyze.certSource "E5R.HybridLoop.Cert" st []
  let dl := if delegate then s!"  delegate := [({regionEntry}, 0)]\n" else ""
  IO.FS.writeFile args[0]! (src.replace "end E5R.HybridLoop.Cert" (dl ++ "end E5R.HybridLoop.Cert"))
  return 0
