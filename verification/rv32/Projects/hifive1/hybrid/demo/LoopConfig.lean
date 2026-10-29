/-
  The loop variant of the hybrid demo (ring_loop.rs, build/hybrid-ring-loop-O2.elf):
  the ring head is stepped on every iteration of the main loop. The checker
  covers the loop, delegating the wrap-and-store region at 0x20010018 to a
  directly proved summary; the abstract summary (`enterOk`, `post`) says what
  the region needs from, and gives back to, the abstract states around it.

  Original e5r code, Apache-2.0.
-/
import Theories.Absint
import Theories.Board.Hifive1Revb
import Projects.hifive1.hybrid.demo.LoopImage

namespace E5R.HybridLoop.Job
open E5R E5R.AI

def pwmcmp1 : Nat := 0x10015024

def cfg : Config where
  board := Hifive1Revb.board
  img := HybridLoop.segments
  stackLow := 0x80000100
  pinLow := 0x80004000
  allow := [⟨pwmcmp1, 0, 100⟩]
  hdepth := 0x400

/-- Every boot state the board allows (as `E5R.Hifive1.Job.boot`). -/
def boot : AState where
  pc := HybridLoop.entry
  regs := List.replicate 31 .top
  mem := []
  mie := .no
  mpie := .any
  mpp := [0, 3]
  mieReg := mkVals [0, 8, 0x80, 0x88, 0x800, 0x808, 0x880, 0x888]
  mtvec := .top
  mepc := .top
  mcause := .top
  mscratch := .top
  hnd := false

/-- The directly proved region: `a2` the head, `a0` its address. -/
def regionEntry : Nat := 0x20010018
def regionExit : Nat := 0x20010028

/-- The head below the capacity, MIE clear, the head address an exact,
    aligned RAM word, and the state well formed for the checker. -/
def enterOk (s : AState) : Bool :=
  s.pc == regionEntry && !s.hnd && s.mie == .no && s.wf cfg && noSym s &&
  (s.get 12).leq (.rng 0 3) &&
  match s.get 10 with
  | .vals [a] => a % 4 == 0 && cfg.board.inRam (w a) 4 && a < M32
  | _ => false

/-- The abstract state at the region's exit: the new head in `a2`, the wrap
    mask in `a3`, the head word stored, everything else as at entry. -/
def post (s : AState) : AState :=
  let a := match s.get 10 with | .vals [a] => a | _ => 0
  { (s.set 12 (.vals [0, 1, 2, 3])).set 13 (.vals [0, 0xffffffff]) with
    pc := regionExit
    mem := storeStrong s.mem .abs a .w (.vals [0, 1, 2, 3]) }

end E5R.HybridLoop.Job
