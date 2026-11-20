/-
  The hybrid demo job: the compiled ring.rs (build/hybrid-ring-O2.elf), its
  board, the PWM property, the boot description, and the abstract state the
  checker starts from at the end of the directly proved region.

  Original e5r code, Apache-2.0.
-/
import Theories.Absint
import Theories.Board.Hifive1Revb
import Projects.hifive1.hybrid.demo.Image

namespace E5R.HybridDemo.Job
open E5R E5R.AI

/-- pwm0.pwmcmp1: every write must be at most 100 (as for the firmware). -/
def pwmcmp1 : Nat := 0x10015024

def cfg : Config where
  board := Hifive1Revb.board
  img := HybridDemo.segments
  stackLow := 0x80000100
  pinLow := 0x80004000
  allow := [⟨pwmcmp1, 0, 100⟩]
  hdepth := 0x400

/-- Every boot state the board allows (as `E5R.Hifive1.Job.boot`): pc at the
    entry, mstatus.MIE = 0, registers and RAM arbitrary. -/
def boot : AState where
  pc := HybridDemo.entry
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

/-- Where the directly proved region hands over: its exit pc, `a0` the head
    pointer, the head below the capacity, CSRs as at boot. -/
def regionExit : Nat := 0x20010028
def head : Nat := 0x80000000

def handover : AState :=
  { boot with
    pc := regionExit
    regs := (List.replicate 31 AV.top).set 9 (AV.const head)
    mem := [⟨.abs, head, .w, .vals [0, 1, 2, 3], none⟩] }

end E5R.HybridDemo.Job
