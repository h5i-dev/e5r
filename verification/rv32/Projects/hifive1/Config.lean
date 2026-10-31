/-
  The verification job for the HiFive1 Embassy firmware: board, image,
  property, and the abstract boot state the checker starts from.
-/
import Theories.Absint
import Theories.Board.Hifive1Revb
import Projects.hifive1.Image

namespace E5R.Hifive1.Job
open E5R E5R.AI

/-- pwm0.pwmcmp1: every write must be a duty of at most 100. -/
def pwmcmp1 : Nat := 0x10015024

def cfg : Config where
  board := Hifive1Revb.board
  img := Firmware.segments
  stackLow := 0x800000e0
  pinLow := 0x80003fe0
  allow := [⟨pwmcmp1, 0, 100⟩]
  hdepth := 0x400

/-- Every boot state the board allows (boards/hifive1-revb.json): pc at the
    entry, mstatus.MIE = 0, everything else arbitrary within the
    implemented CSR bits. -/
def boot : AState where
  pc := Firmware.entry
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

end E5R.Hifive1.Job
