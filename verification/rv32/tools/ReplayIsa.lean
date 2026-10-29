/- Replay a QEMU user-mode trace of an instruction test program
   (tools/gen_isa_test.py). The program's image is read at run time from the
   ELF file by the independent Lean reader (Theories/FlashElf.lean), so one
   build of this tool checks any number of generated programs. No CSRs,
   devices or interrupts are involved. -/
import tools.ReplayLib
import Theories.FlashElf
import Theories.Board.QemuUserRv32
open E5R

def main (args : List String) : IO UInt32 := do
  let bytes ← IO.FS.readBinFile args[0]!
  let B := E5R.QemuUserRv32.board
  let w : FlashElf.Windows := ⟨0x10000, 0x10000, B.ramBase, B.ramSize⟩
  match FlashElf.loadFlash w (bytes.toList.map (·.toNat)) with
  | .error e => IO.eprintln s!"{args[0]!}: {e}"; return 2
  | .ok (_, segs) => Replay.replay B segs false 0 args[1]!
