/- The HiFive1 Embassy firmware replay (see tools/Replay.lean). -/
import tools.Replay
import Theories.Board.Hifive1Revb
import Projects.hifive1.Image
open NoCompiler

def main (args : List String) : IO UInt32 := do
  let some path := args.head? | IO.eprintln "usage: replay TRACE"; return 2
  Replay.Mmio.replay NoCompiler.Hifive1Revb.board NoCompiler.Firmware.segments 0x10015024 path
