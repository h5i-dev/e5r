/- Replay a QEMU sifive_e trace of the Embassy firmware (tools/ReplayLib.lean). -/
import tools.ReplayLib
import Theories.Board.Hifive1Revb
import Projects.hifive1.Image

def main (args : List String) : IO UInt32 :=
  Replay.replay E5R.Hifive1Revb.board E5R.Firmware.segments true 0x10015024 args[0]!
