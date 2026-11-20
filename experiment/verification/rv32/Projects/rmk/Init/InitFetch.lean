/-
  Instruction facts for the session task's initialization (0x80003b38..0x80003b42 and
  0x80003d8e..0x80003e1a: the s10/s11 set-up, the session statics, `TopicSubscribers::new` and
  `memset` calls, the deframer reset) in the pinned RMK image, generated from the model's own
  decoder (the `fetchDecode_of` form of Projects/rmk/Deframer/TailFetch.lean) and checked by the
  kernel against the packed ELF.

  Original e5r code, Apache-2.0. Regenerate rather than edit by hand.
-/
import Projects.rmk.Fetch

set_option maxRecDepth 100000

namespace E5R.Rmk.InitFetch
open E5R E5R.Rmk

theorem f80003b38 : fetchDecode img 0x80003b38 = some (E5R.Instr.opimm (E5R.AluOp.add) 26 22 0x00000333#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x333b0d13) (by decide +kernel) (by decide +kernel)

theorem f80003b3c : fetchDecode img 0x80003b3c = some (E5R.Instr.opimm (E5R.AluOp.add) 27 22 0x00000330#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x330b0d93) (by decide +kernel) (by decide +kernel)

theorem f80003b40 : fetchDecode img 0x80003b40 = some (E5R.Instr.jal 0 0x0000024e#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xa4b9) (by decide +kernel) (by decide +kernel)

theorem f80003d8e : fetchDecode img 0x80003d8e = some (E5R.Instr.opimm (E5R.AluOp.add) 10 23 0x000000f1#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xf1b8513) (by decide +kernel) (by decide +kernel)

theorem f80003d92 : fetchDecode img 0x80003d92 = some (E5R.Instr.store (E5R.Width.w) 22 10 0x000002df#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2cab2fa3) (by decide +kernel) (by decide +kernel)

theorem f80003d96 : fetchDecode img 0x80003d96 = some (E5R.Instr.load (E5R.Width.w) true 12 2 0x0000001c#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4672) (by decide +kernel) (by decide +kernel)

theorem f80003d98 : fetchDecode img 0x80003d98 = some (E5R.Instr.store (E5R.Width.w) 22 12 0x000002e3#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2ecb21a3) (by decide +kernel) (by decide +kernel)

theorem f80003d9c : fetchDecode img 0x80003d9c = some (E5R.Instr.load (E5R.Width.w) true 11 2 0x00000018#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x45e2) (by decide +kernel) (by decide +kernel)

theorem f80003d9e : fetchDecode img 0x80003d9e = some (E5R.Instr.store (E5R.Width.w) 22 11 0x000002e7#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2ebb23a3) (by decide +kernel) (by decide +kernel)

theorem f80003da2 : fetchDecode img 0x80003da2 = some (E5R.Instr.store (E5R.Width.b) 22 0 0x000002ee#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2e0b0723) (by decide +kernel) (by decide +kernel)

theorem f80003da6 : fetchDecode img 0x80003da6 = some (E5R.Instr.store (E5R.Width.w) 22 10 0x000002c3#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2cab21a3) (by decide +kernel) (by decide +kernel)

theorem f80003daa : fetchDecode img 0x80003daa = some (E5R.Instr.store (E5R.Width.w) 22 12 0x000002c7#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2ccb23a3) (by decide +kernel) (by decide +kernel)

theorem f80003dae : fetchDecode img 0x80003dae = some (E5R.Instr.store (E5R.Width.w) 22 11 0x000002cb#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2cbb25a3) (by decide +kernel) (by decide +kernel)

theorem f80003db2 : fetchDecode img 0x80003db2 = some (E5R.Instr.lui 11 0x0007a000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x7a5b7) (by decide +kernel) (by decide +kernel)

theorem f80003db6 : fetchDecode img 0x80003db6 = some (E5R.Instr.load (E5R.Width.w) true 12 10 0x00000038#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x5d10) (by decide +kernel) (by decide +kernel)

theorem f80003db8 : fetchDecode img 0x80003db8 = some (E5R.Instr.load (E5R.Width.w) true 13 10 0x00000044#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4174) (by decide +kernel) (by decide +kernel)

theorem f80003dba : fetchDecode img 0x80003dba = some (E5R.Instr.load (E5R.Width.w) true 14 10 0x00000048#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4538) (by decide +kernel) (by decide +kernel)

theorem f80003dbc : fetchDecode img 0x80003dbc = some (E5R.Instr.load (E5R.Width.b) false 10 10 0x0000004c#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4c54503) (by decide +kernel) (by decide +kernel)

theorem f80003dc0 : fetchDecode img 0x80003dc0 = some (E5R.Instr.opimm (E5R.AluOp.add) 11 11 0x00000120#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x12058593) (by decide +kernel) (by decide +kernel)

theorem f80003dc4 : fetchDecode img 0x80003dc4 = some (E5R.Instr.store (E5R.Width.w) 22 0 0x00000053#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x40b29a3) (by decide +kernel) (by decide +kernel)

theorem f80003dc8 : fetchDecode img 0x80003dc8 = some (E5R.Instr.store (E5R.Width.w) 22 0 0x00000057#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x40b2ba3) (by decide +kernel) (by decide +kernel)

theorem f80003dcc : fetchDecode img 0x80003dcc = some (E5R.Instr.store (E5R.Width.w) 22 11 0x0000005b#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4bb2da3) (by decide +kernel) (by decide +kernel)

theorem f80003dd0 : fetchDecode img 0x80003dd0 = some (E5R.Instr.store (E5R.Width.w) 22 0 0x0000005f#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x40b2fa3) (by decide +kernel) (by decide +kernel)

theorem f80003dd4 : fetchDecode img 0x80003dd4 = some (E5R.Instr.store (E5R.Width.w) 22 13 0x00000063#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x6db21a3) (by decide +kernel) (by decide +kernel)

theorem f80003dd8 : fetchDecode img 0x80003dd8 = some (E5R.Instr.store (E5R.Width.w) 22 14 0x00000067#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x6eb23a3) (by decide +kernel) (by decide +kernel)

theorem f80003ddc : fetchDecode img 0x80003ddc = some (E5R.Instr.store (E5R.Width.w) 22 12 0x0000006b#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x6cb25a3) (by decide +kernel) (by decide +kernel)

theorem f80003de0 : fetchDecode img 0x80003de0 = some (E5R.Instr.store (E5R.Width.b) 22 10 0x0000006f#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x6ab07a3) (by decide +kernel) (by decide +kernel)

theorem f80003de4 : fetchDecode img 0x80003de4 = some (E5R.Instr.store (E5R.Width.b) 22 0 0x00000070#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x60b0823) (by decide +kernel) (by decide +kernel)

theorem f80003de8 : fetchDecode img 0x80003de8 = some (E5R.Instr.store (E5R.Width.b) 22 10 0x00000071#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x6ab08a3) (by decide +kernel) (by decide +kernel)

theorem f80003dec : fetchDecode img 0x80003dec = some (E5R.Instr.opimm (E5R.AluOp.add) 10 23 0x00000161#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x161b8513) (by decide +kernel) (by decide +kernel)

theorem f80003df0 : fetchDecode img 0x80003df0 = some (E5R.Instr.auipc 1 0x00013000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x13097) (by decide +kernel) (by decide +kernel)

theorem f80003df4 : fetchDecode img 0x80003df4 = some (E5R.Instr.jalr 1 1 0x00000762#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x762080e7) (by decide +kernel) (by decide +kernel)

theorem f80003df8 : fetchDecode img 0x80003df8 = some (E5R.Instr.opimm (E5R.AluOp.add) 10 23 0x000001c1#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1c1b8513) (by decide +kernel) (by decide +kernel)

theorem f80003dfc : fetchDecode img 0x80003dfc = some (E5R.Instr.opimm (E5R.AluOp.add) 12 0 0x000001e8#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1e800613) (by decide +kernel) (by decide +kernel)

theorem f80003e00 : fetchDecode img 0x80003e00 = some (E5R.Instr.opimm (E5R.AluOp.add) 11 0 0x00000000#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4581) (by decide +kernel) (by decide +kernel)

theorem f80003e02 : fetchDecode img 0x80003e02 = some (E5R.Instr.auipc 1 0x0001d000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1d097) (by decide +kernel) (by decide +kernel)

theorem f80003e06 : fetchDecode img 0x80003e06 = some (E5R.Instr.jalr 1 1 0xfffffdb0#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xdb0080e7) (by decide +kernel) (by decide +kernel)

theorem f80003e0a : fetchDecode img 0x80003e0a = some (E5R.Instr.store (E5R.Width.w) 22 0 0x000002cf#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2c0b27a3) (by decide +kernel) (by decide +kernel)

theorem f80003e0e : fetchDecode img 0x80003e0e = some (E5R.Instr.store (E5R.Width.w) 22 0 0x000002d3#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2c0b29a3) (by decide +kernel) (by decide +kernel)

theorem f80003e12 : fetchDecode img 0x80003e12 = some (E5R.Instr.store (E5R.Width.b) 22 0 0x000002d7#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2c0b0ba3) (by decide +kernel) (by decide +kernel)

theorem f80003e16 : fetchDecode img 0x80003e16 = some (E5R.Instr.store (E5R.Width.b) 22 0 0x000002ed#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2e0b06a3) (by decide +kernel) (by decide +kernel)

end E5R.Rmk.InitFetch
