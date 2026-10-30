/-
  Instruction facts for the session's None path around the UART receive poll (0x80003f7c..0x80003fa6:
  the pending/discarding tests and the read future's state; 0x8000434c..0x80004374: the Uart16550
  register addresses; 0x800043a8..0x800043b6 and 0x80003b98..0x80003ba4: filled += n and back to the
  loop head), in the pinned RMK image, generated from the model's own decoder (/dev/shm generator,
  the `fetchDecode_of` form of Projects/rmk/Deframer/TailFetch.lean) and checked by the kernel against
  the packed ELF.

  Original e5r code, Apache-2.0. Regenerate rather than edit by hand.
-/
import Projects.rmk.Fetch

set_option maxRecDepth 100000

namespace E5R.Rmk.NoneFetch
open E5R E5R.Rmk

theorem f80003f7c : fetchDecode img 0x80003f7c = some (E5R.Instr.branch (E5R.BrCond.ne) 25 0 0x00000076#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x60c9b63) (by decide +kernel) (by decide +kernel)

theorem f80003f80 : fetchDecode img 0x80003f80 = some (E5R.Instr.branch (E5R.BrCond.geu) 21 24 0x00000072#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x78af963) (by decide +kernel) (by decide +kernel)

theorem f80003f84 : fetchDecode img 0x80003f84 = some (E5R.Instr.store (E5R.Width.w) 22 18 0x000002fb#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2f2b2da3) (by decide +kernel) (by decide +kernel)

theorem f80003f88 : fetchDecode img 0x80003f88 = some (E5R.Instr.store (E5R.Width.w) 22 20 0x000002ff#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2f4b2fa3) (by decide +kernel) (by decide +kernel)

theorem f80003f8c : fetchDecode img 0x80003f8c = some (E5R.Instr.store (E5R.Width.w) 22 19 0x00000307#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x313b23a3) (by decide +kernel) (by decide +kernel)

theorem f80003f90 : fetchDecode img 0x80003f90 = some (E5R.Instr.store (E5R.Width.b) 22 0 0x0000030c#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x300b0623) (by decide +kernel) (by decide +kernel)

theorem f80003f94 : fetchDecode img 0x80003f94 = some (E5R.Instr.store (E5R.Width.w) 22 18 0x000002f3#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2f2b29a3) (by decide +kernel) (by decide +kernel)

theorem f80003f98 : fetchDecode img 0x80003f98 = some (E5R.Instr.store (E5R.Width.w) 22 20 0x000002f7#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2f4b2ba3) (by decide +kernel) (by decide +kernel)

theorem f80003f9c : fetchDecode img 0x80003f9c = some (E5R.Instr.store (E5R.Width.w) 22 19 0x00000303#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x313b21a3) (by decide +kernel) (by decide +kernel)

theorem f80003fa0 : fetchDecode img 0x80003fa0 = some (E5R.Instr.branch (E5R.BrCond.ne) 20 0 0x000003ac#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x3a0a1663) (by decide +kernel) (by decide +kernel)

theorem f80003fa4 : fetchDecode img 0x80003fa4 = some (E5R.Instr.jal 0 0x00000484#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xa151) (by decide +kernel) (by decide +kernel)

theorem f8000434c : fetchDecode img 0x8000434c = some (E5R.Instr.load (E5R.Width.b) false 10 19 0x00000020#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x209c503) (by decide +kernel) (by decide +kernel)

theorem f80004350 : fetchDecode img 0x80004350 = some (E5R.Instr.opimm (E5R.AluOp.and) 10 10 0x000000ff#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xff57513) (by decide +kernel) (by decide +kernel)

theorem f80004354 : fetchDecode img 0x80004354 = some (E5R.Instr.opimm (E5R.AluOp.sll) 11 10 0x00000002#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x251593) (by decide +kernel) (by decide +kernel)

theorem f80004358 : fetchDecode img 0x80004358 = some (E5R.Instr.op (E5R.AluOp.add) 10 10 11, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x952e) (by decide +kernel) (by decide +kernel)

theorem f8000435a : fetchDecode img 0x8000435a = some (E5R.Instr.opimm (E5R.AluOp.srl) 11 10 0x00000008#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x855593) (by decide +kernel) (by decide +kernel)

theorem f8000435e : fetchDecode img 0x8000435e = some (E5R.Instr.branch (E5R.BrCond.ne) 11 0 0x0000009c#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xedd1) (by decide +kernel) (by decide +kernel)

theorem f80004360 : fetchDecode img 0x80004360 = some (E5R.Instr.opimm (E5R.AluOp.add) 9 0 0x00000000#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4481) (by decide +kernel) (by decide +kernel)

theorem f80004362 : fetchDecode img 0x80004362 = some (E5R.Instr.load (E5R.Width.w) true 19 19 0x0000001c#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1c9a983) (by decide +kernel) (by decide +kernel)

theorem f80004366 : fetchDecode img 0x80004366 = some (E5R.Instr.opimm (E5R.AluOp.and) 21 10 0x000000ff#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xff57a93) (by decide +kernel) (by decide +kernel)

theorem f8000436a : fetchDecode img 0x8000436a = some (E5R.Instr.op (E5R.AluOp.add) 21 21 19, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x9ace) (by decide +kernel) (by decide +kernel)

theorem f8000436c : fetchDecode img 0x8000436c = some (E5R.Instr.lui 24 0x80025000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x80025c37) (by decide +kernel) (by decide +kernel)

theorem f80004370 : fetchDecode img 0x80004370 = some (E5R.Instr.opimm (E5R.AluOp.add) 24 24 0xfffffcb0#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xcb0c0c13) (by decide +kernel) (by decide +kernel)

theorem f800043a8 : fetchDecode img 0x800043a8 = some (E5R.Instr.branch (E5R.BrCond.eq) 9 0 0x00000080#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc0c1) (by decide +kernel) (by decide +kernel)

theorem f800043aa : fetchDecode img 0x800043aa = some (E5R.Instr.opimm (E5R.AluOp.add) 11 0 0x00000001#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4585) (by decide +kernel) (by decide +kernel)

theorem f800043ac : fetchDecode img 0x800043ac = some (E5R.Instr.load (E5R.Width.w) true 12 2 0x00000024#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x5612) (by decide +kernel) (by decide +kernel)

theorem f800043ae : fetchDecode img 0x800043ae = some (E5R.Instr.store (E5R.Width.b) 12 11 0x00000000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xb60023) (by decide +kernel) (by decide +kernel)

theorem f800043b2 : fetchDecode img 0x800043b2 = some (E5R.Instr.jal 0 0xfffff7e6#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfe6ff06f) (by decide +kernel) (by decide +kernel)

theorem f80003b98 : fetchDecode img 0x80003b98 = some (E5R.Instr.load (E5R.Width.w) true 10 22 0x000002d3#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2d3b2503) (by decide +kernel) (by decide +kernel)

theorem f80003b9c : fetchDecode img 0x80003b9c = some (E5R.Instr.op (E5R.AluOp.add) 10 10 9, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x9526) (by decide +kernel) (by decide +kernel)

theorem f80003b9e : fetchDecode img 0x80003b9e = some (E5R.Instr.store (E5R.Width.w) 22 10 0x000002d3#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2cab29a3) (by decide +kernel) (by decide +kernel)

theorem f80003ba2 : fetchDecode img 0x80003ba2 = some (E5R.Instr.jal 0 0x00000278#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xaca5) (by decide +kernel) (by decide +kernel)

end E5R.Rmk.NoneFetch
