/-
  Instruction facts for the session's unpark call site (0x80003fd8..0x80003ff2: load the parked
  count, call `unpark_pending`, jump back to the loop head 0x80003e1a) in the pinned RMK image,
  generated from the model's own decoder (/dev/shm generator, the `fetchDecode_of` form of
  Projects/rmk/Deframer/TailFetch.lean) and checked by the kernel against the packed ELF.

  Original e5r code, Apache-2.0. Regenerate rather than edit by hand.
-/
import Projects.rmk.Fetch

set_option maxRecDepth 100000

namespace E5R.Rmk.UnparkSiteFetch
open E5R E5R.Rmk

theorem f80003fd8 : fetchDecode img 0x80003fd8 = some (E5R.Instr.load (E5R.Width.w) true 13 22 0x000002db#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2dbb2683) (by decide +kernel) (by decide +kernel)

theorem f80003fdc : fetchDecode img 0x80003fdc = some (E5R.Instr.opimm (E5R.AluOp.add) 10 23 0x000003bd#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x3bdb8513) (by decide +kernel) (by decide +kernel)

theorem f80003fe0 : fetchDecode img 0x80003fe0 = some (E5R.Instr.opimm (E5R.AluOp.add) 11 23 0x000001c1#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1c1b8593) (by decide +kernel) (by decide +kernel)

theorem f80003fe4 : fetchDecode img 0x80003fe4 = some (E5R.Instr.opimm (E5R.AluOp.add) 12 0 0x000001e8#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1e800613) (by decide +kernel) (by decide +kernel)

theorem f80003fe8 : fetchDecode img 0x80003fe8 = some (E5R.Instr.auipc 1 0x00019000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x19097) (by decide +kernel) (by decide +kernel)

theorem f80003fec : fetchDecode img 0x80003fec = some (E5R.Instr.jalr 1 1 0x0000040a#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x40a080e7) (by decide +kernel) (by decide +kernel)

theorem f80003ff0 : fetchDecode img 0x80003ff0 = some (E5R.Instr.jal 0 0xfffffe2a#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xb52d) (by decide +kernel) (by decide +kernel)

end E5R.Rmk.UnparkSiteFetch
