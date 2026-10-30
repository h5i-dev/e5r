/-
  Instruction facts for the Rynk session receive step inside the main task's poll
  (0x80003e1a..0x80003e70 and 0x80003f58..0x80003f7c) in the pinned RMK image, generated from the
  model's own decoder (/dev/shm generator, the same `fetchDecode_of` form as
  Projects/rmk/Deframer/TailFetch.lean) and checked by the kernel against the packed ELF.

  Original e5r code, Apache-2.0. Regenerate rather than edit by hand.
-/
import Projects.rmk.Fetch

set_option maxRecDepth 100000

namespace E5R.Rmk.SessionFetch
open E5R E5R.Rmk

theorem f80003e1a : fetchDecode img 0x80003e1a = some (E5R.Instr.opimm (E5R.AluOp.add) 9 22 0x000002cf#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2cfb0493) (by decide +kernel) (by decide +kernel)

theorem f80003e1e : fetchDecode img 0x80003e1e = some (E5R.Instr.opimm (E5R.AluOp.add) 8 23 0x000001c1#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1c1b8413) (by decide +kernel) (by decide +kernel)

theorem f80003e22 : fetchDecode img 0x80003e22 = some (E5R.Instr.opimm (E5R.AluOp.add) 12 0 0x000001e8#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1e800613) (by decide +kernel) (by decide +kernel)

theorem f80003e26 : fetchDecode img 0x80003e26 = some (E5R.Instr.opimm (E5R.AluOp.add) 19 0 0x000001e8#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1e800993) (by decide +kernel) (by decide +kernel)

theorem f80003e2a : fetchDecode img 0x80003e2a = some (E5R.Instr.op (E5R.AluOp.add) 10 0 9, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8526) (by decide +kernel) (by decide +kernel)

theorem f80003e2c : fetchDecode img 0x80003e2c = some (E5R.Instr.op (E5R.AluOp.add) 11 0 8, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x85a2) (by decide +kernel) (by decide +kernel)

theorem f80003e2e : fetchDecode img 0x80003e2e = some (E5R.Instr.auipc 1 0x00019000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x19097) (by decide +kernel) (by decide +kernel)

theorem f80003e32 : fetchDecode img 0x80003e32 = some (E5R.Instr.jalr 1 1 0x0000060c#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x60c080e7) (by decide +kernel) (by decide +kernel)

theorem f80003e36 : fetchDecode img 0x80003e36 = some (E5R.Instr.opimm (E5R.AluOp.and) 10 10 0x00000001#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8905) (by decide +kernel) (by decide +kernel)

theorem f80003e38 : fetchDecode img 0x80003e38 = some (E5R.Instr.branch (E5R.BrCond.eq) 10 0 0x00000120#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x12050063) (by decide +kernel) (by decide +kernel)

theorem f80003e3c : fetchDecode img 0x80003e3c = some (E5R.Instr.op (E5R.AluOp.add) 18 0 11, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x892e) (by decide +kernel) (by decide +kernel)

theorem f80003e3e : fetchDecode img 0x80003e3e = some (E5R.Instr.opimm (E5R.AluOp.add) 12 0 0x000001e8#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1e800613) (by decide +kernel) (by decide +kernel)

theorem f80003e42 : fetchDecode img 0x80003e42 = some (E5R.Instr.op (E5R.AluOp.add) 10 0 9, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8526) (by decide +kernel) (by decide +kernel)

theorem f80003e44 : fetchDecode img 0x80003e44 = some (E5R.Instr.op (E5R.AluOp.add) 11 0 8, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x85a2) (by decide +kernel) (by decide +kernel)

theorem f80003e46 : fetchDecode img 0x80003e46 = some (E5R.Instr.auipc 1 0x00019000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x19097) (by decide +kernel) (by decide +kernel)

theorem f80003e4a : fetchDecode img 0x80003e4a = some (E5R.Instr.jalr 1 1 0x00000542#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x542080e7) (by decide +kernel) (by decide +kernel)

theorem f80003e4e : fetchDecode img 0x80003e4e = some (E5R.Instr.op (E5R.AluOp.sub) 12 19 10, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x40a98633) (by decide +kernel) (by decide +kernel)

theorem f80003e52 : fetchDecode img 0x80003e52 = some (E5R.Instr.opimm (E5R.AluOp.add) 11 0 0x000001e9#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1e900593) (by decide +kernel) (by decide +kernel)

theorem f80003e56 : fetchDecode img 0x80003e56 = some (E5R.Instr.store (E5R.Width.w) 22 10 0x000002db#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2cab2da3) (by decide +kernel) (by decide +kernel)

theorem f80003e5a : fetchDecode img 0x80003e5a = some (E5R.Instr.branch (E5R.BrCond.geu) 12 11 0x000003da#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x3cb67d63) (by decide +kernel) (by decide +kernel)

theorem f80003e5e : fetchDecode img 0x80003e5e = some (E5R.Instr.opimm (E5R.AluOp.add) 9 23 0x000001b1#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1b1b8493) (by decide +kernel) (by decide +kernel)

theorem f80003e62 : fetchDecode img 0x80003e62 = some (E5R.Instr.op (E5R.AluOp.add) 10 0 9, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8526) (by decide +kernel) (by decide +kernel)

theorem f80003e64 : fetchDecode img 0x80003e64 = some (E5R.Instr.op (E5R.AluOp.add) 11 0 8, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x85a2) (by decide +kernel) (by decide +kernel)

theorem f80003e66 : fetchDecode img 0x80003e66 = some (E5R.Instr.op (E5R.AluOp.add) 13 0 18, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x86ca) (by decide +kernel) (by decide +kernel)

theorem f80003e68 : fetchDecode img 0x80003e68 = some (E5R.Instr.auipc 1 0x00018000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x18097) (by decide +kernel) (by decide +kernel)

theorem f80003e6c : fetchDecode img 0x80003e6c = some (E5R.Instr.jalr 1 1 0x0000055e#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x55e080e7) (by decide +kernel) (by decide +kernel)

theorem f80003f58 : fetchDecode img 0x80003f58 = some (E5R.Instr.load (E5R.Width.w) true 19 22 0x000002c7#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2c7b2983) (by decide +kernel) (by decide +kernel)

theorem f80003f5c : fetchDecode img 0x80003f5c = some (E5R.Instr.load (E5R.Width.w) true 21 22 0x000002cf#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2cfb2a83) (by decide +kernel) (by decide +kernel)

theorem f80003f60 : fetchDecode img 0x80003f60 = some (E5R.Instr.load (E5R.Width.w) true 24 22 0x000002d3#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2d3b2c03) (by decide +kernel) (by decide +kernel)

theorem f80003f64 : fetchDecode img 0x80003f64 = some (E5R.Instr.load (E5R.Width.b) false 25 22 0x000002d7#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2d7b4c83) (by decide +kernel) (by decide +kernel)

theorem f80003f68 : fetchDecode img 0x80003f68 = some (E5R.Instr.opimm (E5R.AluOp.add) 12 0 0x000001e8#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1e800613) (by decide +kernel) (by decide +kernel)

theorem f80003f6c : fetchDecode img 0x80003f6c = some (E5R.Instr.op (E5R.AluOp.add) 10 0 9, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8526) (by decide +kernel) (by decide +kernel)

theorem f80003f6e : fetchDecode img 0x80003f6e = some (E5R.Instr.op (E5R.AluOp.add) 11 0 8, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x85a2) (by decide +kernel) (by decide +kernel)

theorem f80003f70 : fetchDecode img 0x80003f70 = some (E5R.Instr.auipc 1 0x00019000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x19097) (by decide +kernel) (by decide +kernel)

theorem f80003f74 : fetchDecode img 0x80003f74 = some (E5R.Instr.jalr 1 1 0x00000606#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x606080e7) (by decide +kernel) (by decide +kernel)

theorem f80003f78 : fetchDecode img 0x80003f78 = some (E5R.Instr.op (E5R.AluOp.add) 18 0 10, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x892a) (by decide +kernel) (by decide +kernel)

theorem f80003f7a : fetchDecode img 0x80003f7a = some (E5R.Instr.op (E5R.AluOp.add) 20 0 11, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8a2e) (by decide +kernel) (by decide +kernel)

end E5R.Rmk.SessionFetch
