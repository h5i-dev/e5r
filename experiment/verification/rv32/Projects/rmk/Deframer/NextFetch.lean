/-
  Instruction facts for `Deframer::next` (0x8001d43a..0x8001d576), the `cobs::dec::decode_in_place`
  wrapper (0x8001e006..0x8001e02e, not the COBS decoder itself, which the COBS worker owns) and
  the slice-range check `core::slice::index::range` (0x8001ad76..0x8001ad80) in the pinned RMK
  image, generated from the model's own decoder (/dev/shm generator, the same `fetchDecode_of` form
  as Projects/rmk/Deframer/TailFetch.lean) and checked by the kernel against the packed ELF.

  Original e5r code, Apache-2.0. Regenerate rather than edit by hand.
-/
import Projects.rmk.Fetch

set_option maxRecDepth 100000

namespace E5R.Rmk.NextFetch
open E5R E5R.Rmk

theorem f8001d43a : fetchDecode img 0x8001d43a = some (E5R.Instr.opimm (E5R.AluOp.add) 2 2 0xffffffc0#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x7139) (by decide +kernel) (by decide +kernel)

theorem f8001d43c : fetchDecode img 0x8001d43c = some (E5R.Instr.store (E5R.Width.w) 2 1 0x0000003c#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xde06) (by decide +kernel) (by decide +kernel)

theorem f8001d43e : fetchDecode img 0x8001d43e = some (E5R.Instr.store (E5R.Width.w) 2 8 0x00000038#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xdc22) (by decide +kernel) (by decide +kernel)

theorem f8001d440 : fetchDecode img 0x8001d440 = some (E5R.Instr.store (E5R.Width.w) 2 9 0x00000034#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xda26) (by decide +kernel) (by decide +kernel)

theorem f8001d442 : fetchDecode img 0x8001d442 = some (E5R.Instr.store (E5R.Width.w) 2 18 0x00000030#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xd84a) (by decide +kernel) (by decide +kernel)

theorem f8001d444 : fetchDecode img 0x8001d444 = some (E5R.Instr.store (E5R.Width.w) 2 19 0x0000002c#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xd64e) (by decide +kernel) (by decide +kernel)

theorem f8001d446 : fetchDecode img 0x8001d446 = some (E5R.Instr.store (E5R.Width.w) 2 20 0x00000028#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xd452) (by decide +kernel) (by decide +kernel)

theorem f8001d448 : fetchDecode img 0x8001d448 = some (E5R.Instr.store (E5R.Width.w) 2 21 0x00000024#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xd256) (by decide +kernel) (by decide +kernel)

theorem f8001d44a : fetchDecode img 0x8001d44a = some (E5R.Instr.store (E5R.Width.w) 2 22 0x00000020#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xd05a) (by decide +kernel) (by decide +kernel)

theorem f8001d44c : fetchDecode img 0x8001d44c = some (E5R.Instr.store (E5R.Width.w) 2 23 0x0000001c#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xce5e) (by decide +kernel) (by decide +kernel)

theorem f8001d44e : fetchDecode img 0x8001d44e = some (E5R.Instr.store (E5R.Width.w) 2 24 0x00000018#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xcc62) (by decide +kernel) (by decide +kernel)

theorem f8001d450 : fetchDecode img 0x8001d450 = some (E5R.Instr.store (E5R.Width.w) 2 25 0x00000014#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xca66) (by decide +kernel) (by decide +kernel)

theorem f8001d452 : fetchDecode img 0x8001d452 = some (E5R.Instr.store (E5R.Width.w) 2 26 0x00000010#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc86a) (by decide +kernel) (by decide +kernel)

theorem f8001d454 : fetchDecode img 0x8001d454 = some (E5R.Instr.store (E5R.Width.w) 2 27 0x0000000c#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc66e) (by decide +kernel) (by decide +kernel)

theorem f8001d456 : fetchDecode img 0x8001d456 = some (E5R.Instr.op (E5R.AluOp.add) 18 0 12, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8932) (by decide +kernel) (by decide +kernel)

theorem f8001d458 : fetchDecode img 0x8001d458 = some (E5R.Instr.load (E5R.Width.w) true 8 10 0x00000004#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4140) (by decide +kernel) (by decide +kernel)

theorem f8001d45a : fetchDecode img 0x8001d45a = some (E5R.Instr.load (E5R.Width.w) true 9 10 0x00000000#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4104) (by decide +kernel) (by decide +kernel)

theorem f8001d45c : fetchDecode img 0x8001d45c = some (E5R.Instr.branch (E5R.BrCond.ltu) 12 8 0x00000084#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8866263) (by decide +kernel) (by decide +kernel)

theorem f8001d460 : fetchDecode img 0x8001d460 = some (E5R.Instr.branch (E5R.BrCond.ltu) 8 9 0x00000080#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8946063) (by decide +kernel) (by decide +kernel)

theorem f8001d464 : fetchDecode img 0x8001d464 = some (E5R.Instr.op (E5R.AluOp.add) 19 0 10, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x89aa) (by decide +kernel) (by decide +kernel)

theorem f8001d466 : fetchDecode img 0x8001d466 = some (E5R.Instr.op (E5R.AluOp.add) 20 0 11, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8a2e) (by decide +kernel) (by decide +kernel)

theorem f8001d468 : fetchDecode img 0x8001d468 = some (E5R.Instr.load (E5R.Width.b) false 23 10 0x00000008#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x854b83) (by decide +kernel) (by decide +kernel)

theorem f8001d46c : fetchDecode img 0x8001d46c = some (E5R.Instr.op (E5R.AluOp.sub) 24 0 8, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x40800c33) (by decide +kernel) (by decide +kernel)

theorem f8001d470 : fetchDecode img 0x8001d470 = some (E5R.Instr.opimm (E5R.AluOp.add) 25 0 0xffffffff#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x5cfd) (by decide +kernel) (by decide +kernel)

theorem f8001d472 : fetchDecode img 0x8001d472 = some (E5R.Instr.opimm (E5R.AluOp.add) 26 0 0x00000002#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4d09) (by decide +kernel) (by decide +kernel)

theorem f8001d474 : fetchDecode img 0x8001d474 = some (E5R.Instr.op (E5R.AluOp.add) 10 0 23, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x855e) (by decide +kernel) (by decide +kernel)

theorem f8001d476 : fetchDecode img 0x8001d476 = some (E5R.Instr.branch (E5R.BrCond.eq) 9 8 0x00000080#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8848063) (by decide +kernel) (by decide +kernel)

theorem f8001d47a : fetchDecode img 0x8001d47a = some (E5R.Instr.opimm (E5R.AluOp.add) 12 0 0x00000000#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4601) (by decide +kernel) (by decide +kernel)

theorem f8001d47c : fetchDecode img 0x8001d47c = some (E5R.Instr.op (E5R.AluOp.add) 11 20 9, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x9a05b3) (by decide +kernel) (by decide +kernel)

theorem f8001d480 : fetchDecode img 0x8001d480 = some (E5R.Instr.op (E5R.AluOp.add) 13 24 9, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x9c06b3) (by decide +kernel) (by decide +kernel)

theorem f8001d484 : fetchDecode img 0x8001d484 = some (E5R.Instr.op (E5R.AluOp.add) 14 0 20, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8752) (by decide +kernel) (by decide +kernel)

theorem f8001d486 : fetchDecode img 0x8001d486 = some (E5R.Instr.op (E5R.AluOp.add) 15 14 9, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x9707b3) (by decide +kernel) (by decide +kernel)

theorem f8001d48a : fetchDecode img 0x8001d48a = some (E5R.Instr.load (E5R.Width.b) false 15 15 0x00000000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x7c783) (by decide +kernel) (by decide +kernel)

theorem f8001d48e : fetchDecode img 0x8001d48e = some (E5R.Instr.branch (E5R.BrCond.eq) 15 0 0x0000000c#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc791) (by decide +kernel) (by decide +kernel)

theorem f8001d490 : fetchDecode img 0x8001d490 = some (E5R.Instr.opimm (E5R.AluOp.add) 12 12 0xffffffff#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x167d) (by decide +kernel) (by decide +kernel)

theorem f8001d492 : fetchDecode img 0x8001d492 = some (E5R.Instr.opimm (E5R.AluOp.add) 14 14 0x00000001#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x705) (by decide +kernel) (by decide +kernel)

theorem f8001d494 : fetchDecode img 0x8001d494 = some (E5R.Instr.branch (E5R.BrCond.ne) 13 12 0xfffffff2#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfec699e3) (by decide +kernel) (by decide +kernel)

theorem f8001d498 : fetchDecode img 0x8001d498 = some (E5R.Instr.jal 0 0x00000060#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xa085) (by decide +kernel) (by decide +kernel)

theorem f8001d49a : fetchDecode img 0x8001d49a = some (E5R.Instr.op (E5R.AluOp.sub) 21 9 12, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x40c48ab3) (by decide +kernel) (by decide +kernel)

theorem f8001d49e : fetchDecode img 0x8001d49e = some (E5R.Instr.opimm (E5R.AluOp.add) 27 21 0x00000001#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1a8d93) (by decide +kernel) (by decide +kernel)

theorem f8001d4a2 : fetchDecode img 0x8001d4a2 = some (E5R.Instr.opimm (E5R.AluOp.and) 10 10 0x00000001#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8905) (by decide +kernel) (by decide +kernel)

theorem f8001d4a4 : fetchDecode img 0x8001d4a4 = some (E5R.Instr.store (E5R.Width.w) 19 27 0x00000000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1b9a023) (by decide +kernel) (by decide +kernel)

theorem f8001d4a8 : fetchDecode img 0x8001d4a8 = some (E5R.Instr.branch (E5R.BrCond.eq) 10 0 0x0000000a#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc509) (by decide +kernel) (by decide +kernel)

theorem f8001d4aa : fetchDecode img 0x8001d4aa = some (E5R.Instr.opimm (E5R.AluOp.add) 23 0 0x00000000#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4b81) (by decide +kernel) (by decide +kernel)

theorem f8001d4ac : fetchDecode img 0x8001d4ac = some (E5R.Instr.store (E5R.Width.b) 19 0 0x00000008#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x98423) (by decide +kernel) (by decide +kernel)

theorem f8001d4b0 : fetchDecode img 0x8001d4b0 = some (E5R.Instr.jal 0 0x00000024#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xa015) (by decide +kernel) (by decide +kernel)

theorem f8001d4b2 : fetchDecode img 0x8001d4b2 = some (E5R.Instr.branch (E5R.BrCond.ltu) 21 9 0x000000ae#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xa9ae763) (by decide +kernel) (by decide +kernel)

theorem f8001d4b6 : fetchDecode img 0x8001d4b6 = some (E5R.Instr.branch (E5R.BrCond.ltu) 18 21 0x000000aa#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xb596563) (by decide +kernel) (by decide +kernel)

theorem f8001d4ba : fetchDecode img 0x8001d4ba = some (E5R.Instr.op (E5R.AluOp.sub) 12 0 12, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x40c00633) (by decide +kernel) (by decide +kernel)

theorem f8001d4be : fetchDecode img 0x8001d4be = some (E5R.Instr.opimm (E5R.AluOp.add) 10 2 0x00000004#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x48) (by decide +kernel) (by decide +kernel)

theorem f8001d4c0 : fetchDecode img 0x8001d4c0 = some (E5R.Instr.auipc 1 0x00001000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1097) (by decide +kernel) (by decide +kernel)

theorem f8001d4c4 : fetchDecode img 0x8001d4c4 = some (E5R.Instr.jalr 1 1 0xfffffb46#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xb46080e7) (by decide +kernel) (by decide +kernel)

theorem f8001d4c8 : fetchDecode img 0x8001d4c8 = some (E5R.Instr.load (E5R.Width.w) true 10 2 0x00000004#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4512) (by decide +kernel) (by decide +kernel)

theorem f8001d4ca : fetchDecode img 0x8001d4ca = some (E5R.Instr.branch (E5R.BrCond.ne) 10 25 0x0000000a#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1951563) (by decide +kernel) (by decide +kernel)

theorem f8001d4ce : fetchDecode img 0x8001d4ce = some (E5R.Instr.load (E5R.Width.w) true 22 2 0x00000008#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4b22) (by decide +kernel) (by decide +kernel)

theorem f8001d4d0 : fetchDecode img 0x8001d4d0 = some (E5R.Instr.branch (E5R.BrCond.ltu) 26 22 0x00000060#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x76d6063) (by decide +kernel) (by decide +kernel)

theorem f8001d4d4 : fetchDecode img 0x8001d4d4 = some (E5R.Instr.opimm (E5R.AluOp.add) 10 0 0x00000000#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4501) (by decide +kernel) (by decide +kernel)

theorem f8001d4d6 : fetchDecode img 0x8001d4d6 = some (E5R.Instr.op (E5R.AluOp.add) 9 0 27, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x84ee) (by decide +kernel) (by decide +kernel)

theorem f8001d4d8 : fetchDecode img 0x8001d4d8 = some (E5R.Instr.branch (E5R.BrCond.geu) 8 27 0xffffff9e#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xf9b47fe3) (by decide +kernel) (by decide +kernel)

theorem f8001d4dc : fetchDecode img 0x8001d4dc = some (E5R.Instr.opimm (E5R.AluOp.add) 9 21 0x00000001#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1a8493) (by decide +kernel) (by decide +kernel)

theorem f8001d4e0 : fetchDecode img 0x8001d4e0 = some (E5R.Instr.lui 13 0x80028000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x800286b7) (by decide +kernel) (by decide +kernel)

theorem f8001d4e4 : fetchDecode img 0x8001d4e4 = some (E5R.Instr.opimm (E5R.AluOp.add) 13 13 0xfffffe34#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xe3468693) (by decide +kernel) (by decide +kernel)

theorem f8001d4e8 : fetchDecode img 0x8001d4e8 = some (E5R.Instr.op (E5R.AluOp.add) 10 0 9, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8526) (by decide +kernel) (by decide +kernel)

theorem f8001d4ea : fetchDecode img 0x8001d4ea = some (E5R.Instr.op (E5R.AluOp.add) 11 0 8, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x85a2) (by decide +kernel) (by decide +kernel)

theorem f8001d4ec : fetchDecode img 0x8001d4ec = some (E5R.Instr.op (E5R.AluOp.add) 12 0 18, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x864a) (by decide +kernel) (by decide +kernel)

theorem f8001d4ee : fetchDecode img 0x8001d4ee = some (E5R.Instr.auipc 1 0x00002000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2097) (by decide +kernel) (by decide +kernel)

theorem f8001d4f2 : fetchDecode img 0x8001d4f2 = some (E5R.Instr.jalr 1 1 0x0000060e#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x60e080e7) (by decide +kernel) (by decide +kernel)

theorem f8001d4f6 : fetchDecode img 0x8001d4f6 = some (E5R.Instr.op (E5R.AluOp.add) 9 0 8, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x84a2) (by decide +kernel) (by decide +kernel)

theorem f8001d4f8 : fetchDecode img 0x8001d4f8 = some (E5R.Instr.opimm (E5R.AluOp.and) 10 23 0x00000001#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1bf513) (by decide +kernel) (by decide +kernel)

theorem f8001d4fc : fetchDecode img 0x8001d4fc = some (E5R.Instr.branch (E5R.BrCond.ne) 10 0 0x00000008#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xe501) (by decide +kernel) (by decide +kernel)

theorem f8001d4fe : fetchDecode img 0x8001d4fe = some (E5R.Instr.branch (E5R.BrCond.ne) 8 18 0x00000012#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1241963) (by decide +kernel) (by decide +kernel)

theorem f8001d502 : fetchDecode img 0x8001d502 = some (E5R.Instr.branch (E5R.BrCond.ne) 9 0 0x0000000e#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xe499) (by decide +kernel) (by decide +kernel)

theorem f8001d504 : fetchDecode img 0x8001d504 = some (E5R.Instr.opimm (E5R.AluOp.add) 10 0 0x00000000#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4501) (by decide +kernel) (by decide +kernel)

theorem f8001d506 : fetchDecode img 0x8001d506 = some (E5R.Instr.opimm (E5R.AluOp.add) 11 0 0x00000001#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4585) (by decide +kernel) (by decide +kernel)

theorem f8001d508 : fetchDecode img 0x8001d508 = some (E5R.Instr.store (E5R.Width.w) 19 8 0x00000000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x89a023) (by decide +kernel) (by decide +kernel)

theorem f8001d50c : fetchDecode img 0x8001d50c = some (E5R.Instr.store (E5R.Width.b) 19 11 0x00000008#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xb98423) (by decide +kernel) (by decide +kernel)

theorem f8001d510 : fetchDecode img 0x8001d510 = some (E5R.Instr.op (E5R.AluOp.add) 11 0 22, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x85da) (by decide +kernel) (by decide +kernel)

theorem f8001d512 : fetchDecode img 0x8001d512 = some (E5R.Instr.load (E5R.Width.w) true 1 2 0x0000003c#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x50f2) (by decide +kernel) (by decide +kernel)

theorem f8001d514 : fetchDecode img 0x8001d514 = some (E5R.Instr.load (E5R.Width.w) true 8 2 0x00000038#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x5462) (by decide +kernel) (by decide +kernel)

theorem f8001d516 : fetchDecode img 0x8001d516 = some (E5R.Instr.load (E5R.Width.w) true 9 2 0x00000034#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x54d2) (by decide +kernel) (by decide +kernel)

theorem f8001d518 : fetchDecode img 0x8001d518 = some (E5R.Instr.load (E5R.Width.w) true 18 2 0x00000030#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x5942) (by decide +kernel) (by decide +kernel)

theorem f8001d51a : fetchDecode img 0x8001d51a = some (E5R.Instr.load (E5R.Width.w) true 19 2 0x0000002c#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x59b2) (by decide +kernel) (by decide +kernel)

theorem f8001d51c : fetchDecode img 0x8001d51c = some (E5R.Instr.load (E5R.Width.w) true 20 2 0x00000028#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x5a22) (by decide +kernel) (by decide +kernel)

theorem f8001d51e : fetchDecode img 0x8001d51e = some (E5R.Instr.load (E5R.Width.w) true 21 2 0x00000024#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x5a92) (by decide +kernel) (by decide +kernel)

theorem f8001d520 : fetchDecode img 0x8001d520 = some (E5R.Instr.load (E5R.Width.w) true 22 2 0x00000020#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x5b02) (by decide +kernel) (by decide +kernel)

theorem f8001d522 : fetchDecode img 0x8001d522 = some (E5R.Instr.load (E5R.Width.w) true 23 2 0x0000001c#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4bf2) (by decide +kernel) (by decide +kernel)

theorem f8001d524 : fetchDecode img 0x8001d524 = some (E5R.Instr.load (E5R.Width.w) true 24 2 0x00000018#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4c62) (by decide +kernel) (by decide +kernel)

theorem f8001d526 : fetchDecode img 0x8001d526 = some (E5R.Instr.load (E5R.Width.w) true 25 2 0x00000014#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4cd2) (by decide +kernel) (by decide +kernel)

theorem f8001d528 : fetchDecode img 0x8001d528 = some (E5R.Instr.load (E5R.Width.w) true 26 2 0x00000010#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4d42) (by decide +kernel) (by decide +kernel)

theorem f8001d52a : fetchDecode img 0x8001d52a = some (E5R.Instr.load (E5R.Width.w) true 27 2 0x0000000c#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4db2) (by decide +kernel) (by decide +kernel)

theorem f8001d52c : fetchDecode img 0x8001d52c = some (E5R.Instr.opimm (E5R.AluOp.add) 2 2 0x00000040#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x6121) (by decide +kernel) (by decide +kernel)

theorem f8001d52e : fetchDecode img 0x8001d52e = some (E5R.Instr.jalr 0 1 0x00000000#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8082) (by decide +kernel) (by decide +kernel)

theorem f8001d530 : fetchDecode img 0x8001d530 = some (E5R.Instr.branch (E5R.BrCond.eq) 9 0 0x0000002c#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc495) (by decide +kernel) (by decide +kernel)

theorem f8001d532 : fetchDecode img 0x8001d532 = some (E5R.Instr.op (E5R.AluOp.add) 11 22 9, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x9b05b3) (by decide +kernel) (by decide +kernel)

theorem f8001d536 : fetchDecode img 0x8001d536 = some (E5R.Instr.lui 13 0x80028000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x800286b7) (by decide +kernel) (by decide +kernel)

theorem f8001d53a : fetchDecode img 0x8001d53a = some (E5R.Instr.opimm (E5R.AluOp.add) 13 13 0xfffffe14#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xe1468693) (by decide +kernel) (by decide +kernel)

theorem f8001d53e : fetchDecode img 0x8001d53e = some (E5R.Instr.op (E5R.AluOp.add) 10 0 9, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8526) (by decide +kernel) (by decide +kernel)

theorem f8001d540 : fetchDecode img 0x8001d540 = some (E5R.Instr.op (E5R.AluOp.add) 12 0 18, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x864a) (by decide +kernel) (by decide +kernel)

theorem f8001d542 : fetchDecode img 0x8001d542 = some (E5R.Instr.auipc 1 0xffffe000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xffffe097) (by decide +kernel) (by decide +kernel)

theorem f8001d546 : fetchDecode img 0x8001d546 = some (E5R.Instr.jalr 1 1 0xfffff834#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x834080e7) (by decide +kernel) (by decide +kernel)

theorem f8001d54a : fetchDecode img 0x8001d54a = some (E5R.Instr.op (E5R.AluOp.sub) 12 11 10, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x40a58633) (by decide +kernel) (by decide +kernel)

theorem f8001d54e : fetchDecode img 0x8001d54e = some (E5R.Instr.op (E5R.AluOp.add) 11 20 10, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xaa05b3) (by decide +kernel) (by decide +kernel)

theorem f8001d552 : fetchDecode img 0x8001d552 = some (E5R.Instr.op (E5R.AluOp.add) 10 0 20, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8552) (by decide +kernel) (by decide +kernel)

theorem f8001d554 : fetchDecode img 0x8001d554 = some (E5R.Instr.auipc 1 0x00003000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x3097) (by decide +kernel) (by decide +kernel)

theorem f8001d558 : fetchDecode img 0x8001d558 = some (E5R.Instr.jalr 1 1 0x000006ca#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x6ca080e7) (by decide +kernel) (by decide +kernel)

theorem f8001d55c : fetchDecode img 0x8001d55c = some (E5R.Instr.opimm (E5R.AluOp.add) 10 0 0x00000001#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4505) (by decide +kernel) (by decide +kernel)

theorem f8001d55e : fetchDecode img 0x8001d55e = some (E5R.Instr.jal 0 0xffffffb2#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xbf4d) (by decide +kernel) (by decide +kernel)

theorem f8001d560 : fetchDecode img 0x8001d560 = some (E5R.Instr.lui 13 0x80028000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x800286b7) (by decide +kernel) (by decide +kernel)

theorem f8001d564 : fetchDecode img 0x8001d564 = some (E5R.Instr.opimm (E5R.AluOp.add) 13 13 0xfffffe24#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xe2468693) (by decide +kernel) (by decide +kernel)

theorem f8001d568 : fetchDecode img 0x8001d568 = some (E5R.Instr.op (E5R.AluOp.add) 10 0 9, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8526) (by decide +kernel) (by decide +kernel)

theorem f8001d56a : fetchDecode img 0x8001d56a = some (E5R.Instr.op (E5R.AluOp.add) 11 0 21, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x85d6) (by decide +kernel) (by decide +kernel)

theorem f8001d56c : fetchDecode img 0x8001d56c = some (E5R.Instr.op (E5R.AluOp.add) 12 0 18, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x864a) (by decide +kernel) (by decide +kernel)

theorem f8001d56e : fetchDecode img 0x8001d56e = some (E5R.Instr.auipc 1 0x00002000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2097) (by decide +kernel) (by decide +kernel)

theorem f8001d572 : fetchDecode img 0x8001d572 = some (E5R.Instr.jalr 1 1 0x0000058e#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x58e080e7) (by decide +kernel) (by decide +kernel)

theorem f8001e006 : fetchDecode img 0x8001e006 = some (E5R.Instr.opimm (E5R.AluOp.add) 2 2 0xffffffe0#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1101) (by decide +kernel) (by decide +kernel)

theorem f8001e008 : fetchDecode img 0x8001e008 = some (E5R.Instr.store (E5R.Width.w) 2 1 0x0000001c#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xce06) (by decide +kernel) (by decide +kernel)

theorem f8001e00a : fetchDecode img 0x8001e00a = some (E5R.Instr.store (E5R.Width.w) 2 8 0x00000018#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xcc22) (by decide +kernel) (by decide +kernel)

theorem f8001e00c : fetchDecode img 0x8001e00c = some (E5R.Instr.op (E5R.AluOp.add) 8 0 10, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x842a) (by decide +kernel) (by decide +kernel)

theorem f8001e00e : fetchDecode img 0x8001e00e = some (E5R.Instr.opimm (E5R.AluOp.add) 10 2 0x0000000c#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x68) (by decide +kernel) (by decide +kernel)

theorem f8001e010 : fetchDecode img 0x8001e010 = some (E5R.Instr.auipc 1 0x00000000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x97) (by decide +kernel) (by decide +kernel)

theorem f8001e014 : fetchDecode img 0x8001e014 = some (E5R.Instr.jalr 1 1 0x0000001e#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1e080e7) (by decide +kernel) (by decide +kernel)

theorem f8001e018 : fetchDecode img 0x8001e018 = some (E5R.Instr.load (E5R.Width.w) true 10 2 0x0000000c#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4532) (by decide +kernel) (by decide +kernel)

theorem f8001e01a : fetchDecode img 0x8001e01a = some (E5R.Instr.load (E5R.Width.w) true 11 2 0x00000010#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x45c2) (by decide +kernel) (by decide +kernel)

theorem f8001e01c : fetchDecode img 0x8001e01c = some (E5R.Instr.load (E5R.Width.w) true 12 2 0x00000014#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4652) (by decide +kernel) (by decide +kernel)

theorem f8001e01e : fetchDecode img 0x8001e01e = some (E5R.Instr.opimm (E5R.AluOp.add) 10 10 0xffffffff#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x157d) (by decide +kernel) (by decide +kernel)

theorem f8001e020 : fetchDecode img 0x8001e020 = some (E5R.Instr.op (E5R.AluOp.or) 10 10 11, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8d4d) (by decide +kernel) (by decide +kernel)

theorem f8001e022 : fetchDecode img 0x8001e022 = some (E5R.Instr.store (E5R.Width.w) 8 10 0x00000000#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc008) (by decide +kernel) (by decide +kernel)

theorem f8001e024 : fetchDecode img 0x8001e024 = some (E5R.Instr.store (E5R.Width.w) 8 12 0x00000004#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc050) (by decide +kernel) (by decide +kernel)

theorem f8001e026 : fetchDecode img 0x8001e026 = some (E5R.Instr.load (E5R.Width.w) true 1 2 0x0000001c#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x40f2) (by decide +kernel) (by decide +kernel)

theorem f8001e028 : fetchDecode img 0x8001e028 = some (E5R.Instr.load (E5R.Width.w) true 8 2 0x00000018#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4462) (by decide +kernel) (by decide +kernel)

theorem f8001e02a : fetchDecode img 0x8001e02a = some (E5R.Instr.opimm (E5R.AluOp.add) 2 2 0x00000020#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x6105) (by decide +kernel) (by decide +kernel)

theorem f8001e02c : fetchDecode img 0x8001e02c = some (E5R.Instr.jalr 0 1 0x00000000#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8082) (by decide +kernel) (by decide +kernel)

theorem f8001ad76 : fetchDecode img 0x8001ad76 = some (E5R.Instr.branch (E5R.BrCond.ltu) 12 11 0x0000000a#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xb66563) (by decide +kernel) (by decide +kernel)

theorem f8001ad7a : fetchDecode img 0x8001ad7a = some (E5R.Instr.branch (E5R.BrCond.ltu) 11 10 0x00000018#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xa5ec63) (by decide +kernel) (by decide +kernel)

theorem f8001ad7e : fetchDecode img 0x8001ad7e = some (E5R.Instr.jalr 0 1 0x00000000#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8082) (by decide +kernel) (by decide +kernel)

end E5R.Rmk.NextFetch
