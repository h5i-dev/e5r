/-
  Instruction facts for `Deframer::park_pending` (0x8001d388..0x8001d3f2) and
  `Deframer::unpark_pending` (0x8001d3f2..0x8001d43a) in the pinned RMK image, generated from the
  model's own decoder (/dev/shm generator, the same `fetchDecode_of` form as
  Projects/rmk/Deframer/TailFetch.lean) and checked by the kernel against the packed ELF.

  Original nocompiler code, Apache-2.0. Regenerate rather than edit by hand.
-/
import Projects.rmk.Fetch

set_option maxRecDepth 100000

namespace NoCompiler.Rmk.ParkFetch
open NoCompiler NoCompiler.Rmk

theorem f8001d388 : fetchDecode img 0x8001d388 = some (NoCompiler.Instr.opimm (NoCompiler.AluOp.add) 2 2 0xfffffff0#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1141) (by decide +kernel) (by decide +kernel)

theorem f8001d38a : fetchDecode img 0x8001d38a = some (NoCompiler.Instr.store (NoCompiler.Width.w) 2 1 0x0000000c#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc606) (by decide +kernel) (by decide +kernel)

theorem f8001d38c : fetchDecode img 0x8001d38c = some (NoCompiler.Instr.store (NoCompiler.Width.w) 2 8 0x00000008#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc422) (by decide +kernel) (by decide +kernel)

theorem f8001d38e : fetchDecode img 0x8001d38e = some (NoCompiler.Instr.store (NoCompiler.Width.w) 2 9 0x00000004#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc226) (by decide +kernel) (by decide +kernel)

theorem f8001d390 : fetchDecode img 0x8001d390 = some (NoCompiler.Instr.load (NoCompiler.Width.w) true 14 10 0x00000004#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4158) (by decide +kernel) (by decide +kernel)

theorem f8001d392 : fetchDecode img 0x8001d392 = some (NoCompiler.Instr.branch (NoCompiler.BrCond.ltu) 12 14 0x0000003a#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2e66d63) (by decide +kernel) (by decide +kernel)

theorem f8001d396 : fetchDecode img 0x8001d396 = some (NoCompiler.Instr.op (NoCompiler.AluOp.add) 8 0 10, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x842a) (by decide +kernel) (by decide +kernel)

theorem f8001d398 : fetchDecode img 0x8001d398 = some (NoCompiler.Instr.load (NoCompiler.Width.w) true 10 10 0x00000000#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4108) (by decide +kernel) (by decide +kernel)

theorem f8001d39a : fetchDecode img 0x8001d39a = some (NoCompiler.Instr.branch (NoCompiler.BrCond.ltu) 14 10 0x00000046#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4a76363) (by decide +kernel) (by decide +kernel)

theorem f8001d39e : fetchDecode img 0x8001d39e = some (NoCompiler.Instr.op (NoCompiler.AluOp.sub) 9 14 10, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x40a704b3) (by decide +kernel) (by decide +kernel)

theorem f8001d3a2 : fetchDecode img 0x8001d3a2 = some (NoCompiler.Instr.op (NoCompiler.AluOp.add) 13 11 10, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xa586b3) (by decide +kernel) (by decide +kernel)

theorem f8001d3a6 : fetchDecode img 0x8001d3a6 = some (NoCompiler.Instr.op (NoCompiler.AluOp.add) 10 11 12, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc58533) (by decide +kernel) (by decide +kernel)

theorem f8001d3aa : fetchDecode img 0x8001d3aa = some (NoCompiler.Instr.op (NoCompiler.AluOp.sub) 10 10 9, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8d05) (by decide +kernel) (by decide +kernel)

theorem f8001d3ac : fetchDecode img 0x8001d3ac = some (NoCompiler.Instr.op (NoCompiler.AluOp.add) 11 0 13, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x85b6) (by decide +kernel) (by decide +kernel)

theorem f8001d3ae : fetchDecode img 0x8001d3ae = some (NoCompiler.Instr.op (NoCompiler.AluOp.add) 12 0 9, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8626) (by decide +kernel) (by decide +kernel)

theorem f8001d3b0 : fetchDecode img 0x8001d3b0 = some (NoCompiler.Instr.auipc 1 0x00004000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4097) (by decide +kernel) (by decide +kernel)

theorem f8001d3b4 : fetchDecode img 0x8001d3b4 = some (NoCompiler.Instr.jalr 1 1 0xfffff86e#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x86e080e7) (by decide +kernel) (by decide +kernel)

theorem f8001d3b8 : fetchDecode img 0x8001d3b8 = some (NoCompiler.Instr.store (NoCompiler.Width.w) 8 0 0x00000000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x42023) (by decide +kernel) (by decide +kernel)

theorem f8001d3bc : fetchDecode img 0x8001d3bc = some (NoCompiler.Instr.store (NoCompiler.Width.w) 8 0 0x00000004#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x42223) (by decide +kernel) (by decide +kernel)

theorem f8001d3c0 : fetchDecode img 0x8001d3c0 = some (NoCompiler.Instr.op (NoCompiler.AluOp.add) 10 0 9, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8526) (by decide +kernel) (by decide +kernel)

theorem f8001d3c2 : fetchDecode img 0x8001d3c2 = some (NoCompiler.Instr.load (NoCompiler.Width.w) true 1 2 0x0000000c#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x40b2) (by decide +kernel) (by decide +kernel)

theorem f8001d3c4 : fetchDecode img 0x8001d3c4 = some (NoCompiler.Instr.load (NoCompiler.Width.w) true 8 2 0x00000008#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4422) (by decide +kernel) (by decide +kernel)

theorem f8001d3c6 : fetchDecode img 0x8001d3c6 = some (NoCompiler.Instr.load (NoCompiler.Width.w) true 9 2 0x00000004#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4492) (by decide +kernel) (by decide +kernel)

theorem f8001d3c8 : fetchDecode img 0x8001d3c8 = some (NoCompiler.Instr.opimm (NoCompiler.AluOp.add) 2 2 0x00000010#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x141) (by decide +kernel) (by decide +kernel)

theorem f8001d3ca : fetchDecode img 0x8001d3ca = some (NoCompiler.Instr.jalr 0 1 0x00000000#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8082) (by decide +kernel) (by decide +kernel)

theorem f8001d3cc : fetchDecode img 0x8001d3cc = some (NoCompiler.Instr.lui 13 0x80028000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x800286b7) (by decide +kernel) (by decide +kernel)

theorem f8001d3d0 : fetchDecode img 0x8001d3d0 = some (NoCompiler.Instr.opimm (NoCompiler.AluOp.add) 13 13 0xfffffc20#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc2068693) (by decide +kernel) (by decide +kernel)

theorem f8001d3d4 : fetchDecode img 0x8001d3d4 = some (NoCompiler.Instr.opimm (NoCompiler.AluOp.add) 10 0 0x00000000#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4501) (by decide +kernel) (by decide +kernel)

theorem f8001d3d6 : fetchDecode img 0x8001d3d6 = some (NoCompiler.Instr.op (NoCompiler.AluOp.add) 11 0 14, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x85ba) (by decide +kernel) (by decide +kernel)

theorem f8001d3d8 : fetchDecode img 0x8001d3d8 = some (NoCompiler.Instr.auipc 1 0x00002000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2097) (by decide +kernel) (by decide +kernel)

theorem f8001d3dc : fetchDecode img 0x8001d3dc = some (NoCompiler.Instr.jalr 1 1 0x00000724#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x724080e7) (by decide +kernel) (by decide +kernel)

theorem f8001d3e0 : fetchDecode img 0x8001d3e0 = some (NoCompiler.Instr.lui 13 0x80028000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x800286b7) (by decide +kernel) (by decide +kernel)

theorem f8001d3e4 : fetchDecode img 0x8001d3e4 = some (NoCompiler.Instr.opimm (NoCompiler.AluOp.add) 13 13 0xfffffc30#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc3068693) (by decide +kernel) (by decide +kernel)

theorem f8001d3e8 : fetchDecode img 0x8001d3e8 = some (NoCompiler.Instr.op (NoCompiler.AluOp.add) 11 0 14, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x85ba) (by decide +kernel) (by decide +kernel)

theorem f8001d3ea : fetchDecode img 0x8001d3ea = some (NoCompiler.Instr.auipc 1 0x00002000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2097) (by decide +kernel) (by decide +kernel)

theorem f8001d3ee : fetchDecode img 0x8001d3ee = some (NoCompiler.Instr.jalr 1 1 0x00000712#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x712080e7) (by decide +kernel) (by decide +kernel)

theorem f8001d3f2 : fetchDecode img 0x8001d3f2 = some (NoCompiler.Instr.opimm (NoCompiler.AluOp.add) 2 2 0xfffffff0#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1141) (by decide +kernel) (by decide +kernel)

theorem f8001d3f4 : fetchDecode img 0x8001d3f4 = some (NoCompiler.Instr.store (NoCompiler.Width.w) 2 1 0x0000000c#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc606) (by decide +kernel) (by decide +kernel)

theorem f8001d3f6 : fetchDecode img 0x8001d3f6 = some (NoCompiler.Instr.store (NoCompiler.Width.w) 2 8 0x00000008#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc422) (by decide +kernel) (by decide +kernel)

theorem f8001d3f8 : fetchDecode img 0x8001d3f8 = some (NoCompiler.Instr.store (NoCompiler.Width.w) 2 9 0x00000004#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc226) (by decide +kernel) (by decide +kernel)

theorem f8001d3fa : fetchDecode img 0x8001d3fa = some (NoCompiler.Instr.op (NoCompiler.AluOp.add) 9 0 10, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x84aa) (by decide +kernel) (by decide +kernel)

theorem f8001d3fc : fetchDecode img 0x8001d3fc = some (NoCompiler.Instr.op (NoCompiler.AluOp.sub) 10 12 13, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x40d60533) (by decide +kernel) (by decide +kernel)

theorem f8001d400 : fetchDecode img 0x8001d400 = some (NoCompiler.Instr.branch (NoCompiler.BrCond.ltu) 12 13 0x00000028#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2d66463) (by decide +kernel) (by decide +kernel)

theorem f8001d404 : fetchDecode img 0x8001d404 = some (NoCompiler.Instr.op (NoCompiler.AluOp.add) 8 0 13, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8436) (by decide +kernel) (by decide +kernel)

theorem f8001d406 : fetchDecode img 0x8001d406 = some (NoCompiler.Instr.op (NoCompiler.AluOp.add) 12 11 10, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xa58633) (by decide +kernel) (by decide +kernel)

theorem f8001d40a : fetchDecode img 0x8001d40a = some (NoCompiler.Instr.op (NoCompiler.AluOp.add) 10 0 11, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x852e) (by decide +kernel) (by decide +kernel)

theorem f8001d40c : fetchDecode img 0x8001d40c = some (NoCompiler.Instr.op (NoCompiler.AluOp.add) 11 0 12, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x85b2) (by decide +kernel) (by decide +kernel)

theorem f8001d40e : fetchDecode img 0x8001d40e = some (NoCompiler.Instr.op (NoCompiler.AluOp.add) 12 0 13, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8636) (by decide +kernel) (by decide +kernel)

theorem f8001d410 : fetchDecode img 0x8001d410 = some (NoCompiler.Instr.auipc 1 0x00004000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4097) (by decide +kernel) (by decide +kernel)

theorem f8001d414 : fetchDecode img 0x8001d414 = some (NoCompiler.Instr.jalr 1 1 0xfffff80e#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x80e080e7) (by decide +kernel) (by decide +kernel)

theorem f8001d418 : fetchDecode img 0x8001d418 = some (NoCompiler.Instr.store (NoCompiler.Width.w) 9 0 0x00000000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4a023) (by decide +kernel) (by decide +kernel)

theorem f8001d41c : fetchDecode img 0x8001d41c = some (NoCompiler.Instr.store (NoCompiler.Width.w) 9 8 0x00000004#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc0c0) (by decide +kernel) (by decide +kernel)

theorem f8001d41e : fetchDecode img 0x8001d41e = some (NoCompiler.Instr.load (NoCompiler.Width.w) true 1 2 0x0000000c#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x40b2) (by decide +kernel) (by decide +kernel)

theorem f8001d420 : fetchDecode img 0x8001d420 = some (NoCompiler.Instr.load (NoCompiler.Width.w) true 8 2 0x00000008#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4422) (by decide +kernel) (by decide +kernel)

theorem f8001d422 : fetchDecode img 0x8001d422 = some (NoCompiler.Instr.load (NoCompiler.Width.w) true 9 2 0x00000004#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4492) (by decide +kernel) (by decide +kernel)

theorem f8001d424 : fetchDecode img 0x8001d424 = some (NoCompiler.Instr.opimm (NoCompiler.AluOp.add) 2 2 0x00000010#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x141) (by decide +kernel) (by decide +kernel)

theorem f8001d426 : fetchDecode img 0x8001d426 = some (NoCompiler.Instr.jalr 0 1 0x00000000#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8082) (by decide +kernel) (by decide +kernel)

theorem f8001d428 : fetchDecode img 0x8001d428 = some (NoCompiler.Instr.lui 13 0x80028000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x800286b7) (by decide +kernel) (by decide +kernel)

theorem f8001d42c : fetchDecode img 0x8001d42c = some (NoCompiler.Instr.opimm (NoCompiler.AluOp.add) 13 13 0xfffffc30#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc3068693) (by decide +kernel) (by decide +kernel)

theorem f8001d430 : fetchDecode img 0x8001d430 = some (NoCompiler.Instr.op (NoCompiler.AluOp.add) 11 0 12, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x85b2) (by decide +kernel) (by decide +kernel)

theorem f8001d432 : fetchDecode img 0x8001d432 = some (NoCompiler.Instr.auipc 1 0x00002000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2097) (by decide +kernel) (by decide +kernel)

theorem f8001d436 : fetchDecode img 0x8001d436 = some (NoCompiler.Instr.jalr 1 1 0x000006ca#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x6ca080e7) (by decide +kernel) (by decide +kernel)

end NoCompiler.Rmk.ParkFetch
