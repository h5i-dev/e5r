/-
  Instruction facts for the emitted memmove (compiler_builtins) in the
  pinned RMK image, generated from the model's own decoder and checked by
  the kernel against the packed ELF (Projects/rmk/Fetch.lean).

  Original e5r code, Apache-2.0. Regenerate rather than edit by hand.
-/
import Projects.rmk.Fetch

set_option maxRecDepth 100000

namespace E5R.Rmk.MemmoveFetch
open E5R E5R.Rmk

theorem f80020c1e : fetchDecode img 0x80020c1e = some (Instr.auipc 6 0x00000000#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x317) (by decide +kernel) (by decide +kernel)
theorem f80020c22 : fetchDecode img 0x80020c22 = some (Instr.jalr 0 6 0x00000180#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x18030067) (by decide +kernel) (by decide +kernel)
theorem f80020d9e : fetchDecode img 0x80020d9e = some (Instr.opimm (AluOp.add) 2 2 0xffffffd0#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x7179) (by decide +kernel) (by decide +kernel)
theorem f80020da0 : fetchDecode img 0x80020da0 = some (Instr.store (Width.w) 2 8 0x0000002c#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xd622) (by decide +kernel) (by decide +kernel)
theorem f80020da2 : fetchDecode img 0x80020da2 = some (Instr.store (Width.w) 2 9 0x00000028#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xd426) (by decide +kernel) (by decide +kernel)
theorem f80020da4 : fetchDecode img 0x80020da4 = some (Instr.store (Width.w) 2 18 0x00000024#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xd24a) (by decide +kernel) (by decide +kernel)
theorem f80020da6 : fetchDecode img 0x80020da6 = some (Instr.op (AluOp.sub) 13 10 11, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x40b506b3) (by decide +kernel) (by decide +kernel)
theorem f80020daa : fetchDecode img 0x80020daa = some (Instr.branch (BrCond.geu) 13 12 0x00000076#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x6c6fb63) (by decide +kernel) (by decide +kernel)
theorem f80020dae : fetchDecode img 0x80020dae = some (Instr.op (AluOp.add) 9 10 12, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc504b3) (by decide +kernel) (by decide +kernel)
theorem f80020db2 : fetchDecode img 0x80020db2 = some (Instr.opimm (AluOp.add) 13 0 0x00000010#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x46c1) (by decide +kernel) (by decide +kernel)
theorem f80020db4 : fetchDecode img 0x80020db4 = some (Instr.op (AluOp.add) 16 11 12, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc58833) (by decide +kernel) (by decide +kernel)
theorem f80020db8 : fetchDecode img 0x80020db8 = some (Instr.branch (BrCond.ltu) 12 13 0x000002da#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2cd66d63) (by decide +kernel) (by decide +kernel)
theorem f80021092 : fetchDecode img 0x80021092 = some (Instr.op (AluOp.sub) 11 9 12, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x40c485b3) (by decide +kernel) (by decide +kernel)
theorem f80021096 : fetchDecode img 0x80021096 = some (Instr.branch (BrCond.geu) 11 9 0x0000001a#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x95fd63) (by decide +kernel) (by decide +kernel)
theorem f8002109a : fetchDecode img 0x8002109a = some (Instr.opimm (AluOp.add) 16 16 0xffffffff#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x187d) (by decide +kernel) (by decide +kernel)
theorem f8002109c : fetchDecode img 0x8002109c = some (Instr.load (Width.b) false 12 16 0x00000000#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x84603) (by decide +kernel) (by decide +kernel)
theorem f800210a0 : fetchDecode img 0x800210a0 = some (Instr.opimm (AluOp.add) 13 9 0xffffffff#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfff48693) (by decide +kernel) (by decide +kernel)
theorem f800210a4 : fetchDecode img 0x800210a4 = some (Instr.store (Width.b) 9 12 0xffffffff#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfec48fa3) (by decide +kernel) (by decide +kernel)
theorem f800210a8 : fetchDecode img 0x800210a8 = some (Instr.opimm (AluOp.add) 16 16 0xffffffff#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x187d) (by decide +kernel) (by decide +kernel)
theorem f800210aa : fetchDecode img 0x800210aa = some (Instr.op (AluOp.add) 9 0 13, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x84b6) (by decide +kernel) (by decide +kernel)
theorem f800210ac : fetchDecode img 0x800210ac = some (Instr.branch (BrCond.ltu) 11 13 0xfffffff0#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfed5e8e3) (by decide +kernel) (by decide +kernel)
theorem f80020e20 : fetchDecode img 0x80020e20 = some (Instr.opimm (AluOp.add) 13 0 0x00000010#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x46c1) (by decide +kernel) (by decide +kernel)
theorem f80020e22 : fetchDecode img 0x80020e22 = some (Instr.branch (BrCond.ltu) 12 13 0x00000070#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x6d66863) (by decide +kernel) (by decide +kernel)
theorem f80020e92 : fetchDecode img 0x80020e92 = some (Instr.op (AluOp.add) 13 0 10, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x86aa) (by decide +kernel) (by decide +kernel)
theorem f80020e94 : fetchDecode img 0x80020e94 = some (Instr.op (AluOp.add) 14 10 12, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc50733) (by decide +kernel) (by decide +kernel)
theorem f80020e98 : fetchDecode img 0x80020e98 = some (Instr.branch (BrCond.ltu) 10 14 0x0000012e#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x12e56763) (by decide +kernel) (by decide +kernel)
theorem f80020e9c : fetchDecode img 0x80020e9c = some (Instr.jal 0 0x00000214#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xac11) (by decide +kernel) (by decide +kernel)
theorem f80020fc6 : fetchDecode img 0x80020fc6 = some (Instr.load (Width.b) false 14 11 0x00000000#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x5c703) (by decide +kernel) (by decide +kernel)
theorem f80020fca : fetchDecode img 0x80020fca = some (Instr.opimm (AluOp.add) 12 12 0xffffffff#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x167d) (by decide +kernel) (by decide +kernel)
theorem f80020fcc : fetchDecode img 0x80020fcc = some (Instr.store (Width.b) 13 14 0x00000000#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xe68023) (by decide +kernel) (by decide +kernel)
theorem f80020fd0 : fetchDecode img 0x80020fd0 = some (Instr.opimm (AluOp.add) 13 13 0x00000001#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x685) (by decide +kernel) (by decide +kernel)
theorem f80020fd2 : fetchDecode img 0x80020fd2 = some (Instr.opimm (AluOp.add) 11 11 0x00000001#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x585) (by decide +kernel) (by decide +kernel)
theorem f80020fd4 : fetchDecode img 0x80020fd4 = some (Instr.branch (BrCond.ne) 12 0 0xfffffff2#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfa6d) (by decide +kernel) (by decide +kernel)
theorem f80020fd6 : fetchDecode img 0x80020fd6 = some (Instr.jal 0 0x000000da#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xa8e9) (by decide +kernel) (by decide +kernel)
theorem f800210b0 : fetchDecode img 0x800210b0 = some (Instr.load (Width.w) true 8 2 0x0000002c#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x5432) (by decide +kernel) (by decide +kernel)
theorem f800210b2 : fetchDecode img 0x800210b2 = some (Instr.load (Width.w) true 9 2 0x00000028#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x54a2) (by decide +kernel) (by decide +kernel)
theorem f800210b4 : fetchDecode img 0x800210b4 = some (Instr.load (Width.w) true 18 2 0x00000024#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x5912) (by decide +kernel) (by decide +kernel)
theorem f800210b6 : fetchDecode img 0x800210b6 = some (Instr.opimm (AluOp.add) 2 2 0x00000030#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x6145) (by decide +kernel) (by decide +kernel)
theorem f800210b8 : fetchDecode img 0x800210b8 = some (Instr.jalr 0 1 0x00000000#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8082) (by decide +kernel) (by decide +kernel)

end E5R.Rmk.MemmoveFetch
