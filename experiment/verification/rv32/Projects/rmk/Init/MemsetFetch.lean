/-
  Instruction facts for compiler_builtins `memset` (0x80020bb2..0x80020c1e), called by the session
  task's initialization at 0x80003e02 to clear the deframer buffer, in the pinned RMK image,
  generated from the model's own decoder (the `fetchDecode_of` form of
  Projects/rmk/Deframer/TailFetch.lean) and checked by the kernel against the packed ELF.
  Also `exec_muldiv`, the step form of `mul` the generated segments use.

  Original nocompiler code, Apache-2.0. Regenerate rather than edit by hand.
-/
import Projects.rmk.Fetch

set_option maxRecDepth 100000

namespace NoCompiler.Rmk.MemsetFetch
open NoCompiler NoCompiler.Rmk

theorem exec_muldiv (c : Core) (len : Word) (op rd rs1 rs2) :
    exec c len (.muldiv op rd rs1 rs2) = .done (c.wr rd (muldiv op (c.get rs1) (c.get rs2)) (c.pc + len)) := rfl

theorem f80020bb2 : fetchDecode img 0x80020bb2 = some (NoCompiler.Instr.opimm (NoCompiler.AluOp.add) 13 0 0x00000010#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x46c1) (by decide +kernel) (by decide +kernel)

theorem f80020bb4 : fetchDecode img 0x80020bb4 = some (NoCompiler.Instr.branch (NoCompiler.BrCond.ltu) 12 13 0x00000054#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4d66a63) (by decide +kernel) (by decide +kernel)

theorem f80020bb8 : fetchDecode img 0x80020bb8 = some (NoCompiler.Instr.op (NoCompiler.AluOp.sub) 13 0 10, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x40a006b3) (by decide +kernel) (by decide +kernel)

theorem f80020bbc : fetchDecode img 0x80020bbc = some (NoCompiler.Instr.opimm (NoCompiler.AluOp.and) 16 13 0x00000003#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x36f813) (by decide +kernel) (by decide +kernel)

theorem f80020bc0 : fetchDecode img 0x80020bc0 = some (NoCompiler.Instr.op (NoCompiler.AluOp.add) 14 10 16, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1050733) (by decide +kernel) (by decide +kernel)

theorem f80020bc4 : fetchDecode img 0x80020bc4 = some (NoCompiler.Instr.branch (NoCompiler.BrCond.geu) 10 14 0x00000012#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xe57963) (by decide +kernel) (by decide +kernel)

theorem f80020bc8 : fetchDecode img 0x80020bc8 = some (NoCompiler.Instr.op (NoCompiler.AluOp.add) 15 0 16, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x87c2) (by decide +kernel) (by decide +kernel)

theorem f80020bca : fetchDecode img 0x80020bca = some (NoCompiler.Instr.op (NoCompiler.AluOp.add) 13 0 10, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x86aa) (by decide +kernel) (by decide +kernel)

theorem f80020bcc : fetchDecode img 0x80020bcc = some (NoCompiler.Instr.store (NoCompiler.Width.b) 13 11 0x00000000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xb68023) (by decide +kernel) (by decide +kernel)

theorem f80020bd0 : fetchDecode img 0x80020bd0 = some (NoCompiler.Instr.opimm (NoCompiler.AluOp.add) 15 15 0xffffffff#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x17fd) (by decide +kernel) (by decide +kernel)

theorem f80020bd2 : fetchDecode img 0x80020bd2 = some (NoCompiler.Instr.opimm (NoCompiler.AluOp.add) 13 13 0x00000001#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x685) (by decide +kernel) (by decide +kernel)

theorem f80020bd4 : fetchDecode img 0x80020bd4 = some (NoCompiler.Instr.branch (NoCompiler.BrCond.ne) 15 0 0xfffffff8#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xffe5) (by decide +kernel) (by decide +kernel)

theorem f80020bd6 : fetchDecode img 0x80020bd6 = some (NoCompiler.Instr.op (NoCompiler.AluOp.sub) 12 12 16, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x41060633) (by decide +kernel) (by decide +kernel)

theorem f80020bda : fetchDecode img 0x80020bda = some (NoCompiler.Instr.opimm (NoCompiler.AluOp.and) 13 12 0xfffffffc#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xffc67693) (by decide +kernel) (by decide +kernel)

theorem f80020bde : fetchDecode img 0x80020bde = some (NoCompiler.Instr.op (NoCompiler.AluOp.add) 13 13 14, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x96ba) (by decide +kernel) (by decide +kernel)

theorem f80020be0 : fetchDecode img 0x80020be0 = some (NoCompiler.Instr.branch (NoCompiler.BrCond.geu) 14 13 0x0000001c#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xd77e63) (by decide +kernel) (by decide +kernel)

theorem f80020be4 : fetchDecode img 0x80020be4 = some (NoCompiler.Instr.opimm (NoCompiler.AluOp.and) 16 11 0x000000ff#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xff5f813) (by decide +kernel) (by decide +kernel)

theorem f80020be8 : fetchDecode img 0x80020be8 = some (NoCompiler.Instr.lui 15 0x01010000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x10107b7) (by decide +kernel) (by decide +kernel)

theorem f80020bec : fetchDecode img 0x80020bec = some (NoCompiler.Instr.opimm (NoCompiler.AluOp.add) 15 15 0x00000101#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x10178793) (by decide +kernel) (by decide +kernel)

theorem f80020bf0 : fetchDecode img 0x80020bf0 = some (NoCompiler.Instr.muldiv (NoCompiler.MulOp.mul) 15 16 15, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2f807b3) (by decide +kernel) (by decide +kernel)

theorem f80020bf4 : fetchDecode img 0x80020bf4 = some (NoCompiler.Instr.store (NoCompiler.Width.w) 14 15 0x00000000#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc31c) (by decide +kernel) (by decide +kernel)

theorem f80020bf6 : fetchDecode img 0x80020bf6 = some (NoCompiler.Instr.opimm (NoCompiler.AluOp.add) 14 14 0x00000004#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x711) (by decide +kernel) (by decide +kernel)

theorem f80020bf8 : fetchDecode img 0x80020bf8 = some (NoCompiler.Instr.branch (NoCompiler.BrCond.ltu) 14 13 0xfffffffc#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfed76ee3) (by decide +kernel) (by decide +kernel)

theorem f80020bfc : fetchDecode img 0x80020bfc = some (NoCompiler.Instr.opimm (NoCompiler.AluOp.and) 12 12 0x00000003#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8a0d) (by decide +kernel) (by decide +kernel)

theorem f80020bfe : fetchDecode img 0x80020bfe = some (NoCompiler.Instr.op (NoCompiler.AluOp.add) 14 13 12, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc68733) (by decide +kernel) (by decide +kernel)

theorem f80020c02 : fetchDecode img 0x80020c02 = some (NoCompiler.Instr.branch (NoCompiler.BrCond.ltu) 13 14 0x00000010#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xe6e863) (by decide +kernel) (by decide +kernel)

theorem f80020c06 : fetchDecode img 0x80020c06 = some (NoCompiler.Instr.jal 0 0x00000016#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xa819) (by decide +kernel) (by decide +kernel)

theorem f80020c08 : fetchDecode img 0x80020c08 = some (NoCompiler.Instr.op (NoCompiler.AluOp.add) 13 0 10, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x86aa) (by decide +kernel) (by decide +kernel)

theorem f80020c0a : fetchDecode img 0x80020c0a = some (NoCompiler.Instr.op (NoCompiler.AluOp.add) 14 10 12, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc50733) (by decide +kernel) (by decide +kernel)

theorem f80020c0e : fetchDecode img 0x80020c0e = some (NoCompiler.Instr.branch (NoCompiler.BrCond.geu) 10 14 0x0000000e#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xe57763) (by decide +kernel) (by decide +kernel)

theorem f80020c12 : fetchDecode img 0x80020c12 = some (NoCompiler.Instr.store (NoCompiler.Width.b) 13 11 0x00000000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xb68023) (by decide +kernel) (by decide +kernel)

theorem f80020c16 : fetchDecode img 0x80020c16 = some (NoCompiler.Instr.opimm (NoCompiler.AluOp.add) 12 12 0xffffffff#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x167d) (by decide +kernel) (by decide +kernel)

theorem f80020c18 : fetchDecode img 0x80020c18 = some (NoCompiler.Instr.opimm (NoCompiler.AluOp.add) 13 13 0x00000001#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x685) (by decide +kernel) (by decide +kernel)

theorem f80020c1a : fetchDecode img 0x80020c1a = some (NoCompiler.Instr.branch (NoCompiler.BrCond.ne) 12 0 0xfffffff8#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfe65) (by decide +kernel) (by decide +kernel)

theorem f80020c1c : fetchDecode img 0x80020c1c = some (NoCompiler.Instr.jalr 0 1 0x00000000#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8082) (by decide +kernel) (by decide +kernel)

end NoCompiler.Rmk.MemsetFetch
