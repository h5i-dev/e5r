/-
  Instruction facts for compiler_builtins `memset` (0x80020bb2..0x80020c1e), called by the session
  task's initialization at 0x80003e02 to clear the deframer buffer, in the pinned RMK image,
  generated from the model's own decoder (the `fetchDecode_of` form of
  Projects/rmk/Deframer/TailFetch.lean) and checked by the kernel against the packed ELF.
  Also `exec_muldiv`, the step form of `mul` the generated segments use.

  Original e5r code, Apache-2.0. Regenerate rather than edit by hand.
-/
import Projects.rmk.Fetch

set_option maxRecDepth 100000

namespace E5R.Rmk.MemsetFetch
open E5R E5R.Rmk

theorem exec_muldiv (c : Core) (len : Word) (op rd rs1 rs2) :
    exec c len (.muldiv op rd rs1 rs2) = .done (c.wr rd (muldiv op (c.get rs1) (c.get rs2)) (c.pc + len)) := rfl

theorem f80020bb2 : fetchDecode img 0x80020bb2 = some (E5R.Instr.opimm (E5R.AluOp.add) 13 0 0x00000010#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x46c1) (by decide +kernel) (by decide +kernel)

theorem f80020bb4 : fetchDecode img 0x80020bb4 = some (E5R.Instr.branch (E5R.BrCond.ltu) 12 13 0x00000054#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4d66a63) (by decide +kernel) (by decide +kernel)

theorem f80020bb8 : fetchDecode img 0x80020bb8 = some (E5R.Instr.op (E5R.AluOp.sub) 13 0 10, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x40a006b3) (by decide +kernel) (by decide +kernel)

theorem f80020bbc : fetchDecode img 0x80020bbc = some (E5R.Instr.opimm (E5R.AluOp.and) 16 13 0x00000003#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x36f813) (by decide +kernel) (by decide +kernel)

theorem f80020bc0 : fetchDecode img 0x80020bc0 = some (E5R.Instr.op (E5R.AluOp.add) 14 10 16, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1050733) (by decide +kernel) (by decide +kernel)

theorem f80020bc4 : fetchDecode img 0x80020bc4 = some (E5R.Instr.branch (E5R.BrCond.geu) 10 14 0x00000012#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xe57963) (by decide +kernel) (by decide +kernel)

theorem f80020bc8 : fetchDecode img 0x80020bc8 = some (E5R.Instr.op (E5R.AluOp.add) 15 0 16, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x87c2) (by decide +kernel) (by decide +kernel)

theorem f80020bca : fetchDecode img 0x80020bca = some (E5R.Instr.op (E5R.AluOp.add) 13 0 10, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x86aa) (by decide +kernel) (by decide +kernel)

theorem f80020bcc : fetchDecode img 0x80020bcc = some (E5R.Instr.store (E5R.Width.b) 13 11 0x00000000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xb68023) (by decide +kernel) (by decide +kernel)

theorem f80020bd0 : fetchDecode img 0x80020bd0 = some (E5R.Instr.opimm (E5R.AluOp.add) 15 15 0xffffffff#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x17fd) (by decide +kernel) (by decide +kernel)

theorem f80020bd2 : fetchDecode img 0x80020bd2 = some (E5R.Instr.opimm (E5R.AluOp.add) 13 13 0x00000001#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x685) (by decide +kernel) (by decide +kernel)

theorem f80020bd4 : fetchDecode img 0x80020bd4 = some (E5R.Instr.branch (E5R.BrCond.ne) 15 0 0xfffffff8#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xffe5) (by decide +kernel) (by decide +kernel)

theorem f80020bd6 : fetchDecode img 0x80020bd6 = some (E5R.Instr.op (E5R.AluOp.sub) 12 12 16, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x41060633) (by decide +kernel) (by decide +kernel)

theorem f80020bda : fetchDecode img 0x80020bda = some (E5R.Instr.opimm (E5R.AluOp.and) 13 12 0xfffffffc#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xffc67693) (by decide +kernel) (by decide +kernel)

theorem f80020bde : fetchDecode img 0x80020bde = some (E5R.Instr.op (E5R.AluOp.add) 13 13 14, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x96ba) (by decide +kernel) (by decide +kernel)

theorem f80020be0 : fetchDecode img 0x80020be0 = some (E5R.Instr.branch (E5R.BrCond.geu) 14 13 0x0000001c#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xd77e63) (by decide +kernel) (by decide +kernel)

theorem f80020be4 : fetchDecode img 0x80020be4 = some (E5R.Instr.opimm (E5R.AluOp.and) 16 11 0x000000ff#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xff5f813) (by decide +kernel) (by decide +kernel)

theorem f80020be8 : fetchDecode img 0x80020be8 = some (E5R.Instr.lui 15 0x01010000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x10107b7) (by decide +kernel) (by decide +kernel)

theorem f80020bec : fetchDecode img 0x80020bec = some (E5R.Instr.opimm (E5R.AluOp.add) 15 15 0x00000101#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x10178793) (by decide +kernel) (by decide +kernel)

theorem f80020bf0 : fetchDecode img 0x80020bf0 = some (E5R.Instr.muldiv (E5R.MulOp.mul) 15 16 15, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2f807b3) (by decide +kernel) (by decide +kernel)

theorem f80020bf4 : fetchDecode img 0x80020bf4 = some (E5R.Instr.store (E5R.Width.w) 14 15 0x00000000#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc31c) (by decide +kernel) (by decide +kernel)

theorem f80020bf6 : fetchDecode img 0x80020bf6 = some (E5R.Instr.opimm (E5R.AluOp.add) 14 14 0x00000004#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x711) (by decide +kernel) (by decide +kernel)

theorem f80020bf8 : fetchDecode img 0x80020bf8 = some (E5R.Instr.branch (E5R.BrCond.ltu) 14 13 0xfffffffc#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfed76ee3) (by decide +kernel) (by decide +kernel)

theorem f80020bfc : fetchDecode img 0x80020bfc = some (E5R.Instr.opimm (E5R.AluOp.and) 12 12 0x00000003#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8a0d) (by decide +kernel) (by decide +kernel)

theorem f80020bfe : fetchDecode img 0x80020bfe = some (E5R.Instr.op (E5R.AluOp.add) 14 13 12, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc68733) (by decide +kernel) (by decide +kernel)

theorem f80020c02 : fetchDecode img 0x80020c02 = some (E5R.Instr.branch (E5R.BrCond.ltu) 13 14 0x00000010#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xe6e863) (by decide +kernel) (by decide +kernel)

theorem f80020c06 : fetchDecode img 0x80020c06 = some (E5R.Instr.jal 0 0x00000016#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xa819) (by decide +kernel) (by decide +kernel)

theorem f80020c08 : fetchDecode img 0x80020c08 = some (E5R.Instr.op (E5R.AluOp.add) 13 0 10, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x86aa) (by decide +kernel) (by decide +kernel)

theorem f80020c0a : fetchDecode img 0x80020c0a = some (E5R.Instr.op (E5R.AluOp.add) 14 10 12, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc50733) (by decide +kernel) (by decide +kernel)

theorem f80020c0e : fetchDecode img 0x80020c0e = some (E5R.Instr.branch (E5R.BrCond.geu) 10 14 0x0000000e#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xe57763) (by decide +kernel) (by decide +kernel)

theorem f80020c12 : fetchDecode img 0x80020c12 = some (E5R.Instr.store (E5R.Width.b) 13 11 0x00000000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xb68023) (by decide +kernel) (by decide +kernel)

theorem f80020c16 : fetchDecode img 0x80020c16 = some (E5R.Instr.opimm (E5R.AluOp.add) 12 12 0xffffffff#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x167d) (by decide +kernel) (by decide +kernel)

theorem f80020c18 : fetchDecode img 0x80020c18 = some (E5R.Instr.opimm (E5R.AluOp.add) 13 13 0x00000001#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x685) (by decide +kernel) (by decide +kernel)

theorem f80020c1a : fetchDecode img 0x80020c1a = some (E5R.Instr.branch (E5R.BrCond.ne) 12 0 0xfffffff8#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfe65) (by decide +kernel) (by decide +kernel)

theorem f80020c1c : fetchDecode img 0x80020c1c = some (E5R.Instr.jalr 0 1 0x00000000#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8082) (by decide +kernel) (by decide +kernel)

end E5R.Rmk.MemsetFetch
