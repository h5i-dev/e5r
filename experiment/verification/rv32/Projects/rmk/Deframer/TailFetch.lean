/-
  Instruction facts for `Deframer::tail` (0x8001d576..0x8001d608) in the pinned RMK image,
  generated from the model's own decoder (/dev/shm generator, the same `fetchDecode_of` form as
  Projects/rmk/MemmoveFetch.lean) and checked by the kernel against the packed ELF.

  Original e5r code, Apache-2.0. Regenerate rather than edit by hand.
-/
import Projects.rmk.Fetch

set_option maxRecDepth 100000

namespace E5R.Rmk.TailFetch
open E5R E5R.Rmk

theorem f8001d576 : fetchDecode img 0x8001d576 = some (E5R.Instr.opimm (E5R.AluOp.add) 2 2 0xffffffe0#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1101) (by decide +kernel) (by decide +kernel)
theorem f8001d578 : fetchDecode img 0x8001d578 = some (E5R.Instr.store (E5R.Width.w) 2 1 0x0000001c#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xce06) (by decide +kernel) (by decide +kernel)
theorem f8001d57a : fetchDecode img 0x8001d57a = some (E5R.Instr.store (E5R.Width.w) 2 8 0x00000018#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xcc22) (by decide +kernel) (by decide +kernel)
theorem f8001d57c : fetchDecode img 0x8001d57c = some (E5R.Instr.store (E5R.Width.w) 2 9 0x00000014#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xca26) (by decide +kernel) (by decide +kernel)
theorem f8001d57e : fetchDecode img 0x8001d57e = some (E5R.Instr.store (E5R.Width.w) 2 18 0x00000010#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc84a) (by decide +kernel) (by decide +kernel)
theorem f8001d580 : fetchDecode img 0x8001d580 = some (E5R.Instr.store (E5R.Width.w) 2 19 0x0000000c#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc64e) (by decide +kernel) (by decide +kernel)
theorem f8001d582 : fetchDecode img 0x8001d582 = some (E5R.Instr.op (E5R.AluOp.add) 18 0 12, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8932) (by decide +kernel) (by decide +kernel)
theorem f8001d584 : fetchDecode img 0x8001d584 = some (E5R.Instr.op (E5R.AluOp.add) 8 0 10, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x842a) (by decide +kernel) (by decide +kernel)
theorem f8001d586 : fetchDecode img 0x8001d586 = some (E5R.Instr.load (E5R.Width.w) true 10 10 0x00000000#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4108) (by decide +kernel) (by decide +kernel)
theorem f8001d588 : fetchDecode img 0x8001d588 = some (E5R.Instr.load (E5R.Width.w) true 9 8 0x00000004#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4044) (by decide +kernel) (by decide +kernel)
theorem f8001d58a : fetchDecode img 0x8001d58a = some (E5R.Instr.op (E5R.AluOp.add) 19 0 11, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x89ae) (by decide +kernel) (by decide +kernel)
theorem f8001d58c : fetchDecode img 0x8001d58c = some (E5R.Instr.branch (E5R.BrCond.eq) 10 0 0x00000022#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc10d) (by decide +kernel) (by decide +kernel)
theorem f8001d58e : fetchDecode img 0x8001d58e = some (E5R.Instr.branch (E5R.BrCond.ltu) 18 9 0x00000050#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4996863) (by decide +kernel) (by decide +kernel)
theorem f8001d592 : fetchDecode img 0x8001d592 = some (E5R.Instr.branch (E5R.BrCond.ltu) 9 10 0x00000062#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x6a4e163) (by decide +kernel) (by decide +kernel)
theorem f8001d596 : fetchDecode img 0x8001d596 = some (E5R.Instr.op (E5R.AluOp.sub) 9 9 10, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8c89) (by decide +kernel) (by decide +kernel)
theorem f8001d598 : fetchDecode img 0x8001d598 = some (E5R.Instr.op (E5R.AluOp.add) 11 19 10, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xa985b3) (by decide +kernel) (by decide +kernel)
theorem f8001d59c : fetchDecode img 0x8001d59c = some (E5R.Instr.op (E5R.AluOp.add) 10 0 19, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x854e) (by decide +kernel) (by decide +kernel)
theorem f8001d59e : fetchDecode img 0x8001d59e = some (E5R.Instr.op (E5R.AluOp.add) 12 0 9, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8626) (by decide +kernel) (by decide +kernel)
theorem f8001d5a0 : fetchDecode img 0x8001d5a0 = some (E5R.Instr.auipc 1 0x00003000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x3097) (by decide +kernel) (by decide +kernel)
theorem f8001d5a4 : fetchDecode img 0x8001d5a4 = some (E5R.Instr.jalr 1 1 0x0000067e#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x67e080e7) (by decide +kernel) (by decide +kernel)
theorem f8001d5a8 : fetchDecode img 0x8001d5a8 = some (E5R.Instr.store (E5R.Width.w) 8 0 0x00000000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x42023) (by decide +kernel) (by decide +kernel)
theorem f8001d5ac : fetchDecode img 0x8001d5ac = some (E5R.Instr.store (E5R.Width.w) 8 9 0x00000004#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc044) (by decide +kernel) (by decide +kernel)
theorem f8001d5ae : fetchDecode img 0x8001d5ae = some (E5R.Instr.branch (E5R.BrCond.ltu) 18 9 0x0000001a#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x996d63) (by decide +kernel) (by decide +kernel)
theorem f8001d5b2 : fetchDecode img 0x8001d5b2 = some (E5R.Instr.op (E5R.AluOp.sub) 11 18 9, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x409905b3) (by decide +kernel) (by decide +kernel)
theorem f8001d5b6 : fetchDecode img 0x8001d5b6 = some (E5R.Instr.op (E5R.AluOp.add) 10 19 9, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x998533) (by decide +kernel) (by decide +kernel)
theorem f8001d5ba : fetchDecode img 0x8001d5ba = some (E5R.Instr.load (E5R.Width.w) true 1 2 0x0000001c#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x40f2) (by decide +kernel) (by decide +kernel)
theorem f8001d5bc : fetchDecode img 0x8001d5bc = some (E5R.Instr.load (E5R.Width.w) true 8 2 0x00000018#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4462) (by decide +kernel) (by decide +kernel)
theorem f8001d5be : fetchDecode img 0x8001d5be = some (E5R.Instr.load (E5R.Width.w) true 9 2 0x00000014#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x44d2) (by decide +kernel) (by decide +kernel)
theorem f8001d5c0 : fetchDecode img 0x8001d5c0 = some (E5R.Instr.load (E5R.Width.w) true 18 2 0x00000010#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4942) (by decide +kernel) (by decide +kernel)
theorem f8001d5c2 : fetchDecode img 0x8001d5c2 = some (E5R.Instr.load (E5R.Width.w) true 19 2 0x0000000c#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x49b2) (by decide +kernel) (by decide +kernel)
theorem f8001d5c4 : fetchDecode img 0x8001d5c4 = some (E5R.Instr.opimm (E5R.AluOp.add) 2 2 0x00000020#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x6105) (by decide +kernel) (by decide +kernel)
theorem f8001d5c6 : fetchDecode img 0x8001d5c6 = some (E5R.Instr.jalr 0 1 0x00000000#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8082) (by decide +kernel) (by decide +kernel)
theorem f8001d5c8 : fetchDecode img 0x8001d5c8 = some (E5R.Instr.lui 13 0x80028000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x800286b7) (by decide +kernel) (by decide +kernel)
theorem f8001d5cc : fetchDecode img 0x8001d5cc = some (E5R.Instr.opimm (E5R.AluOp.add) 13 13 0xfffffe44#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xe4468693) (by decide +kernel) (by decide +kernel)
theorem f8001d5d0 : fetchDecode img 0x8001d5d0 = some (E5R.Instr.op (E5R.AluOp.add) 10 0 9, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8526) (by decide +kernel) (by decide +kernel)
theorem f8001d5d2 : fetchDecode img 0x8001d5d2 = some (E5R.Instr.op (E5R.AluOp.add) 11 0 18, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x85ca) (by decide +kernel) (by decide +kernel)
theorem f8001d5d4 : fetchDecode img 0x8001d5d4 = some (E5R.Instr.op (E5R.AluOp.add) 12 0 18, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x864a) (by decide +kernel) (by decide +kernel)
theorem f8001d5d6 : fetchDecode img 0x8001d5d6 = some (E5R.Instr.auipc 1 0x00002000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2097) (by decide +kernel) (by decide +kernel)
theorem f8001d5da : fetchDecode img 0x8001d5da = some (E5R.Instr.jalr 1 1 0x00000526#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x526080e7) (by decide +kernel) (by decide +kernel)
theorem f8001d5de : fetchDecode img 0x8001d5de = some (E5R.Instr.lui 13 0x80028000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x800286b7) (by decide +kernel) (by decide +kernel)
theorem f8001d5e2 : fetchDecode img 0x8001d5e2 = some (E5R.Instr.opimm (E5R.AluOp.add) 13 13 0xfffffc20#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc2068693) (by decide +kernel) (by decide +kernel)
theorem f8001d5e6 : fetchDecode img 0x8001d5e6 = some (E5R.Instr.opimm (E5R.AluOp.add) 10 0 0x00000000#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4501) (by decide +kernel) (by decide +kernel)
theorem f8001d5e8 : fetchDecode img 0x8001d5e8 = some (E5R.Instr.op (E5R.AluOp.add) 11 0 9, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x85a6) (by decide +kernel) (by decide +kernel)
theorem f8001d5ea : fetchDecode img 0x8001d5ea = some (E5R.Instr.op (E5R.AluOp.add) 12 0 18, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x864a) (by decide +kernel) (by decide +kernel)
theorem f8001d5ec : fetchDecode img 0x8001d5ec = some (E5R.Instr.auipc 1 0x00002000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2097) (by decide +kernel) (by decide +kernel)
theorem f8001d5f0 : fetchDecode img 0x8001d5f0 = some (E5R.Instr.jalr 1 1 0x00000510#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x510080e7) (by decide +kernel) (by decide +kernel)
theorem f8001d5f4 : fetchDecode img 0x8001d5f4 = some (E5R.Instr.lui 13 0x80028000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x800286b7) (by decide +kernel) (by decide +kernel)
theorem f8001d5f8 : fetchDecode img 0x8001d5f8 = some (E5R.Instr.opimm (E5R.AluOp.add) 13 13 0xfffffc30#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc3068693) (by decide +kernel) (by decide +kernel)
theorem f8001d5fc : fetchDecode img 0x8001d5fc = some (E5R.Instr.op (E5R.AluOp.add) 11 0 9, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x85a6) (by decide +kernel) (by decide +kernel)
theorem f8001d5fe : fetchDecode img 0x8001d5fe = some (E5R.Instr.op (E5R.AluOp.add) 12 0 18, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x864a) (by decide +kernel) (by decide +kernel)
theorem f8001d600 : fetchDecode img 0x8001d600 = some (E5R.Instr.auipc 1 0x00002000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2097) (by decide +kernel) (by decide +kernel)
theorem f8001d604 : fetchDecode img 0x8001d604 = some (E5R.Instr.jalr 1 1 0x000004fc#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4fc080e7) (by decide +kernel) (by decide +kernel)

end E5R.Rmk.TailFetch
