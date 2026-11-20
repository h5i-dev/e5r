/-
  Instruction facts for `Deframer::tail` (0x8001d576..0x8001d608) in the pinned RMK image,
  generated from the model's own decoder (/dev/shm generator, the same `fetchDecode_of` form as
  Projects/rmk/MemmoveFetch.lean) and checked by the kernel against the packed ELF.

  Original nocompiler code, Apache-2.0. Regenerate rather than edit by hand.
-/
import Projects.rmk.Fetch

set_option maxRecDepth 100000

namespace NoCompiler.Rmk.TailFetch
open NoCompiler NoCompiler.Rmk

theorem f8001d576 : fetchDecode img 0x8001d576 = some (NoCompiler.Instr.opimm (NoCompiler.AluOp.add) 2 2 0xffffffe0#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1101) (by decide +kernel) (by decide +kernel)
theorem f8001d578 : fetchDecode img 0x8001d578 = some (NoCompiler.Instr.store (NoCompiler.Width.w) 2 1 0x0000001c#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xce06) (by decide +kernel) (by decide +kernel)
theorem f8001d57a : fetchDecode img 0x8001d57a = some (NoCompiler.Instr.store (NoCompiler.Width.w) 2 8 0x00000018#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xcc22) (by decide +kernel) (by decide +kernel)
theorem f8001d57c : fetchDecode img 0x8001d57c = some (NoCompiler.Instr.store (NoCompiler.Width.w) 2 9 0x00000014#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xca26) (by decide +kernel) (by decide +kernel)
theorem f8001d57e : fetchDecode img 0x8001d57e = some (NoCompiler.Instr.store (NoCompiler.Width.w) 2 18 0x00000010#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc84a) (by decide +kernel) (by decide +kernel)
theorem f8001d580 : fetchDecode img 0x8001d580 = some (NoCompiler.Instr.store (NoCompiler.Width.w) 2 19 0x0000000c#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc64e) (by decide +kernel) (by decide +kernel)
theorem f8001d582 : fetchDecode img 0x8001d582 = some (NoCompiler.Instr.op (NoCompiler.AluOp.add) 18 0 12, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8932) (by decide +kernel) (by decide +kernel)
theorem f8001d584 : fetchDecode img 0x8001d584 = some (NoCompiler.Instr.op (NoCompiler.AluOp.add) 8 0 10, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x842a) (by decide +kernel) (by decide +kernel)
theorem f8001d586 : fetchDecode img 0x8001d586 = some (NoCompiler.Instr.load (NoCompiler.Width.w) true 10 10 0x00000000#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4108) (by decide +kernel) (by decide +kernel)
theorem f8001d588 : fetchDecode img 0x8001d588 = some (NoCompiler.Instr.load (NoCompiler.Width.w) true 9 8 0x00000004#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4044) (by decide +kernel) (by decide +kernel)
theorem f8001d58a : fetchDecode img 0x8001d58a = some (NoCompiler.Instr.op (NoCompiler.AluOp.add) 19 0 11, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x89ae) (by decide +kernel) (by decide +kernel)
theorem f8001d58c : fetchDecode img 0x8001d58c = some (NoCompiler.Instr.branch (NoCompiler.BrCond.eq) 10 0 0x00000022#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc10d) (by decide +kernel) (by decide +kernel)
theorem f8001d58e : fetchDecode img 0x8001d58e = some (NoCompiler.Instr.branch (NoCompiler.BrCond.ltu) 18 9 0x00000050#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4996863) (by decide +kernel) (by decide +kernel)
theorem f8001d592 : fetchDecode img 0x8001d592 = some (NoCompiler.Instr.branch (NoCompiler.BrCond.ltu) 9 10 0x00000062#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x6a4e163) (by decide +kernel) (by decide +kernel)
theorem f8001d596 : fetchDecode img 0x8001d596 = some (NoCompiler.Instr.op (NoCompiler.AluOp.sub) 9 9 10, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8c89) (by decide +kernel) (by decide +kernel)
theorem f8001d598 : fetchDecode img 0x8001d598 = some (NoCompiler.Instr.op (NoCompiler.AluOp.add) 11 19 10, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xa985b3) (by decide +kernel) (by decide +kernel)
theorem f8001d59c : fetchDecode img 0x8001d59c = some (NoCompiler.Instr.op (NoCompiler.AluOp.add) 10 0 19, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x854e) (by decide +kernel) (by decide +kernel)
theorem f8001d59e : fetchDecode img 0x8001d59e = some (NoCompiler.Instr.op (NoCompiler.AluOp.add) 12 0 9, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8626) (by decide +kernel) (by decide +kernel)
theorem f8001d5a0 : fetchDecode img 0x8001d5a0 = some (NoCompiler.Instr.auipc 1 0x00003000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x3097) (by decide +kernel) (by decide +kernel)
theorem f8001d5a4 : fetchDecode img 0x8001d5a4 = some (NoCompiler.Instr.jalr 1 1 0x0000067e#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x67e080e7) (by decide +kernel) (by decide +kernel)
theorem f8001d5a8 : fetchDecode img 0x8001d5a8 = some (NoCompiler.Instr.store (NoCompiler.Width.w) 8 0 0x00000000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x42023) (by decide +kernel) (by decide +kernel)
theorem f8001d5ac : fetchDecode img 0x8001d5ac = some (NoCompiler.Instr.store (NoCompiler.Width.w) 8 9 0x00000004#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc044) (by decide +kernel) (by decide +kernel)
theorem f8001d5ae : fetchDecode img 0x8001d5ae = some (NoCompiler.Instr.branch (NoCompiler.BrCond.ltu) 18 9 0x0000001a#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x996d63) (by decide +kernel) (by decide +kernel)
theorem f8001d5b2 : fetchDecode img 0x8001d5b2 = some (NoCompiler.Instr.op (NoCompiler.AluOp.sub) 11 18 9, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x409905b3) (by decide +kernel) (by decide +kernel)
theorem f8001d5b6 : fetchDecode img 0x8001d5b6 = some (NoCompiler.Instr.op (NoCompiler.AluOp.add) 10 19 9, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x998533) (by decide +kernel) (by decide +kernel)
theorem f8001d5ba : fetchDecode img 0x8001d5ba = some (NoCompiler.Instr.load (NoCompiler.Width.w) true 1 2 0x0000001c#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x40f2) (by decide +kernel) (by decide +kernel)
theorem f8001d5bc : fetchDecode img 0x8001d5bc = some (NoCompiler.Instr.load (NoCompiler.Width.w) true 8 2 0x00000018#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4462) (by decide +kernel) (by decide +kernel)
theorem f8001d5be : fetchDecode img 0x8001d5be = some (NoCompiler.Instr.load (NoCompiler.Width.w) true 9 2 0x00000014#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x44d2) (by decide +kernel) (by decide +kernel)
theorem f8001d5c0 : fetchDecode img 0x8001d5c0 = some (NoCompiler.Instr.load (NoCompiler.Width.w) true 18 2 0x00000010#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4942) (by decide +kernel) (by decide +kernel)
theorem f8001d5c2 : fetchDecode img 0x8001d5c2 = some (NoCompiler.Instr.load (NoCompiler.Width.w) true 19 2 0x0000000c#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x49b2) (by decide +kernel) (by decide +kernel)
theorem f8001d5c4 : fetchDecode img 0x8001d5c4 = some (NoCompiler.Instr.opimm (NoCompiler.AluOp.add) 2 2 0x00000020#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x6105) (by decide +kernel) (by decide +kernel)
theorem f8001d5c6 : fetchDecode img 0x8001d5c6 = some (NoCompiler.Instr.jalr 0 1 0x00000000#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8082) (by decide +kernel) (by decide +kernel)
theorem f8001d5c8 : fetchDecode img 0x8001d5c8 = some (NoCompiler.Instr.lui 13 0x80028000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x800286b7) (by decide +kernel) (by decide +kernel)
theorem f8001d5cc : fetchDecode img 0x8001d5cc = some (NoCompiler.Instr.opimm (NoCompiler.AluOp.add) 13 13 0xfffffe44#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xe4468693) (by decide +kernel) (by decide +kernel)
theorem f8001d5d0 : fetchDecode img 0x8001d5d0 = some (NoCompiler.Instr.op (NoCompiler.AluOp.add) 10 0 9, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8526) (by decide +kernel) (by decide +kernel)
theorem f8001d5d2 : fetchDecode img 0x8001d5d2 = some (NoCompiler.Instr.op (NoCompiler.AluOp.add) 11 0 18, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x85ca) (by decide +kernel) (by decide +kernel)
theorem f8001d5d4 : fetchDecode img 0x8001d5d4 = some (NoCompiler.Instr.op (NoCompiler.AluOp.add) 12 0 18, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x864a) (by decide +kernel) (by decide +kernel)
theorem f8001d5d6 : fetchDecode img 0x8001d5d6 = some (NoCompiler.Instr.auipc 1 0x00002000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2097) (by decide +kernel) (by decide +kernel)
theorem f8001d5da : fetchDecode img 0x8001d5da = some (NoCompiler.Instr.jalr 1 1 0x00000526#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x526080e7) (by decide +kernel) (by decide +kernel)
theorem f8001d5de : fetchDecode img 0x8001d5de = some (NoCompiler.Instr.lui 13 0x80028000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x800286b7) (by decide +kernel) (by decide +kernel)
theorem f8001d5e2 : fetchDecode img 0x8001d5e2 = some (NoCompiler.Instr.opimm (NoCompiler.AluOp.add) 13 13 0xfffffc20#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc2068693) (by decide +kernel) (by decide +kernel)
theorem f8001d5e6 : fetchDecode img 0x8001d5e6 = some (NoCompiler.Instr.opimm (NoCompiler.AluOp.add) 10 0 0x00000000#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4501) (by decide +kernel) (by decide +kernel)
theorem f8001d5e8 : fetchDecode img 0x8001d5e8 = some (NoCompiler.Instr.op (NoCompiler.AluOp.add) 11 0 9, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x85a6) (by decide +kernel) (by decide +kernel)
theorem f8001d5ea : fetchDecode img 0x8001d5ea = some (NoCompiler.Instr.op (NoCompiler.AluOp.add) 12 0 18, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x864a) (by decide +kernel) (by decide +kernel)
theorem f8001d5ec : fetchDecode img 0x8001d5ec = some (NoCompiler.Instr.auipc 1 0x00002000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2097) (by decide +kernel) (by decide +kernel)
theorem f8001d5f0 : fetchDecode img 0x8001d5f0 = some (NoCompiler.Instr.jalr 1 1 0x00000510#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x510080e7) (by decide +kernel) (by decide +kernel)
theorem f8001d5f4 : fetchDecode img 0x8001d5f4 = some (NoCompiler.Instr.lui 13 0x80028000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x800286b7) (by decide +kernel) (by decide +kernel)
theorem f8001d5f8 : fetchDecode img 0x8001d5f8 = some (NoCompiler.Instr.opimm (NoCompiler.AluOp.add) 13 13 0xfffffc30#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc3068693) (by decide +kernel) (by decide +kernel)
theorem f8001d5fc : fetchDecode img 0x8001d5fc = some (NoCompiler.Instr.op (NoCompiler.AluOp.add) 11 0 9, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x85a6) (by decide +kernel) (by decide +kernel)
theorem f8001d5fe : fetchDecode img 0x8001d5fe = some (NoCompiler.Instr.op (NoCompiler.AluOp.add) 12 0 18, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x864a) (by decide +kernel) (by decide +kernel)
theorem f8001d600 : fetchDecode img 0x8001d600 = some (NoCompiler.Instr.auipc 1 0x00002000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2097) (by decide +kernel) (by decide +kernel)
theorem f8001d604 : fetchDecode img 0x8001d604 = some (NoCompiler.Instr.jalr 1 1 0x000004fc#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4fc080e7) (by decide +kernel) (by decide +kernel)

end NoCompiler.Rmk.TailFetch
