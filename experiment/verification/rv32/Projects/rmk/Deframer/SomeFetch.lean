/-
  Instruction facts for the session's Some path (0x80003e70..0x80003fd8: the message header test,
  the dispatch call 0x80003e9a, encode_frame 0x80003f1a, the response slice and send set-up, the
  0xff/0xfe result branches and the call at 0x80003fd0), in the pinned RMK image, generated from the
  model's own decoder (/dev/shm generator, the `fetchDecode_of` form of
  Projects/rmk/Deframer/TailFetch.lean) and checked by the kernel against the packed ELF.

  Original e5r code, Apache-2.0. Regenerate rather than edit by hand.
-/
import Projects.rmk.Fetch

set_option maxRecDepth 100000

namespace E5R.Rmk.SomeFetch
open E5R E5R.Rmk

theorem f80003e70 : fetchDecode img 0x80003e70 = some (E5R.Instr.load (E5R.Width.h) true 10 22 0x000000cb#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xcbb1503) (by decide +kernel) (by decide +kernel)

theorem f80003e74 : fetchDecode img 0x80003e74 = some (E5R.Instr.store (E5R.Width.h) 22 10 0x000002eb#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2eab15a3) (by decide +kernel) (by decide +kernel)

theorem f80003e78 : fetchDecode img 0x80003e78 = some (E5R.Instr.branch (E5R.BrCond.lt) 10 0 0x00000160#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x16054063) (by decide +kernel) (by decide +kernel)

theorem f80003e7c : fetchDecode img 0x80003e7c = some (E5R.Instr.load (E5R.Width.w) true 10 22 0x000002c3#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2c3b2503) (by decide +kernel) (by decide +kernel)

theorem f80003e80 : fetchDecode img 0x80003e80 = some (E5R.Instr.store (E5R.Width.w) 22 10 0x000002f3#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2eab29a3) (by decide +kernel) (by decide +kernel)

theorem f80003e84 : fetchDecode img 0x80003e84 = some (E5R.Instr.load (E5R.Width.w) true 10 2 0x00000020#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x5502) (by decide +kernel) (by decide +kernel)

theorem f80003e86 : fetchDecode img 0x80003e86 = some (E5R.Instr.store (E5R.Width.w) 22 10 0x000002f7#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2eab2ba3) (by decide +kernel) (by decide +kernel)

theorem f80003e8a : fetchDecode img 0x80003e8a = some (E5R.Instr.store (E5R.Width.w) 22 9 0x000002fb#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2e9b2da3) (by decide +kernel) (by decide +kernel)

theorem f80003e8e : fetchDecode img 0x80003e8e = some (E5R.Instr.store (E5R.Width.b) 22 0 0x000002ff#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2e0b0fa3) (by decide +kernel) (by decide +kernel)

theorem f80003e92 : fetchDecode img 0x80003e92 = some (E5R.Instr.opimm (E5R.AluOp.add) 10 22 0x000002f3#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2f3b0513) (by decide +kernel) (by decide +kernel)

theorem f80003e96 : fetchDecode img 0x80003e96 = some (E5R.Instr.auipc 1 0xffffc000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xffffc097) (by decide +kernel) (by decide +kernel)

theorem f80003e9a : fetchDecode img 0x80003e9a = some (E5R.Instr.jalr 1 1 0x0000035c#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x35c080e7) (by decide +kernel) (by decide +kernel)

theorem f80003e9e : fetchDecode img 0x80003e9e = some (E5R.Instr.opimm (E5R.AluOp.and) 11 10 0x000000ff#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xff57593) (by decide +kernel) (by decide +kernel)

theorem f80003ea2 : fetchDecode img 0x80003ea2 = some (E5R.Instr.opimm (E5R.AluOp.add) 12 0 0x000000fe#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfe00613) (by decide +kernel) (by decide +kernel)

theorem f80003ea6 : fetchDecode img 0x80003ea6 = some (E5R.Instr.branch (E5R.BrCond.eq) 11 12 0x0000035e#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x34c58f63) (by decide +kernel) (by decide +kernel)

theorem f80003eaa : fetchDecode img 0x80003eaa = some (E5R.Instr.load (E5R.Width.h) false 12 22 0x000002eb#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2ebb5603) (by decide +kernel) (by decide +kernel)

theorem f80003eae : fetchDecode img 0x80003eae = some (E5R.Instr.load (E5R.Width.b) false 13 22 0x000002ed#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2edb4683) (by decide +kernel) (by decide +kernel)

theorem f80003eb2 : fetchDecode img 0x80003eb2 = some (E5R.Instr.opimm (E5R.AluOp.add) 12 12 0xfffffffe#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1679) (by decide +kernel) (by decide +kernel)

theorem f80003eb4 : fetchDecode img 0x80003eb4 = some (E5R.Instr.opimm (E5R.AluOp.sltu) 12 12 0x00000001#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x163613) (by decide +kernel) (by decide +kernel)

theorem f80003eb8 : fetchDecode img 0x80003eb8 = some (E5R.Instr.op (E5R.AluOp.or) 12 12 13, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8e55) (by decide +kernel) (by decide +kernel)

theorem f80003eba : fetchDecode img 0x80003eba = some (E5R.Instr.opimm (E5R.AluOp.add) 13 0 0x000000ff#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xff00693) (by decide +kernel) (by decide +kernel)

theorem f80003ebe : fetchDecode img 0x80003ebe = some (E5R.Instr.store (E5R.Width.b) 22 12 0x000002ed#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2ecb06a3) (by decide +kernel) (by decide +kernel)

theorem f80003ec2 : fetchDecode img 0x80003ec2 = some (E5R.Instr.branch (E5R.BrCond.eq) 11 13 0x000000e4#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xed58263) (by decide +kernel) (by decide +kernel)

theorem f80003ec6 : fetchDecode img 0x80003ec6 = some (E5R.Instr.load (E5R.Width.w) true 12 22 0x000002db#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2dbb2603) (by decide +kernel) (by decide +kernel)

theorem f80003eca : fetchDecode img 0x80003eca = some (E5R.Instr.store (E5R.Width.b) 22 10 0x000002f3#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2eab09a3) (by decide +kernel) (by decide +kernel)

theorem f80003ece : fetchDecode img 0x80003ece = some (E5R.Instr.opimm (E5R.AluOp.add) 11 11 0xfffffffd#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x15f5) (by decide +kernel) (by decide +kernel)

theorem f80003ed0 : fetchDecode img 0x80003ed0 = some (E5R.Instr.op (E5R.AluOp.sltu) 12 0 12, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc03633) (by decide +kernel) (by decide +kernel)

theorem f80003ed4 : fetchDecode img 0x80003ed4 = some (E5R.Instr.opimm (E5R.AluOp.sltu) 11 11 0x00000001#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x15b593) (by decide +kernel) (by decide +kernel)

theorem f80003ed8 : fetchDecode img 0x80003ed8 = some (E5R.Instr.op (E5R.AluOp.and) 12 12 11, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8e6d) (by decide +kernel) (by decide +kernel)

theorem f80003eda : fetchDecode img 0x80003eda = some (E5R.Instr.opimm (E5R.AluOp.add) 11 0 0x00000008#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x45a1) (by decide +kernel) (by decide +kernel)

theorem f80003edc : fetchDecode img 0x80003edc = some (E5R.Instr.branch (E5R.BrCond.ne) 12 0 0x00000004#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xe211) (by decide +kernel) (by decide +kernel)

theorem f80003ede : fetchDecode img 0x80003ede = some (E5R.Instr.op (E5R.AluOp.add) 11 0 10, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x85aa) (by decide +kernel) (by decide +kernel)

theorem f80003ee0 : fetchDecode img 0x80003ee0 = some (E5R.Instr.opimm (E5R.AluOp.add) 8 23 0x000003e2#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x3e2b8413) (by decide +kernel) (by decide +kernel)

theorem f80003ee4 : fetchDecode img 0x80003ee4 = some (E5R.Instr.store (E5R.Width.b) 23 0 0x000003e2#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x3e0b8123) (by decide +kernel) (by decide +kernel)

theorem f80003ee8 : fetchDecode img 0x80003ee8 = some (E5R.Instr.load (E5R.Width.h) true 13 22 0x000000cb#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xcbb1683) (by decide +kernel) (by decide +kernel)

theorem f80003eec : fetchDecode img 0x80003eec = some (E5R.Instr.load (E5R.Width.b) false 14 22 0x000000cd#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xcdb4703) (by decide +kernel) (by decide +kernel)

theorem f80003ef0 : fetchDecode img 0x80003ef0 = some (E5R.Instr.store (E5R.Width.b) 8 0 0x00000001#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x400a3) (by decide +kernel) (by decide +kernel)

theorem f80003ef4 : fetchDecode img 0x80003ef4 = some (E5R.Instr.store (E5R.Width.b) 8 0 0x00000002#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x40123) (by decide +kernel) (by decide +kernel)

theorem f80003ef8 : fetchDecode img 0x80003ef8 = some (E5R.Instr.store (E5R.Width.b) 8 0 0x00000003#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x401a3) (by decide +kernel) (by decide +kernel)

theorem f80003efc : fetchDecode img 0x80003efc = some (E5R.Instr.store (E5R.Width.b) 8 0 0x00000004#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x40223) (by decide +kernel) (by decide +kernel)

theorem f80003f00 : fetchDecode img 0x80003f00 = some (E5R.Instr.store (E5R.Width.b) 8 0 0x00000005#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x402a3) (by decide +kernel) (by decide +kernel)

theorem f80003f04 : fetchDecode img 0x80003f04 = some (E5R.Instr.store (E5R.Width.b) 8 0 0x00000006#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x40323) (by decide +kernel) (by decide +kernel)

theorem f80003f08 : fetchDecode img 0x80003f08 = some (E5R.Instr.store (E5R.Width.b) 2 11 0x00000140#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x14b10023) (by decide +kernel) (by decide +kernel)

theorem f80003f0c : fetchDecode img 0x80003f0c = some (E5R.Instr.opimm (E5R.AluOp.add) 10 2 0x00000040#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x88) (by decide +kernel) (by decide +kernel)

theorem f80003f0e : fetchDecode img 0x80003f0e = some (E5R.Instr.opimm (E5R.AluOp.add) 12 0 0x00000007#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x461d) (by decide +kernel) (by decide +kernel)

theorem f80003f10 : fetchDecode img 0x80003f10 = some (E5R.Instr.opimm (E5R.AluOp.add) 15 2 0x00000140#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x29c) (by decide +kernel) (by decide +kernel)

theorem f80003f12 : fetchDecode img 0x80003f12 = some (E5R.Instr.opimm (E5R.AluOp.add) 9 0 0x00000007#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x449d) (by decide +kernel) (by decide +kernel)

theorem f80003f14 : fetchDecode img 0x80003f14 = some (E5R.Instr.op (E5R.AluOp.add) 11 0 8, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x85a2) (by decide +kernel) (by decide +kernel)

theorem f80003f16 : fetchDecode img 0x80003f16 = some (E5R.Instr.auipc 1 0x00005000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x5097) (by decide +kernel) (by decide +kernel)

theorem f80003f1a : fetchDecode img 0x80003f1a = some (E5R.Instr.jalr 1 1 0xfffffe46#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xe46080e7) (by decide +kernel) (by decide +kernel)

theorem f80003f1e : fetchDecode img 0x80003f1e = some (E5R.Instr.load (E5R.Width.b) false 10 2 0x00000040#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4014503) (by decide +kernel) (by decide +kernel)

theorem f80003f22 : fetchDecode img 0x80003f22 = some (E5R.Instr.load (E5R.Width.w) true 11 2 0x00000044#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4596) (by decide +kernel) (by decide +kernel)

theorem f80003f24 : fetchDecode img 0x80003f24 = some (E5R.Instr.opimm (E5R.AluOp.add) 10 10 0xffffffff#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x157d) (by decide +kernel) (by decide +kernel)

theorem f80003f26 : fetchDecode img 0x80003f26 = some (E5R.Instr.op (E5R.AluOp.and) 11 11 10, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8de9) (by decide +kernel) (by decide +kernel)

theorem f80003f28 : fetchDecode img 0x80003f28 = some (E5R.Instr.branch (E5R.BrCond.ltu) 9 11 0x000002e8#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2eb4e463) (by decide +kernel) (by decide +kernel)

theorem f80003f2c : fetchDecode img 0x80003f2c = some (E5R.Instr.load (E5R.Width.w) true 10 22 0x000002cb#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2cbb2503) (by decide +kernel) (by decide +kernel)

theorem f80003f30 : fetchDecode img 0x80003f30 = some (E5R.Instr.store (E5R.Width.w) 22 10 0x000002fb#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2eab2da3) (by decide +kernel) (by decide +kernel)

theorem f80003f34 : fetchDecode img 0x80003f34 = some (E5R.Instr.store (E5R.Width.w) 22 8 0x000002ff#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2e8b2fa3) (by decide +kernel) (by decide +kernel)

theorem f80003f38 : fetchDecode img 0x80003f38 = some (E5R.Instr.store (E5R.Width.w) 22 11 0x00000303#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x30bb21a3) (by decide +kernel) (by decide +kernel)

theorem f80003f3c : fetchDecode img 0x80003f3c = some (E5R.Instr.store (E5R.Width.b) 22 0 0x00000333#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x320b09a3) (by decide +kernel) (by decide +kernel)

theorem f80003f40 : fetchDecode img 0x80003f40 = some (E5R.Instr.store (E5R.Width.w) 22 10 0x00000307#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x30ab23a3) (by decide +kernel) (by decide +kernel)

theorem f80003f44 : fetchDecode img 0x80003f44 = some (E5R.Instr.store (E5R.Width.w) 22 8 0x0000030b#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x308b25a3) (by decide +kernel) (by decide +kernel)

theorem f80003f48 : fetchDecode img 0x80003f48 = some (E5R.Instr.store (E5R.Width.w) 22 11 0x0000030f#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x30bb27a3) (by decide +kernel) (by decide +kernel)

theorem f80003f4c : fetchDecode img 0x80003f4c = some (E5R.Instr.branch (E5R.BrCond.ne) 11 0 0x00000352#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x34059963) (by decide +kernel) (by decide +kernel)

theorem f80003f50 : fetchDecode img 0x80003f50 = some (E5R.Instr.opimm (E5R.AluOp.add) 10 0 0x00000001#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4505) (by decide +kernel) (by decide +kernel)

theorem f80003f52 : fetchDecode img 0x80003f52 = some (E5R.Instr.store (E5R.Width.b) 26 10 0x00000000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xad0023) (by decide +kernel) (by decide +kernel)

theorem f80003f56 : fetchDecode img 0x80003f56 = some (E5R.Instr.jal 0 0x00000082#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xa049) (by decide +kernel) (by decide +kernel)

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

theorem f80003fa6 : fetchDecode img 0x80003fa6 = some (E5R.Instr.load (E5R.Width.w) true 8 22 0x000002cb#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2cbb2403) (by decide +kernel) (by decide +kernel)

theorem f80003faa : fetchDecode img 0x80003faa = some (E5R.Instr.opimm (E5R.AluOp.add) 10 23 0x000001b1#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1b1b8513) (by decide +kernel) (by decide +kernel)

theorem f80003fae : fetchDecode img 0x80003fae = some (E5R.Instr.auipc 1 0x00018000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x18097) (by decide +kernel) (by decide +kernel)

theorem f80003fb2 : fetchDecode img 0x80003fb2 = some (E5R.Instr.jalr 1 1 0x0000044e#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x44e080e7) (by decide +kernel) (by decide +kernel)

theorem f80003fb6 : fetchDecode img 0x80003fb6 = some (E5R.Instr.store (E5R.Width.w) 22 8 0x000002f3#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2e8b29a3) (by decide +kernel) (by decide +kernel)

theorem f80003fba : fetchDecode img 0x80003fba = some (E5R.Instr.store (E5R.Width.w) 22 10 0x000002f7#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2eab2ba3) (by decide +kernel) (by decide +kernel)

theorem f80003fbe : fetchDecode img 0x80003fbe = some (E5R.Instr.store (E5R.Width.w) 22 11 0x000002fb#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2ebb2da3) (by decide +kernel) (by decide +kernel)

theorem f80003fc2 : fetchDecode img 0x80003fc2 = some (E5R.Instr.store (E5R.Width.b) 22 0 0x0000032b#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x320b05a3) (by decide +kernel) (by decide +kernel)

theorem f80003fc6 : fetchDecode img 0x80003fc6 = some (E5R.Instr.opimm (E5R.AluOp.add) 10 23 0x000003e1#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x3e1b8513) (by decide +kernel) (by decide +kernel)

theorem f80003fca : fetchDecode img 0x80003fca = some (E5R.Instr.opimm (E5R.AluOp.add) 11 2 0x00000030#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x180c) (by decide +kernel) (by decide +kernel)

theorem f80003fcc : fetchDecode img 0x80003fcc = some (E5R.Instr.auipc 1 0xfffff000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfffff097) (by decide +kernel) (by decide +kernel)

theorem f80003fd0 : fetchDecode img 0x80003fd0 = some (E5R.Instr.jalr 1 1 0x0000035c#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x35c080e7) (by decide +kernel) (by decide +kernel)

theorem f80003fd4 : fetchDecode img 0x80003fd4 = some (E5R.Instr.branch (E5R.BrCond.ne) 10 0 0x00000234#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x22051a63) (by decide +kernel) (by decide +kernel)

theorem f80003fd8 : fetchDecode img 0x80003fd8 = some (E5R.Instr.load (E5R.Width.w) true 13 22 0x000002db#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2dbb2683) (by decide +kernel) (by decide +kernel)

end E5R.Rmk.SomeFetch
