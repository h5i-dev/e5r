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
theorem f80020dbc : fetchDecode img 0x80020dbc = some (Instr.opimm (AluOp.and) 17 9 0x00000003#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x34f893) (by decide +kernel) (by decide +kernel)
theorem f80020dc0 : fetchDecode img 0x80020dc0 = some (Instr.opimm (AluOp.and) 7 9 0xfffffffc#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xffc4f393) (by decide +kernel) (by decide +kernel)
theorem f80020dc4 : fetchDecode img 0x80020dc4 = some (Instr.op (AluOp.sub) 18 0 17, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x41100933) (by decide +kernel) (by decide +kernel)
theorem f80020dc8 : fetchDecode img 0x80020dc8 = some (Instr.branch (BrCond.geu) 7 9 0x00000020#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x293f063) (by decide +kernel) (by decide +kernel)
theorem f80020dcc : fetchDecode img 0x80020dcc = some (Instr.op (AluOp.add) 15 11 12, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc587b3) (by decide +kernel) (by decide +kernel)
theorem f80020dd0 : fetchDecode img 0x80020dd0 = some (Instr.opimm (AluOp.add) 15 15 0xffffffff#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x17fd) (by decide +kernel) (by decide +kernel)
theorem f80020dd2 : fetchDecode img 0x80020dd2 = some (Instr.op (AluOp.add) 13 0 9, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x86a6) (by decide +kernel) (by decide +kernel)
theorem f80020dd4 : fetchDecode img 0x80020dd4 = some (Instr.load (Width.b) false 8 15 0x00000000#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x7c403) (by decide +kernel) (by decide +kernel)
theorem f80020dd8 : fetchDecode img 0x80020dd8 = some (Instr.opimm (AluOp.add) 14 13 0xffffffff#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfff68713) (by decide +kernel) (by decide +kernel)
theorem f80020ddc : fetchDecode img 0x80020ddc = some (Instr.store (Width.b) 13 8 0xffffffff#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfe868fa3) (by decide +kernel) (by decide +kernel)
theorem f80020de0 : fetchDecode img 0x80020de0 = some (Instr.opimm (AluOp.add) 15 15 0xffffffff#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x17fd) (by decide +kernel) (by decide +kernel)
theorem f80020de2 : fetchDecode img 0x80020de2 = some (Instr.op (AluOp.add) 13 0 14, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x86ba) (by decide +kernel) (by decide +kernel)
theorem f80020de4 : fetchDecode img 0x80020de4 = some (Instr.branch (BrCond.ltu) 7 14 0xfffffff0#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfee3e8e3) (by decide +kernel) (by decide +kernel)
theorem f80020de8 : fetchDecode img 0x80020de8 = some (Instr.op (AluOp.add) 5 16 18, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x12802b3) (by decide +kernel) (by decide +kernel)
theorem f80020dec : fetchDecode img 0x80020dec = some (Instr.op (AluOp.sub) 17 12 17, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x411608b3) (by decide +kernel) (by decide +kernel)
theorem f80020df0 : fetchDecode img 0x80020df0 = some (Instr.opimm (AluOp.and) 13 17 0xfffffffc#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xffc8f693) (by decide +kernel) (by decide +kernel)
theorem f80020df4 : fetchDecode img 0x80020df4 = some (Instr.opimm (AluOp.and) 6 5 0x00000003#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x32f313) (by decide +kernel) (by decide +kernel)
theorem f80020df8 : fetchDecode img 0x80020df8 = some (Instr.op (AluOp.sub) 16 0 13, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x40d00833) (by decide +kernel) (by decide +kernel)
theorem f80020dfc : fetchDecode img 0x80020dfc = some (Instr.op (AluOp.sub) 28 7 13, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x40d38e33) (by decide +kernel) (by decide +kernel)
theorem f80020e00 : fetchDecode img 0x80020e00 = some (Instr.branch (BrCond.eq) 6 0 0x0000009e#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8030f63) (by decide +kernel) (by decide +kernel)
theorem f80020e04 : fetchDecode img 0x80020e04 = some (Instr.op (AluOp.sub) 30 5 6, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x40628f33) (by decide +kernel) (by decide +kernel)
theorem f80020e08 : fetchDecode img 0x80020e08 = some (Instr.store (Width.b) 2 0 0x0000001c#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x10e23) (by decide +kernel) (by decide +kernel)
theorem f80020e0c : fetchDecode img 0x80020e0c = some (Instr.opimm (AluOp.add) 13 0 0x00000001#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4685) (by decide +kernel) (by decide +kernel)
theorem f80020e0e : fetchDecode img 0x80020e0e = some (Instr.store (Width.b) 2 0 0x0000001a#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x10d23) (by decide +kernel) (by decide +kernel)
theorem f80020e12 : fetchDecode img 0x80020e12 = some (Instr.branch (BrCond.ne) 6 13 0x000000c0#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xcd31063) (by decide +kernel) (by decide +kernel)
theorem f80020e16 : fetchDecode img 0x80020e16 = some (Instr.opimm (AluOp.add) 15 0 0x00000000#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4781) (by decide +kernel) (by decide +kernel)
theorem f80020e18 : fetchDecode img 0x80020e18 = some (Instr.opimm (AluOp.add) 31 0 0x00000000#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4f81) (by decide +kernel) (by decide +kernel)
theorem f80020e1a : fetchDecode img 0x80020e1a = some (Instr.opimm (AluOp.add) 29 2 0x0000001c#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1c10e93) (by decide +kernel) (by decide +kernel)
theorem f80020e1e : fetchDecode img 0x80020e1e = some (Instr.jal 0 0x000001c0#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xa2c1) (by decide +kernel) (by decide +kernel)
theorem f80020e20 : fetchDecode img 0x80020e20 = some (Instr.opimm (AluOp.add) 13 0 0x00000010#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x46c1) (by decide +kernel) (by decide +kernel)
theorem f80020e22 : fetchDecode img 0x80020e22 = some (Instr.branch (BrCond.ltu) 12 13 0x00000070#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x6d66863) (by decide +kernel) (by decide +kernel)
theorem f80020e26 : fetchDecode img 0x80020e26 = some (Instr.op (AluOp.sub) 13 0 10, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x40a006b3) (by decide +kernel) (by decide +kernel)
theorem f80020e2a : fetchDecode img 0x80020e2a = some (Instr.opimm (AluOp.and) 16 13 0x00000003#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x36f813) (by decide +kernel) (by decide +kernel)
theorem f80020e2e : fetchDecode img 0x80020e2e = some (Instr.op (AluOp.add) 30 10 16, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1050f33) (by decide +kernel) (by decide +kernel)
theorem f80020e32 : fetchDecode img 0x80020e32 = some (Instr.branch (BrCond.geu) 10 30 0x0000001a#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1e57d63) (by decide +kernel) (by decide +kernel)
theorem f80020e36 : fetchDecode img 0x80020e36 = some (Instr.op (AluOp.add) 15 0 16, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x87c2) (by decide +kernel) (by decide +kernel)
theorem f80020e38 : fetchDecode img 0x80020e38 = some (Instr.op (AluOp.add) 13 0 10, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x86aa) (by decide +kernel) (by decide +kernel)
theorem f80020e3a : fetchDecode img 0x80020e3a = some (Instr.op (AluOp.add) 14 0 11, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x872e) (by decide +kernel) (by decide +kernel)
theorem f80020e3c : fetchDecode img 0x80020e3c = some (Instr.load (Width.b) false 9 14 0x00000000#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x74483) (by decide +kernel) (by decide +kernel)
theorem f80020e40 : fetchDecode img 0x80020e40 = some (Instr.opimm (AluOp.add) 15 15 0xffffffff#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x17fd) (by decide +kernel) (by decide +kernel)
theorem f80020e42 : fetchDecode img 0x80020e42 = some (Instr.store (Width.b) 13 9 0x00000000#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x968023) (by decide +kernel) (by decide +kernel)
theorem f80020e46 : fetchDecode img 0x80020e46 = some (Instr.opimm (AluOp.add) 13 13 0x00000001#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x685) (by decide +kernel) (by decide +kernel)
theorem f80020e48 : fetchDecode img 0x80020e48 = some (Instr.opimm (AluOp.add) 14 14 0x00000001#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x705) (by decide +kernel) (by decide +kernel)
theorem f80020e4a : fetchDecode img 0x80020e4a = some (Instr.branch (BrCond.ne) 15 0 0xfffffff2#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfbed) (by decide +kernel) (by decide +kernel)
theorem f80020e4c : fetchDecode img 0x80020e4c = some (Instr.op (AluOp.add) 5 11 16, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x10582b3) (by decide +kernel) (by decide +kernel)
theorem f80020e50 : fetchDecode img 0x80020e50 = some (Instr.op (AluOp.sub) 16 12 16, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x41060833) (by decide +kernel) (by decide +kernel)
theorem f80020e54 : fetchDecode img 0x80020e54 = some (Instr.opimm (AluOp.and) 17 16 0xfffffffc#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xffc87893) (by decide +kernel) (by decide +kernel)
theorem f80020e58 : fetchDecode img 0x80020e58 = some (Instr.opimm (AluOp.and) 6 5 0x00000003#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x32f313) (by decide +kernel) (by decide +kernel)
theorem f80020e5c : fetchDecode img 0x80020e5c = some (Instr.op (AluOp.add) 13 30 17, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x11f06b3) (by decide +kernel) (by decide +kernel)
theorem f80020e60 : fetchDecode img 0x80020e60 = some (Instr.branch (BrCond.eq) 6 0 0x0000005c#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4030e63) (by decide +kernel) (by decide +kernel)
theorem f80020e64 : fetchDecode img 0x80020e64 = some (Instr.opimm (AluOp.add) 11 0 0x00000000#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4581) (by decide +kernel) (by decide +kernel)
theorem f80020e66 : fetchDecode img 0x80020e66 = some (Instr.opimm (AluOp.add) 12 0 0x00000004#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4611) (by decide +kernel) (by decide +kernel)
theorem f80020e68 : fetchDecode img 0x80020e68 = some (Instr.store (Width.w) 2 0 0x00000014#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xca02) (by decide +kernel) (by decide +kernel)
theorem f80020e6a : fetchDecode img 0x80020e6a = some (Instr.op (AluOp.sub) 14 12 6, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x40660733) (by decide +kernel) (by decide +kernel)
theorem f80020e6e : fetchDecode img 0x80020e6e = some (Instr.opimm (AluOp.add) 12 2 0x00000014#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x850) (by decide +kernel) (by decide +kernel)
theorem f80020e70 : fetchDecode img 0x80020e70 = some (Instr.opimm (AluOp.and) 15 14 0x00000001#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x177793) (by decide +kernel) (by decide +kernel)
theorem f80020e74 : fetchDecode img 0x80020e74 = some (Instr.op (AluOp.or) 12 12 6, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x666633) (by decide +kernel) (by decide +kernel)
theorem f80020e78 : fetchDecode img 0x80020e78 = some (Instr.branch (BrCond.ne) 15 0 0x00000082#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xe3c9) (by decide +kernel) (by decide +kernel)
theorem f80020e7a : fetchDecode img 0x80020e7a = some (Instr.opimm (AluOp.and) 14 14 0x00000002#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8b09) (by decide +kernel) (by decide +kernel)
theorem f80020e7c : fetchDecode img 0x80020e7c = some (Instr.branch (BrCond.ne) 14 0 0x0000008c#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xe751) (by decide +kernel) (by decide +kernel)
theorem f80020e7e : fetchDecode img 0x80020e7e = some (Instr.load (Width.w) true 15 2 0x00000014#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x47d2) (by decide +kernel) (by decide +kernel)
theorem f80020e80 : fetchDecode img 0x80020e80 = some (Instr.opimm (AluOp.sll) 28 6 0x00000003#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x331e13) (by decide +kernel) (by decide +kernel)
theorem f80020e84 : fetchDecode img 0x80020e84 = some (Instr.opimm (AluOp.add) 12 30 0x00000004#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4f0613) (by decide +kernel) (by decide +kernel)
theorem f80020e88 : fetchDecode img 0x80020e88 = some (Instr.op (AluOp.sub) 11 5 6, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x406285b3) (by decide +kernel) (by decide +kernel)
theorem f80020e8c : fetchDecode img 0x80020e8c = some (Instr.branch (BrCond.ltu) 12 13 0x0000009c#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8d66e63) (by decide +kernel) (by decide +kernel)
theorem f80020e90 : fetchDecode img 0x80020e90 = some (Instr.jal 0 0x000000bc#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xa875) (by decide +kernel) (by decide +kernel)
theorem f80020e92 : fetchDecode img 0x80020e92 = some (Instr.op (AluOp.add) 13 0 10, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x86aa) (by decide +kernel) (by decide +kernel)
theorem f80020e94 : fetchDecode img 0x80020e94 = some (Instr.op (AluOp.add) 14 10 12, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc50733) (by decide +kernel) (by decide +kernel)
theorem f80020e98 : fetchDecode img 0x80020e98 = some (Instr.branch (BrCond.ltu) 10 14 0x0000012e#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x12e56763) (by decide +kernel) (by decide +kernel)
theorem f80020e9c : fetchDecode img 0x80020e9c = some (Instr.jal 0 0x00000214#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xac11) (by decide +kernel) (by decide +kernel)
theorem f80020e9e : fetchDecode img 0x80020e9e = some (Instr.branch (BrCond.geu) 28 7 0x000001ea#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1e7e7563) (by decide +kernel) (by decide +kernel)
theorem f80020ea2 : fetchDecode img 0x80020ea2 = some (Instr.op (AluOp.add) 11 11 17, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x95c6) (by decide +kernel) (by decide +kernel)
theorem f80020ea4 : fetchDecode img 0x80020ea4 = some (Instr.opimm (AluOp.add) 11 11 0xfffffffc#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x15f1) (by decide +kernel) (by decide +kernel)
theorem f80020ea6 : fetchDecode img 0x80020ea6 = some (Instr.op (AluOp.add) 12 0 7, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x861e) (by decide +kernel) (by decide +kernel)
theorem f80020ea8 : fetchDecode img 0x80020ea8 = some (Instr.load (Width.w) true 13 11 0x00000000#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4194) (by decide +kernel) (by decide +kernel)
theorem f80020eaa : fetchDecode img 0x80020eaa = some (Instr.opimm (AluOp.add) 14 12 0xfffffffc#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xffc60713) (by decide +kernel) (by decide +kernel)
theorem f80020eae : fetchDecode img 0x80020eae = some (Instr.store (Width.w) 12 13 0xfffffffc#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfed62e23) (by decide +kernel) (by decide +kernel)
theorem f80020eb2 : fetchDecode img 0x80020eb2 = some (Instr.opimm (AluOp.add) 11 11 0xfffffffc#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x15f1) (by decide +kernel) (by decide +kernel)
theorem f80020eb4 : fetchDecode img 0x80020eb4 = some (Instr.op (AluOp.add) 12 0 14, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x863a) (by decide +kernel) (by decide +kernel)
theorem f80020eb6 : fetchDecode img 0x80020eb6 = some (Instr.branch (BrCond.ltu) 28 14 0xfffffff2#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfeee69e3) (by decide +kernel) (by decide +kernel)
theorem f80020eba : fetchDecode img 0x80020eba = some (Instr.jal 0 0x000001ce#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xa2f9) (by decide +kernel) (by decide +kernel)
theorem f80020ebc : fetchDecode img 0x80020ebc = some (Instr.branch (BrCond.geu) 30 13 0x000000fa#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xedf7d63) (by decide +kernel) (by decide +kernel)
theorem f80020ec0 : fetchDecode img 0x80020ec0 = some (Instr.op (AluOp.add) 11 0 5, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8596) (by decide +kernel) (by decide +kernel)
theorem f80020ec2 : fetchDecode img 0x80020ec2 = some (Instr.load (Width.w) true 12 11 0x00000000#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4190) (by decide +kernel) (by decide +kernel)
theorem f80020ec4 : fetchDecode img 0x80020ec4 = some (Instr.store (Width.w) 30 12 0x00000000#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xcf2023) (by decide +kernel) (by decide +kernel)
theorem f80020ec8 : fetchDecode img 0x80020ec8 = some (Instr.opimm (AluOp.add) 30 30 0x00000004#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xf11) (by decide +kernel) (by decide +kernel)
theorem f80020eca : fetchDecode img 0x80020eca = some (Instr.opimm (AluOp.add) 11 11 0x00000004#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x591) (by decide +kernel) (by decide +kernel)
theorem f80020ecc : fetchDecode img 0x80020ecc = some (Instr.branch (BrCond.ltu) 30 13 0xfffffff6#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfedf6be3) (by decide +kernel) (by decide +kernel)
theorem f80020ed0 : fetchDecode img 0x80020ed0 = some (Instr.jal 0 0x000000e6#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xa0dd) (by decide +kernel) (by decide +kernel)
theorem f80020ed2 : fetchDecode img 0x80020ed2 = some (Instr.load (Width.b) false 15 30 0x00000000#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xf4783) (by decide +kernel) (by decide +kernel)
theorem f80020ed6 : fetchDecode img 0x80020ed6 = some (Instr.load (Width.b) false 31 30 0x00000001#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1f4f83) (by decide +kernel) (by decide +kernel)
theorem f80020eda : fetchDecode img 0x80020eda = some (Instr.opimm (AluOp.and) 13 5 0x00000001#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x12f693) (by decide +kernel) (by decide +kernel)
theorem f80020ede : fetchDecode img 0x80020ede = some (Instr.store (Width.b) 2 15 0x0000001c#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xf10e23) (by decide +kernel) (by decide +kernel)
theorem f80020ee2 : fetchDecode img 0x80020ee2 = some (Instr.branch (BrCond.ne) 13 0 0x000000f6#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xeafd) (by decide +kernel) (by decide +kernel)
theorem f80020ee4 : fetchDecode img 0x80020ee4 = some (Instr.opimm (AluOp.sll) 29 6 0x00000003#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x331e93) (by decide +kernel) (by decide +kernel)
theorem f80020ee8 : fetchDecode img 0x80020ee8 = some (Instr.opimm (AluOp.sll) 31 31 0x00000008#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfa2) (by decide +kernel) (by decide +kernel)
theorem f80020eea : fetchDecode img 0x80020eea = some (Instr.op (AluOp.add) 15 0 15, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x87be) (by decide +kernel) (by decide +kernel)
theorem f80020eec : fetchDecode img 0x80020eec = some (Instr.opimm (AluOp.add) 28 28 0x00000004#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xe11) (by decide +kernel) (by decide +kernel)
theorem f80020eee : fetchDecode img 0x80020eee = some (Instr.op (AluOp.or) 15 31 15, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xffe7b3) (by decide +kernel) (by decide +kernel)
theorem f80020ef2 : fetchDecode img 0x80020ef2 = some (Instr.branch (BrCond.ltu) 28 7 0x00000112#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x107e6963) (by decide +kernel) (by decide +kernel)
theorem f80020ef6 : fetchDecode img 0x80020ef6 = some (Instr.op (AluOp.add) 11 0 7, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x859e) (by decide +kernel) (by decide +kernel)
theorem f80020ef8 : fetchDecode img 0x80020ef8 = some (Instr.jal 0 0x00000144#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xa291) (by decide +kernel) (by decide +kernel)
theorem f80020efa : fetchDecode img 0x80020efa = some (Instr.load (Width.b) false 11 5 0x00000000#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2c583) (by decide +kernel) (by decide +kernel)
theorem f80020efe : fetchDecode img 0x80020efe = some (Instr.store (Width.b) 12 11 0x00000000#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xb60023) (by decide +kernel) (by decide +kernel)
theorem f80020f02 : fetchDecode img 0x80020f02 = some (Instr.opimm (AluOp.add) 11 0 0x00000001#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4585) (by decide +kernel) (by decide +kernel)
theorem f80020f04 : fetchDecode img 0x80020f04 = some (Instr.opimm (AluOp.and) 14 14 0x00000002#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8b09) (by decide +kernel) (by decide +kernel)
theorem f80020f06 : fetchDecode img 0x80020f06 = some (Instr.branch (BrCond.eq) 14 0 0xffffff78#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xdf25) (by decide +kernel) (by decide +kernel)
theorem f80020f08 : fetchDecode img 0x80020f08 = some (Instr.op (AluOp.add) 14 5 11, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xb28733) (by decide +kernel) (by decide +kernel)
theorem f80020f0c : fetchDecode img 0x80020f0c = some (Instr.load (Width.h) true 14 14 0x00000000#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x71703) (by decide +kernel) (by decide +kernel)
theorem f80020f10 : fetchDecode img 0x80020f10 = some (Instr.op (AluOp.add) 11 11 12, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x95b2) (by decide +kernel) (by decide +kernel)
theorem f80020f12 : fetchDecode img 0x80020f12 = some (Instr.store (Width.h) 11 14 0x00000000#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xe59023) (by decide +kernel) (by decide +kernel)
theorem f80020f16 : fetchDecode img 0x80020f16 = some (Instr.load (Width.w) true 15 2 0x00000014#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x47d2) (by decide +kernel) (by decide +kernel)
theorem f80020f18 : fetchDecode img 0x80020f18 = some (Instr.opimm (AluOp.sll) 28 6 0x00000003#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x331e13) (by decide +kernel) (by decide +kernel)
theorem f80020f1c : fetchDecode img 0x80020f1c = some (Instr.opimm (AluOp.add) 12 30 0x00000004#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4f0613) (by decide +kernel) (by decide +kernel)
theorem f80020f20 : fetchDecode img 0x80020f20 = some (Instr.op (AluOp.sub) 11 5 6, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x406285b3) (by decide +kernel) (by decide +kernel)
theorem f80020f24 : fetchDecode img 0x80020f24 = some (Instr.branch (BrCond.geu) 12 13 0x00000028#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2d67463) (by decide +kernel) (by decide +kernel)
theorem f80020f28 : fetchDecode img 0x80020f28 = some (Instr.op (AluOp.sub) 12 0 28, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x41c00633) (by decide +kernel) (by decide +kernel)
theorem f80020f2c : fetchDecode img 0x80020f2c = some (Instr.opimm (AluOp.and) 12 12 0x00000018#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8a61) (by decide +kernel) (by decide +kernel)
theorem f80020f2e : fetchDecode img 0x80020f2e = some (Instr.op (AluOp.add) 14 0 15, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x873e) (by decide +kernel) (by decide +kernel)
theorem f80020f30 : fetchDecode img 0x80020f30 = some (Instr.load (Width.w) true 15 11 0x00000004#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x41dc) (by decide +kernel) (by decide +kernel)
theorem f80020f32 : fetchDecode img 0x80020f32 = some (Instr.op (AluOp.srl) 14 14 28, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1c75733) (by decide +kernel) (by decide +kernel)
theorem f80020f36 : fetchDecode img 0x80020f36 = some (Instr.opimm (AluOp.add) 11 11 0x00000004#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x591) (by decide +kernel) (by decide +kernel)
theorem f80020f38 : fetchDecode img 0x80020f38 = some (Instr.op (AluOp.sll) 9 15 12, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc794b3) (by decide +kernel) (by decide +kernel)
theorem f80020f3c : fetchDecode img 0x80020f3c = some (Instr.op (AluOp.or) 14 14 9, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8f45) (by decide +kernel) (by decide +kernel)
theorem f80020f3e : fetchDecode img 0x80020f3e = some (Instr.opimm (AluOp.add) 9 30 0x00000008#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8f0493) (by decide +kernel) (by decide +kernel)
theorem f80020f42 : fetchDecode img 0x80020f42 = some (Instr.store (Width.w) 30 14 0x00000000#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xef2023) (by decide +kernel) (by decide +kernel)
theorem f80020f46 : fetchDecode img 0x80020f46 = some (Instr.opimm (AluOp.add) 30 30 0x00000004#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xf11) (by decide +kernel) (by decide +kernel)
theorem f80020f48 : fetchDecode img 0x80020f48 = some (Instr.branch (BrCond.ltu) 9 13 0xffffffe6#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfed4e3e3) (by decide +kernel) (by decide +kernel)
theorem f80020f4c : fetchDecode img 0x80020f4c = some (Instr.store (Width.b) 2 0 0x00000010#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x10823) (by decide +kernel) (by decide +kernel)
theorem f80020f50 : fetchDecode img 0x80020f50 = some (Instr.opimm (AluOp.add) 12 0 0x00000001#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4605) (by decide +kernel) (by decide +kernel)
theorem f80020f52 : fetchDecode img 0x80020f52 = some (Instr.store (Width.b) 2 0 0x0000000e#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x10723) (by decide +kernel) (by decide +kernel)
theorem f80020f56 : fetchDecode img 0x80020f56 = some (Instr.branch (BrCond.ne) 6 12 0x00000028#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2c31463) (by decide +kernel) (by decide +kernel)
theorem f80020f5a : fetchDecode img 0x80020f5a = some (Instr.opimm (AluOp.add) 6 0 0x00000000#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4301) (by decide +kernel) (by decide +kernel)
theorem f80020f5c : fetchDecode img 0x80020f5c = some (Instr.opimm (AluOp.add) 7 0 0x00000000#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4381) (by decide +kernel) (by decide +kernel)
theorem f80020f5e : fetchDecode img 0x80020f5e = some (Instr.opimm (AluOp.add) 29 0 0x00000000#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4e81) (by decide +kernel) (by decide +kernel)
theorem f80020f60 : fetchDecode img 0x80020f60 = some (Instr.opimm (AluOp.add) 12 2 0x00000010#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x810) (by decide +kernel) (by decide +kernel)
theorem f80020f62 : fetchDecode img 0x80020f62 = some (Instr.opimm (AluOp.and) 14 5 0x00000001#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x12f713) (by decide +kernel) (by decide +kernel)
theorem f80020f66 : fetchDecode img 0x80020f66 = some (Instr.branch (BrCond.eq) 14 0 0x00000032#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xcb0d) (by decide +kernel) (by decide +kernel)
theorem f80020f68 : fetchDecode img 0x80020f68 = some (Instr.op (AluOp.add) 11 11 29, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x95f6) (by decide +kernel) (by decide +kernel)
theorem f80020f6a : fetchDecode img 0x80020f6a = some (Instr.load (Width.b) false 11 11 0x00000004#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x45c583) (by decide +kernel) (by decide +kernel)
theorem f80020f6e : fetchDecode img 0x80020f6e = some (Instr.store (Width.b) 12 11 0x00000000#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xb60023) (by decide +kernel) (by decide +kernel)
theorem f80020f72 : fetchDecode img 0x80020f72 = some (Instr.load (Width.b) false 11 2 0x0000000e#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xe14583) (by decide +kernel) (by decide +kernel)
theorem f80020f76 : fetchDecode img 0x80020f76 = some (Instr.load (Width.b) false 6 2 0x00000010#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1014303) (by decide +kernel) (by decide +kernel)
theorem f80020f7a : fetchDecode img 0x80020f7a = some (Instr.opimm (AluOp.sll) 11 11 0x00000010#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x5c2) (by decide +kernel) (by decide +kernel)
theorem f80020f7c : fetchDecode img 0x80020f7c = some (Instr.jal 0 0x0000001e#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xa839) (by decide +kernel) (by decide +kernel)
theorem f80020f7e : fetchDecode img 0x80020f7e = some (Instr.load (Width.b) false 6 11 0x00000004#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x45c303) (by decide +kernel) (by decide +kernel)
theorem f80020f82 : fetchDecode img 0x80020f82 = some (Instr.load (Width.b) false 7 11 0x00000005#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x55c383) (by decide +kernel) (by decide +kernel)
theorem f80020f86 : fetchDecode img 0x80020f86 = some (Instr.opimm (AluOp.add) 29 0 0x00000002#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4e89) (by decide +kernel) (by decide +kernel)
theorem f80020f88 : fetchDecode img 0x80020f88 = some (Instr.store (Width.b) 2 6 0x00000010#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x610823) (by decide +kernel) (by decide +kernel)
theorem f80020f8c : fetchDecode img 0x80020f8c = some (Instr.opimm (AluOp.sll) 7 7 0x00000008#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x3a2) (by decide +kernel) (by decide +kernel)
theorem f80020f8e : fetchDecode img 0x80020f8e = some (Instr.opimm (AluOp.add) 12 2 0x0000000e#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xe10613) (by decide +kernel) (by decide +kernel)
theorem f80020f92 : fetchDecode img 0x80020f92 = some (Instr.opimm (AluOp.and) 14 5 0x00000001#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x12f713) (by decide +kernel) (by decide +kernel)
theorem f80020f96 : fetchDecode img 0x80020f96 = some (Instr.branch (BrCond.ne) 14 0 0xffffffd2#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfb69) (by decide +kernel) (by decide +kernel)
theorem f80020f98 : fetchDecode img 0x80020f98 = some (Instr.opimm (AluOp.add) 11 0 0x00000000#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4581) (by decide +kernel) (by decide +kernel)
theorem f80020f9a : fetchDecode img 0x80020f9a = some (Instr.op (AluOp.or) 11 7 11, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xb3e5b3) (by decide +kernel) (by decide +kernel)
theorem f80020f9e : fetchDecode img 0x80020f9e = some (Instr.op (AluOp.srl) 12 15 28, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1c7d633) (by decide +kernel) (by decide +kernel)
theorem f80020fa2 : fetchDecode img 0x80020fa2 = some (Instr.op (AluOp.sub) 14 0 28, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x41c00733) (by decide +kernel) (by decide +kernel)
theorem f80020fa6 : fetchDecode img 0x80020fa6 = some (Instr.op (AluOp.or) 11 11 6, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x65e5b3) (by decide +kernel) (by decide +kernel)
theorem f80020faa : fetchDecode img 0x80020faa = some (Instr.opimm (AluOp.and) 14 14 0x00000018#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8b61) (by decide +kernel) (by decide +kernel)
theorem f80020fac : fetchDecode img 0x80020fac = some (Instr.op (AluOp.sll) 11 11 14, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xe595b3) (by decide +kernel) (by decide +kernel)
theorem f80020fb0 : fetchDecode img 0x80020fb0 = some (Instr.op (AluOp.or) 11 11 12, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8dd1) (by decide +kernel) (by decide +kernel)
theorem f80020fb2 : fetchDecode img 0x80020fb2 = some (Instr.store (Width.w) 30 11 0x00000000#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xbf2023) (by decide +kernel) (by decide +kernel)
theorem f80020fb6 : fetchDecode img 0x80020fb6 = some (Instr.op (AluOp.add) 11 5 17, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x11285b3) (by decide +kernel) (by decide +kernel)
theorem f80020fba : fetchDecode img 0x80020fba = some (Instr.opimm (AluOp.and) 12 16 0x00000003#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x387613) (by decide +kernel) (by decide +kernel)
theorem f80020fbe : fetchDecode img 0x80020fbe = some (Instr.op (AluOp.add) 14 13 12, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc68733) (by decide +kernel) (by decide +kernel)
theorem f80020fc2 : fetchDecode img 0x80020fc2 = some (Instr.branch (BrCond.geu) 13 14 0x000000ee#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xee6f763) (by decide +kernel) (by decide +kernel)
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
theorem f80020fd8 : fetchDecode img 0x80020fd8 = some (Instr.opimm (AluOp.add) 29 2 0x0000001a#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1a10e93) (by decide +kernel) (by decide +kernel)
theorem f80020fdc : fetchDecode img 0x80020fdc = some (Instr.opimm (AluOp.add) 15 0 0x00000002#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4789) (by decide +kernel) (by decide +kernel)
theorem f80020fde : fetchDecode img 0x80020fde = some (Instr.op (AluOp.add) 15 15 30, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x97fa) (by decide +kernel) (by decide +kernel)
theorem f80020fe0 : fetchDecode img 0x80020fe0 = some (Instr.load (Width.b) false 13 15 0x00000000#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x7c683) (by decide +kernel) (by decide +kernel)
theorem f80020fe4 : fetchDecode img 0x80020fe4 = some (Instr.store (Width.b) 29 13 0x00000000#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xde8023) (by decide +kernel) (by decide +kernel)
theorem f80020fe8 : fetchDecode img 0x80020fe8 = some (Instr.load (Width.b) false 8 2 0x0000001a#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1a14403) (by decide +kernel) (by decide +kernel)
theorem f80020fec : fetchDecode img 0x80020fec = some (Instr.load (Width.b) false 15 2 0x0000001c#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1c14783) (by decide +kernel) (by decide +kernel)
theorem f80020ff0 : fetchDecode img 0x80020ff0 = some (Instr.opimm (AluOp.sll) 8 8 0x00000010#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x442) (by decide +kernel) (by decide +kernel)
theorem f80020ff2 : fetchDecode img 0x80020ff2 = some (Instr.opimm (AluOp.sll) 29 6 0x00000003#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x331e93) (by decide +kernel) (by decide +kernel)
theorem f80020ff6 : fetchDecode img 0x80020ff6 = some (Instr.opimm (AluOp.sll) 31 31 0x00000008#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfa2) (by decide +kernel) (by decide +kernel)
theorem f80020ff8 : fetchDecode img 0x80020ff8 = some (Instr.op (AluOp.or) 15 15 8, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8fc1) (by decide +kernel) (by decide +kernel)
theorem f80020ffa : fetchDecode img 0x80020ffa = some (Instr.opimm (AluOp.add) 28 28 0x00000004#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xe11) (by decide +kernel) (by decide +kernel)
theorem f80020ffc : fetchDecode img 0x80020ffc = some (Instr.op (AluOp.or) 15 31 15, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xffe7b3) (by decide +kernel) (by decide +kernel)
theorem f80021000 : fetchDecode img 0x80021000 = some (Instr.branch (BrCond.geu) 28 7 0xfffffef6#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xee7e7be3) (by decide +kernel) (by decide +kernel)
theorem f80021004 : fetchDecode img 0x80021004 = some (Instr.op (AluOp.sub) 13 0 29, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x41d006b3) (by decide +kernel) (by decide +kernel)
theorem f80021008 : fetchDecode img 0x80021008 = some (Instr.op (AluOp.sub) 30 12 6, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x40660f33) (by decide +kernel) (by decide +kernel)
theorem f8002100c : fetchDecode img 0x8002100c = some (Instr.opimm (AluOp.and) 12 13 0x00000018#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x186f613) (by decide +kernel) (by decide +kernel)
theorem f80021010 : fetchDecode img 0x80021010 = some (Instr.op (AluOp.add) 30 30 11, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x9f2e) (by decide +kernel) (by decide +kernel)
theorem f80021012 : fetchDecode img 0x80021012 = some (Instr.op (AluOp.add) 11 0 15, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x85be) (by decide +kernel) (by decide +kernel)
theorem f80021014 : fetchDecode img 0x80021014 = some (Instr.op (AluOp.add) 13 30 18, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x12f06b3) (by decide +kernel) (by decide +kernel)
theorem f80021018 : fetchDecode img 0x80021018 = some (Instr.load (Width.w) true 15 13 0xfffffffc#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xffc6a783) (by decide +kernel) (by decide +kernel)
theorem f8002101c : fetchDecode img 0x8002101c = some (Instr.op (AluOp.sll) 11 11 12, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc595b3) (by decide +kernel) (by decide +kernel)
theorem f80021020 : fetchDecode img 0x80021020 = some (Instr.op (AluOp.srl) 13 15 29, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1d7d6b3) (by decide +kernel) (by decide +kernel)
theorem f80021024 : fetchDecode img 0x80021024 = some (Instr.op (AluOp.or) 11 11 13, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8dd5) (by decide +kernel) (by decide +kernel)
theorem f80021026 : fetchDecode img 0x80021026 = some (Instr.op (AluOp.add) 13 9 18, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x12486b3) (by decide +kernel) (by decide +kernel)
theorem f8002102a : fetchDecode img 0x8002102a = some (Instr.opimm (AluOp.add) 9 9 0xfffffffc#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x14f1) (by decide +kernel) (by decide +kernel)
theorem f8002102c : fetchDecode img 0x8002102c = some (Instr.store (Width.w) 13 11 0xfffffffc#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfeb6ae23) (by decide +kernel) (by decide +kernel)
theorem f80021030 : fetchDecode img 0x80021030 = some (Instr.op (AluOp.add) 11 9 18, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x12485b3) (by decide +kernel) (by decide +kernel)
theorem f80021034 : fetchDecode img 0x80021034 = some (Instr.opimm (AluOp.add) 30 30 0xfffffffc#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1f71) (by decide +kernel) (by decide +kernel)
theorem f80021036 : fetchDecode img 0x80021036 = some (Instr.branch (BrCond.ltu) 28 11 0xffffffdc#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfcbe6ee3) (by decide +kernel) (by decide +kernel)
theorem f8002103a : fetchDecode img 0x8002103a = some (Instr.op (AluOp.add) 30 30 18, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x9f4a) (by decide +kernel) (by decide +kernel)
theorem f8002103c : fetchDecode img 0x8002103c = some (Instr.opimm (AluOp.add) 12 0 0x00000000#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4601) (by decide +kernel) (by decide +kernel)
theorem f8002103e : fetchDecode img 0x8002103e = some (Instr.op (AluOp.add) 14 30 6, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x6f0733) (by decide +kernel) (by decide +kernel)
theorem f80021042 : fetchDecode img 0x80021042 = some (Instr.opimm (AluOp.add) 13 0 0x00000004#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4691) (by decide +kernel) (by decide +kernel)
theorem f80021044 : fetchDecode img 0x80021044 = some (Instr.store (Width.w) 2 0 0x00000020#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xd002) (by decide +kernel) (by decide +kernel)
theorem f80021046 : fetchDecode img 0x80021046 = some (Instr.opimm (AluOp.add) 9 2 0x00000020#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1004) (by decide +kernel) (by decide +kernel)
theorem f80021048 : fetchDecode img 0x80021048 = some (Instr.op (AluOp.sub) 13 13 6, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x406686b3) (by decide +kernel) (by decide +kernel)
theorem f8002104c : fetchDecode img 0x8002104c = some (Instr.op (AluOp.or) 6 9 6, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x64e333) (by decide +kernel) (by decide +kernel)
theorem f80021050 : fetchDecode img 0x80021050 = some (Instr.opimm (AluOp.and) 9 13 0x00000001#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x16f493) (by decide +kernel) (by decide +kernel)
theorem f80021054 : fetchDecode img 0x80021054 = some (Instr.opimm (AluOp.add) 14 14 0xfffffffc#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1771) (by decide +kernel) (by decide +kernel)
theorem f80021056 : fetchDecode img 0x80021056 = some (Instr.branch (BrCond.eq) 9 0 0x0000000c#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc491) (by decide +kernel) (by decide +kernel)
theorem f80021058 : fetchDecode img 0x80021058 = some (Instr.load (Width.b) false 12 14 0x00000000#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x74603) (by decide +kernel) (by decide +kernel)
theorem f8002105c : fetchDecode img 0x8002105c = some (Instr.store (Width.b) 6 12 0x00000000#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc30023) (by decide +kernel) (by decide +kernel)
theorem f80021060 : fetchDecode img 0x80021060 = some (Instr.opimm (AluOp.add) 12 0 0x00000001#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4605) (by decide +kernel) (by decide +kernel)
theorem f80021062 : fetchDecode img 0x80021062 = some (Instr.opimm (AluOp.and) 13 13 0x00000002#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8a89) (by decide +kernel) (by decide +kernel)
theorem f80021064 : fetchDecode img 0x80021064 = some (Instr.branch (BrCond.eq) 13 0 0x0000000e#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc699) (by decide +kernel) (by decide +kernel)
theorem f80021066 : fetchDecode img 0x80021066 = some (Instr.op (AluOp.add) 14 14 12, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x9732) (by decide +kernel) (by decide +kernel)
theorem f80021068 : fetchDecode img 0x80021068 = some (Instr.load (Width.h) true 13 14 0x00000000#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x71683) (by decide +kernel) (by decide +kernel)
theorem f8002106c : fetchDecode img 0x8002106c = some (Instr.op (AluOp.add) 12 12 6, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x961a) (by decide +kernel) (by decide +kernel)
theorem f8002106e : fetchDecode img 0x8002106e = some (Instr.store (Width.h) 12 13 0x00000000#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xd61023) (by decide +kernel) (by decide +kernel)
theorem f80021072 : fetchDecode img 0x80021072 = some (Instr.load (Width.w) true 12 2 0x00000020#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x5602) (by decide +kernel) (by decide +kernel)
theorem f80021074 : fetchDecode img 0x80021074 = some (Instr.op (AluOp.sub) 13 0 29, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x41d006b3) (by decide +kernel) (by decide +kernel)
theorem f80021078 : fetchDecode img 0x80021078 = some (Instr.opimm (AluOp.and) 13 13 0x00000018#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8ae1) (by decide +kernel) (by decide +kernel)
theorem f8002107a : fetchDecode img 0x8002107a = some (Instr.op (AluOp.sll) 13 15 13, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xd796b3) (by decide +kernel) (by decide +kernel)
theorem f8002107e : fetchDecode img 0x8002107e = some (Instr.op (AluOp.srl) 12 12 29, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1d65633) (by decide +kernel) (by decide +kernel)
theorem f80021082 : fetchDecode img 0x80021082 = some (Instr.op (AluOp.or) 12 12 13, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8e55) (by decide +kernel) (by decide +kernel)
theorem f80021084 : fetchDecode img 0x80021084 = some (Instr.store (Width.w) 11 12 0xfffffffc#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfec5ae23) (by decide +kernel) (by decide +kernel)
theorem f80021088 : fetchDecode img 0x80021088 = some (Instr.op (AluOp.add) 9 7 16, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x10384b3) (by decide +kernel) (by decide +kernel)
theorem f8002108c : fetchDecode img 0x8002108c = some (Instr.op (AluOp.add) 16 16 5, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x9816) (by decide +kernel) (by decide +kernel)
theorem f8002108e : fetchDecode img 0x8002108e = some (Instr.opimm (AluOp.and) 12 17 0x00000003#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x38f613) (by decide +kernel) (by decide +kernel)
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
