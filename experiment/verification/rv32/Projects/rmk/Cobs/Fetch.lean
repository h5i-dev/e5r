/-
  Instruction facts for `cobs::dec::decode_in_place` (0x8001e006..0x8001e02e, 18 instructions)
  and `cobs::dec::decode_in_place_report` (0x8001e02e..0x8001e148, 97 instructions) in the
  pinned RMK image (ELF sha256 f39d833f...). Proposed by Projects/rmk/Cobs/GenFetch.lean from
  the model's own decoder and checked here by the kernel against the packed ELF
  (Projects/rmk/Fetch.lean `fetchDecode_of`).

  Original e5r code, Apache-2.0. Regenerate rather than edit by hand.
-/
import Projects.rmk.Fetch

set_option maxRecDepth 100000

namespace E5R.Rmk.CobsFetch
open E5R E5R.Rmk

theorem f8001e006 : fetchDecode img 0x8001e006 = some (Instr.opimm (AluOp.add) 2 2 0xffffffe0#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 4353) (by decide +kernel) (by decide +kernel)
theorem f8001e008 : fetchDecode img 0x8001e008 = some (Instr.store (Width.w) 2 1 0x0000001c#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 52742) (by decide +kernel) (by decide +kernel)
theorem f8001e00a : fetchDecode img 0x8001e00a = some (Instr.store (Width.w) 2 8 0x00000018#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 52258) (by decide +kernel) (by decide +kernel)
theorem f8001e00c : fetchDecode img 0x8001e00c = some (Instr.op (AluOp.add) 8 0 10, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 33834) (by decide +kernel) (by decide +kernel)
theorem f8001e00e : fetchDecode img 0x8001e00e = some (Instr.opimm (AluOp.add) 10 2 0x0000000c#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 104) (by decide +kernel) (by decide +kernel)
theorem f8001e010 : fetchDecode img 0x8001e010 = some (Instr.auipc 1 0x00000000#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 151) (by decide +kernel) (by decide +kernel)
theorem f8001e014 : fetchDecode img 0x8001e014 = some (Instr.jalr 1 1 0x0000001e#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 31490279) (by decide +kernel) (by decide +kernel)
theorem f8001e018 : fetchDecode img 0x8001e018 = some (Instr.load (Width.w) true 10 2 0x0000000c#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 17714) (by decide +kernel) (by decide +kernel)
theorem f8001e01a : fetchDecode img 0x8001e01a = some (Instr.load (Width.w) true 11 2 0x00000010#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 17858) (by decide +kernel) (by decide +kernel)
theorem f8001e01c : fetchDecode img 0x8001e01c = some (Instr.load (Width.w) true 12 2 0x00000014#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 18002) (by decide +kernel) (by decide +kernel)
theorem f8001e01e : fetchDecode img 0x8001e01e = some (Instr.opimm (AluOp.add) 10 10 0xffffffff#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 5501) (by decide +kernel) (by decide +kernel)
theorem f8001e020 : fetchDecode img 0x8001e020 = some (Instr.op (AluOp.or) 10 10 11, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 36173) (by decide +kernel) (by decide +kernel)
theorem f8001e022 : fetchDecode img 0x8001e022 = some (Instr.store (Width.w) 8 10 0x00000000#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 49160) (by decide +kernel) (by decide +kernel)
theorem f8001e024 : fetchDecode img 0x8001e024 = some (Instr.store (Width.w) 8 12 0x00000004#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 49232) (by decide +kernel) (by decide +kernel)
theorem f8001e026 : fetchDecode img 0x8001e026 = some (Instr.load (Width.w) true 1 2 0x0000001c#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 16626) (by decide +kernel) (by decide +kernel)
theorem f8001e028 : fetchDecode img 0x8001e028 = some (Instr.load (Width.w) true 8 2 0x00000018#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 17506) (by decide +kernel) (by decide +kernel)
theorem f8001e02a : fetchDecode img 0x8001e02a = some (Instr.opimm (AluOp.add) 2 2 0x00000020#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 24837) (by decide +kernel) (by decide +kernel)
theorem f8001e02c : fetchDecode img 0x8001e02c = some (Instr.jalr 0 1 0x00000000#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 32898) (by decide +kernel) (by decide +kernel)
theorem f8001e02e : fetchDecode img 0x8001e02e = some (Instr.opimm (AluOp.add) 2 2 0xfffffff0#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 4417) (by decide +kernel) (by decide +kernel)
theorem f8001e030 : fetchDecode img 0x8001e030 = some (Instr.store (Width.w) 2 8 0x0000000c#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 50722) (by decide +kernel) (by decide +kernel)
theorem f8001e032 : fetchDecode img 0x8001e032 = some (Instr.store (Width.w) 2 9 0x00000008#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 50214) (by decide +kernel) (by decide +kernel)
theorem f8001e034 : fetchDecode img 0x8001e034 = some (Instr.store (Width.w) 2 18 0x00000004#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 49738) (by decide +kernel) (by decide +kernel)
theorem f8001e036 : fetchDecode img 0x8001e036 = some (Instr.store (Width.w) 2 19 0x00000000#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 49230) (by decide +kernel) (by decide +kernel)
theorem f8001e038 : fetchDecode img 0x8001e038 = some (Instr.opimm (AluOp.add) 16 0 0x00000004#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 18449) (by decide +kernel) (by decide +kernel)
theorem f8001e03a : fetchDecode img 0x8001e03a = some (Instr.branch (BrCond.eq) 12 0 0x000000be#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 52829) (by decide +kernel) (by decide +kernel)
theorem f8001e03c : fetchDecode img 0x8001e03c = some (Instr.opimm (AluOp.add) 14 0 0x00000000#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 18177) (by decide +kernel) (by decide +kernel)
theorem f8001e03e : fetchDecode img 0x8001e03e = some (Instr.op (AluOp.add) 13 11 14, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 15042227) (by decide +kernel) (by decide +kernel)
theorem f8001e042 : fetchDecode img 0x8001e042 = some (Instr.load (Width.b) false 13 13 0x00000000#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 444035) (by decide +kernel) (by decide +kernel)
theorem f8001e046 : fetchDecode img 0x8001e046 = some (Instr.branch (BrCond.eq) 13 0 0x0000000a#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 50825) (by decide +kernel) (by decide +kernel)
theorem f8001e048 : fetchDecode img 0x8001e048 = some (Instr.opimm (AluOp.add) 14 14 0x00000001#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 1797) (by decide +kernel) (by decide +kernel)
theorem f8001e04a : fetchDecode img 0x8001e04a = some (Instr.branch (BrCond.ne) 12 14 0xfffffff4#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 4276493027) (by decide +kernel) (by decide +kernel)
theorem f8001e04e : fetchDecode img 0x8001e04e = some (Instr.op (AluOp.add) 14 0 12, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 34610) (by decide +kernel) (by decide +kernel)
theorem f8001e050 : fetchDecode img 0x8001e050 = some (Instr.opimm (AluOp.add) 29 0 0x00000000#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 20097) (by decide +kernel) (by decide +kernel)
theorem f8001e052 : fetchDecode img 0x8001e052 = some (Instr.opimm (AluOp.add) 7 0 0x00000000#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 17281) (by decide +kernel) (by decide +kernel)
theorem f8001e054 : fetchDecode img 0x8001e054 = some (Instr.branch (BrCond.eq) 14 0 0x0000009a#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 53065) (by decide +kernel) (by decide +kernel)
theorem f8001e056 : fetchDecode img 0x8001e056 = some (Instr.opimm (AluOp.add) 13 0 0x00000001#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 18053) (by decide +kernel) (by decide +kernel)
theorem f8001e058 : fetchDecode img 0x8001e058 = some (Instr.opimm (AluOp.add) 17 0 0x00000002#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 18569) (by decide +kernel) (by decide +kernel)
theorem f8001e05a : fetchDecode img 0x8001e05a = some (Instr.op (AluOp.sub) 5 13 12, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 1086751411) (by decide +kernel) (by decide +kernel)
theorem f8001e05e : fetchDecode img 0x8001e05e = some (Instr.opimm (AluOp.add) 6 0 0x000000ff#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 267387667) (by decide +kernel) (by decide +kernel)
theorem f8001e062 : fetchDecode img 0x8001e062 = some (Instr.jal 0 0x00000006#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 40985) (by decide +kernel) (by decide +kernel)
theorem f8001e064 : fetchDecode img 0x8001e064 = some (Instr.branch (BrCond.geu) 29 14 0x0000008a#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 149878115) (by decide +kernel) (by decide +kernel)
theorem f8001e068 : fetchDecode img 0x8001e068 = some (Instr.branch (BrCond.geu) 29 12 0x000000ca#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 214889827) (by decide +kernel) (by decide +kernel)
theorem f8001e06c : fetchDecode img 0x8001e06c = some (Instr.op (AluOp.add) 19 11 29, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 30771635) (by decide +kernel) (by decide +kernel)
theorem f8001e070 : fetchDecode img 0x8001e070 = some (Instr.load (Width.b) false 28 19 0x00000000#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 642563) (by decide +kernel) (by decide +kernel)
theorem f8001e074 : fetchDecode img 0x8001e074 = some (Instr.op (AluOp.add) 15 29 28, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 30312371) (by decide +kernel) (by decide +kernel)
theorem f8001e078 : fetchDecode img 0x8001e078 = some (Instr.branch (BrCond.ltu) 14 15 0x0000009e#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 150433635) (by decide +kernel) (by decide +kernel)
theorem f8001e07c : fetchDecode img 0x8001e07c = some (Instr.branch (BrCond.ltu) 28 17 0x00000056#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 85879651) (by decide +kernel) (by decide +kernel)
theorem f8001e080 : fetchDecode img 0x8001e080 = some (Instr.opimm (AluOp.add) 13 0 0x00000000#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 18049) (by decide +kernel) (by decide +kernel)
theorem f8001e082 : fetchDecode img 0x8001e082 = some (Instr.op (AluOp.sub) 31 12 7, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 1081479091) (by decide +kernel) (by decide +kernel)
theorem f8001e086 : fetchDecode img 0x8001e086 = some (Instr.op (AluOp.add) 30 5 29, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 30576435) (by decide +kernel) (by decide +kernel)
theorem f8001e08a : fetchDecode img 0x8001e08a = some (Instr.op (AluOp.sltu) 8 12 31, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 32912435) (by decide +kernel) (by decide +kernel)
theorem f8001e08e : fetchDecode img 0x8001e08e = some (Instr.opimm (AluOp.add) 8 8 0xffffffff#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 5245) (by decide +kernel) (by decide +kernel)
theorem f8001e090 : fetchDecode img 0x8001e090 = some (Instr.op (AluOp.and) 31 8 31, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 32800691) (by decide +kernel) (by decide +kernel)
theorem f8001e094 : fetchDecode img 0x8001e094 = some (Instr.op (AluOp.add) 18 11 7, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 7702835) (by decide +kernel) (by decide +kernel)
theorem f8001e098 : fetchDecode img 0x8001e098 = some (Instr.opimm (AluOp.and) 8 15 0x000000ff#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 267908115) (by decide +kernel) (by decide +kernel)
theorem f8001e09c : fetchDecode img 0x8001e09c = some (Instr.op (AluOp.add) 15 30 13, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 14616499) (by decide +kernel) (by decide +kernel)
theorem f8001e0a0 : fetchDecode img 0x8001e0a0 = some (Instr.branch (BrCond.eq) 15 0 0x0000007c#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 53173) (by decide +kernel) (by decide +kernel)
theorem f8001e0a2 : fetchDecode img 0x8001e0a2 = some (Instr.branch (BrCond.eq) 31 13 0x0000005c#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 81759843) (by decide +kernel) (by decide +kernel)
theorem f8001e0a6 : fetchDecode img 0x8001e0a6 = some (Instr.op (AluOp.add) 15 19 13, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 14256051) (by decide +kernel) (by decide +kernel)
theorem f8001e0aa : fetchDecode img 0x8001e0aa = some (Instr.load (Width.b) false 15 15 0x00000001#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 1558403) (by decide +kernel) (by decide +kernel)
theorem f8001e0ae : fetchDecode img 0x8001e0ae = some (Instr.op (AluOp.add) 9 18 13, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 14222515) (by decide +kernel) (by decide +kernel)
theorem f8001e0b2 : fetchDecode img 0x8001e0b2 = some (Instr.store (Width.b) 9 15 0x00000000#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 16023587) (by decide +kernel) (by decide +kernel)
theorem f8001e0b6 : fetchDecode img 0x8001e0b6 = some (Instr.op (AluOp.add) 15 29 13, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 14583731) (by decide +kernel) (by decide +kernel)
theorem f8001e0ba : fetchDecode img 0x8001e0ba = some (Instr.opimm (AluOp.add) 15 15 0x00000002#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 1929) (by decide +kernel) (by decide +kernel)
theorem f8001e0bc : fetchDecode img 0x8001e0bc = some (Instr.opimm (AluOp.and) 15 15 0x000000ff#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 267909011) (by decide +kernel) (by decide +kernel)
theorem f8001e0c0 : fetchDecode img 0x8001e0c0 = some (Instr.opimm (AluOp.add) 13 13 0x00000001#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 1669) (by decide +kernel) (by decide +kernel)
theorem f8001e0c2 : fetchDecode img 0x8001e0c2 = some (Instr.branch (BrCond.ne) 8 15 0xffffffda#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 4243856867) (by decide +kernel) (by decide +kernel)
theorem f8001e0c6 : fetchDecode img 0x8001e0c6 = some (Instr.op (AluOp.add) 29 29 13, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 40630) (by decide +kernel) (by decide +kernel)
theorem f8001e0c8 : fetchDecode img 0x8001e0c8 = some (Instr.opimm (AluOp.add) 29 29 0x00000001#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 3717) (by decide +kernel) (by decide +kernel)
theorem f8001e0ca : fetchDecode img 0x8001e0ca = some (Instr.op (AluOp.add) 7 7 13, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 37814) (by decide +kernel) (by decide +kernel)
theorem f8001e0cc : fetchDecode img 0x8001e0cc = some (Instr.branch (BrCond.ne) 28 6 0x0000000c#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 7214691) (by decide +kernel) (by decide +kernel)
theorem f8001e0d0 : fetchDecode img 0x8001e0d0 = some (Instr.jal 0 0xffffff94#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 48977) (by decide +kernel) (by decide +kernel)
theorem f8001e0d2 : fetchDecode img 0x8001e0d2 = some (Instr.opimm (AluOp.add) 29 29 0x00000001#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 3717) (by decide +kernel) (by decide +kernel)
theorem f8001e0d4 : fetchDecode img 0x8001e0d4 = some (Instr.branch (BrCond.eq) 28 6 0xffffff90#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 4167960803) (by decide +kernel) (by decide +kernel)
theorem f8001e0d8 : fetchDecode img 0x8001e0d8 = some (Instr.branch (BrCond.geu) 29 14 0xffffff8c#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 4176410339) (by decide +kernel) (by decide +kernel)
theorem f8001e0dc : fetchDecode img 0x8001e0dc = some (Instr.branch (BrCond.geu) 7 12 0x00000022#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 46395747) (by decide +kernel) (by decide +kernel)
theorem f8001e0e0 : fetchDecode img 0x8001e0e0 = some (Instr.op (AluOp.add) 13 11 7, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 7702195) (by decide +kernel) (by decide +kernel)
theorem f8001e0e4 : fetchDecode img 0x8001e0e4 = some (Instr.store (Width.b) 13 0 0x00000000#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 426019) (by decide +kernel) (by decide +kernel)
theorem f8001e0e8 : fetchDecode img 0x8001e0e8 = some (Instr.opimm (AluOp.add) 7 7 0x00000001#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 901) (by decide +kernel) (by decide +kernel)
theorem f8001e0ea : fetchDecode img 0x8001e0ea = some (Instr.branch (BrCond.ltu) 29 14 0xffffff7e#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 4142854115) (by decide +kernel) (by decide +kernel)
theorem f8001e0ee : fetchDecode img 0x8001e0ee = some (Instr.opimm (AluOp.add) 11 0 0x00000000#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 17793) (by decide +kernel) (by decide +kernel)
theorem f8001e0f0 : fetchDecode img 0x8001e0f0 = some (Instr.store (Width.w) 10 29 0x00000004#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 30745123) (by decide +kernel) (by decide +kernel)
theorem f8001e0f4 : fetchDecode img 0x8001e0f4 = some (Instr.opimm (AluOp.add) 16 0 0x00000008#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 18465) (by decide +kernel) (by decide +kernel)
theorem f8001e0f6 : fetchDecode img 0x8001e0f6 = some (Instr.jal 0 0x0000000c#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 41009) (by decide +kernel) (by decide +kernel)
theorem f8001e0f8 : fetchDecode img 0x8001e0f8 = some (Instr.opimm (AluOp.add) 7 0 0x00000000#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 17281) (by decide +kernel) (by decide +kernel)
theorem f8001e0fa : fetchDecode img 0x8001e0fa = some (Instr.opimm (AluOp.add) 11 0 0x00000001#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 17797) (by decide +kernel) (by decide +kernel)
theorem f8001e0fc : fetchDecode img 0x8001e0fc = some (Instr.jal 0 0x00000006#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 40985) (by decide +kernel) (by decide +kernel)
theorem f8001e0fe : fetchDecode img 0x8001e0fe = some (Instr.opimm (AluOp.add) 11 0 0x00000001#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 17797) (by decide +kernel) (by decide +kernel)
theorem f8001e100 : fetchDecode img 0x8001e100 = some (Instr.opimm (AluOp.add) 7 0 0x00000002#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 17289) (by decide +kernel) (by decide +kernel)
theorem f8001e102 : fetchDecode img 0x8001e102 = some (Instr.op (AluOp.add) 16 16 10, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 38954) (by decide +kernel) (by decide +kernel)
theorem f8001e104 : fetchDecode img 0x8001e104 = some (Instr.store (Width.w) 16 7 0x00000000#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 7872547) (by decide +kernel) (by decide +kernel)
theorem f8001e108 : fetchDecode img 0x8001e108 = some (Instr.store (Width.w) 10 11 0x00000000#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 49420) (by decide +kernel) (by decide +kernel)
theorem f8001e10a : fetchDecode img 0x8001e10a = some (Instr.load (Width.w) true 8 2 0x0000000c#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 17458) (by decide +kernel) (by decide +kernel)
theorem f8001e10c : fetchDecode img 0x8001e10c = some (Instr.load (Width.w) true 9 2 0x00000008#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 17570) (by decide +kernel) (by decide +kernel)
theorem f8001e10e : fetchDecode img 0x8001e10e = some (Instr.load (Width.w) true 18 2 0x00000004#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 18706) (by decide +kernel) (by decide +kernel)
theorem f8001e110 : fetchDecode img 0x8001e110 = some (Instr.load (Width.w) true 19 2 0x00000000#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 18818) (by decide +kernel) (by decide +kernel)
theorem f8001e112 : fetchDecode img 0x8001e112 = some (Instr.opimm (AluOp.add) 2 2 0x00000010#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 321) (by decide +kernel) (by decide +kernel)
theorem f8001e114 : fetchDecode img 0x8001e114 = some (Instr.jalr 0 1 0x00000000#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 32898) (by decide +kernel) (by decide +kernel)
theorem f8001e116 : fetchDecode img 0x8001e116 = some (Instr.opimm (AluOp.add) 29 0 0x00000001#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 20101) (by decide +kernel) (by decide +kernel)
theorem f8001e118 : fetchDecode img 0x8001e118 = some (Instr.opimm (AluOp.add) 11 0 0x00000001#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 17797) (by decide +kernel) (by decide +kernel)
theorem f8001e11a : fetchDecode img 0x8001e11a = some (Instr.jal 0 0xffffffd6#32, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 49113) (by decide +kernel) (by decide +kernel)
theorem f8001e11c : fetchDecode img 0x8001e11c = some (Instr.lui 13 0x80029000#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 2147653303) (by decide +kernel) (by decide +kernel)
theorem f8001e120 : fetchDecode img 0x8001e120 = some (Instr.opimm (AluOp.add) 13 13 0xfffffc90#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 3372648083) (by decide +kernel) (by decide +kernel)
theorem f8001e124 : fetchDecode img 0x8001e124 = some (Instr.op (AluOp.add) 10 0 12, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 34098) (by decide +kernel) (by decide +kernel)
theorem f8001e126 : fetchDecode img 0x8001e126 = some (Instr.op (AluOp.add) 11 0 12, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 34226) (by decide +kernel) (by decide +kernel)
theorem f8001e128 : fetchDecode img 0x8001e128 = some (Instr.op (AluOp.add) 12 0 13, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 34358) (by decide +kernel) (by decide +kernel)
theorem f8001e12a : fetchDecode img 0x8001e12a = some (Instr.auipc 1 0x00001000#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 4247) (by decide +kernel) (by decide +kernel)
theorem f8001e12e : fetchDecode img 0x8001e12e = some (Instr.jalr 1 1 0x00000710#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 1895858407) (by decide +kernel) (by decide +kernel)
theorem f8001e132 : fetchDecode img 0x8001e132 = some (Instr.lui 14 0x80029000#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 2147653431) (by decide +kernel) (by decide +kernel)
theorem f8001e136 : fetchDecode img 0x8001e136 = some (Instr.opimm (AluOp.add) 14 14 0xfffffc80#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 3355903763) (by decide +kernel) (by decide +kernel)
theorem f8001e13a : fetchDecode img 0x8001e13a = some (Instr.op (AluOp.add) 10 0 29, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 34166) (by decide +kernel) (by decide +kernel)
theorem f8001e13c : fetchDecode img 0x8001e13c = some (Instr.op (AluOp.add) 11 0 12, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 34226) (by decide +kernel) (by decide +kernel)
theorem f8001e13e : fetchDecode img 0x8001e13e = some (Instr.op (AluOp.add) 12 0 14, 2) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 34362) (by decide +kernel) (by decide +kernel)
theorem f8001e140 : fetchDecode img 0x8001e140 = some (Instr.auipc 1 0x00001000#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 4247) (by decide +kernel) (by decide +kernel)
theorem f8001e144 : fetchDecode img 0x8001e144 = some (Instr.jalr 1 1 0x000006fa#32, 4) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 1872789735) (by decide +kernel) (by decide +kernel)

end E5R.Rmk.CobsFetch
