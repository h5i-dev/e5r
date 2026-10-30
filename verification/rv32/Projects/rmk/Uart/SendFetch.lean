/-
  Instruction facts for `Uart16550<MmioBackend>::send_bytes` (0x800098a6..0x8000999e) and the
  `uart_16550::backend::assert_offset` check it calls (0x8001692e..0x80016940), in the pinned RMK
  image, generated from the model's own decoder (the `fetchDecode_of` form of
  Projects/rmk/Deframer/TailFetch.lean) and checked by the kernel against the packed ELF.

  Original e5r code, Apache-2.0. Regenerate rather than edit by hand.
-/
import Projects.rmk.Fetch

set_option maxRecDepth 100000

namespace E5R.Rmk.SendFetch
open E5R E5R.Rmk

theorem f800098a6 : fetchDecode img 0x800098a6 = some (E5R.Instr.opimm (E5R.AluOp.add) 2 2 0xffffffd0#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x7179) (by decide +kernel) (by decide +kernel)

theorem f800098a8 : fetchDecode img 0x800098a8 = some (E5R.Instr.store (E5R.Width.w) 2 1 0x0000002c#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xd606) (by decide +kernel) (by decide +kernel)

theorem f800098aa : fetchDecode img 0x800098aa = some (E5R.Instr.store (E5R.Width.w) 2 8 0x00000028#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xd422) (by decide +kernel) (by decide +kernel)

theorem f800098ac : fetchDecode img 0x800098ac = some (E5R.Instr.store (E5R.Width.w) 2 9 0x00000024#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xd226) (by decide +kernel) (by decide +kernel)

theorem f800098ae : fetchDecode img 0x800098ae = some (E5R.Instr.store (E5R.Width.w) 2 18 0x00000020#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xd04a) (by decide +kernel) (by decide +kernel)

theorem f800098b0 : fetchDecode img 0x800098b0 = some (E5R.Instr.store (E5R.Width.w) 2 19 0x0000001c#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xce4e) (by decide +kernel) (by decide +kernel)

theorem f800098b2 : fetchDecode img 0x800098b2 = some (E5R.Instr.store (E5R.Width.w) 2 20 0x00000018#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xcc52) (by decide +kernel) (by decide +kernel)

theorem f800098b4 : fetchDecode img 0x800098b4 = some (E5R.Instr.store (E5R.Width.w) 2 21 0x00000014#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xca56) (by decide +kernel) (by decide +kernel)

theorem f800098b6 : fetchDecode img 0x800098b6 = some (E5R.Instr.store (E5R.Width.w) 2 22 0x00000010#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc85a) (by decide +kernel) (by decide +kernel)

theorem f800098b8 : fetchDecode img 0x800098b8 = some (E5R.Instr.store (E5R.Width.w) 2 23 0x0000000c#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc65e) (by decide +kernel) (by decide +kernel)

theorem f800098ba : fetchDecode img 0x800098ba = some (E5R.Instr.branch (E5R.BrCond.eq) 12 0 0x00000040#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc221) (by decide +kernel) (by decide +kernel)

theorem f800098bc : fetchDecode img 0x800098bc = some (E5R.Instr.op (E5R.AluOp.add) 19 0 12, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x89b2) (by decide +kernel) (by decide +kernel)

theorem f800098be : fetchDecode img 0x800098be = some (E5R.Instr.op (E5R.AluOp.add) 23 0 11, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8bae) (by decide +kernel) (by decide +kernel)

theorem f800098c0 : fetchDecode img 0x800098c0 = some (E5R.Instr.op (E5R.AluOp.add) 18 0 10, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x892a) (by decide +kernel) (by decide +kernel)

theorem f800098c2 : fetchDecode img 0x800098c2 = some (E5R.Instr.lui 11 0x80025000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x800255b7) (by decide +kernel) (by decide +kernel)

theorem f800098c6 : fetchDecode img 0x800098c6 = some (E5R.Instr.opimm (E5R.AluOp.add) 11 11 0xfffffcb0#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xcb058593) (by decide +kernel) (by decide +kernel)

theorem f800098ca : fetchDecode img 0x800098ca = some (E5R.Instr.opimm (E5R.AluOp.add) 10 0 0x00000005#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4515) (by decide +kernel) (by decide +kernel)

theorem f800098cc : fetchDecode img 0x800098cc = some (E5R.Instr.auipc 1 0x0000d000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xd097) (by decide +kernel) (by decide +kernel)

theorem f800098d0 : fetchDecode img 0x800098d0 = some (E5R.Instr.jalr 1 1 0x00000062#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x62080e7) (by decide +kernel) (by decide +kernel)

theorem f800098d4 : fetchDecode img 0x800098d4 = some (E5R.Instr.load (E5R.Width.b) false 20 18 0x00000020#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2094a03) (by decide +kernel) (by decide +kernel)

theorem f800098d8 : fetchDecode img 0x800098d8 = some (E5R.Instr.opimm (E5R.AluOp.sll) 21 20 0x00000002#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2a1a93) (by decide +kernel) (by decide +kernel)

theorem f800098dc : fetchDecode img 0x800098dc = some (E5R.Instr.op (E5R.AluOp.add) 10 21 20, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x14a8533) (by decide +kernel) (by decide +kernel)

theorem f800098e0 : fetchDecode img 0x800098e0 = some (E5R.Instr.opimm (E5R.AluOp.srl) 11 10 0x00000008#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x855593) (by decide +kernel) (by decide +kernel)

theorem f800098e4 : fetchDecode img 0x800098e4 = some (E5R.Instr.branch (E5R.BrCond.ne) 11 0 0x000000ba#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xedcd) (by decide +kernel) (by decide +kernel)

theorem f800098e6 : fetchDecode img 0x800098e6 = some (E5R.Instr.load (E5R.Width.w) true 22 18 0x0000001c#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1c92b03) (by decide +kernel) (by decide +kernel)

theorem f800098ea : fetchDecode img 0x800098ea = some (E5R.Instr.opimm (E5R.AluOp.and) 10 10 0x000000ff#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xff57513) (by decide +kernel) (by decide +kernel)

theorem f800098ee : fetchDecode img 0x800098ee = some (E5R.Instr.op (E5R.AluOp.add) 10 10 22, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x955a) (by decide +kernel) (by decide +kernel)

theorem f800098f0 : fetchDecode img 0x800098f0 = some (E5R.Instr.load (E5R.Width.b) false 10 10 0x00000000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x54503) (by decide +kernel) (by decide +kernel)

theorem f800098f4 : fetchDecode img 0x800098f4 = some (E5R.Instr.opimm (E5R.AluOp.and) 10 10 0x00000020#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2057513) (by decide +kernel) (by decide +kernel)

theorem f800098f8 : fetchDecode img 0x800098f8 = some (E5R.Instr.branch (E5R.BrCond.ne) 10 0 0x00000006#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xe119) (by decide +kernel) (by decide +kernel)

theorem f800098fa : fetchDecode img 0x800098fa = some (E5R.Instr.opimm (E5R.AluOp.add) 19 0 0x00000000#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4981) (by decide +kernel) (by decide +kernel)

theorem f800098fc : fetchDecode img 0x800098fc = some (E5R.Instr.jal 0 0x0000008a#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xa069) (by decide +kernel) (by decide +kernel)

theorem f800098fe : fetchDecode img 0x800098fe = some (E5R.Instr.load (E5R.Width.b) false 10 18 0x00000015#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1594503) (by decide +kernel) (by decide +kernel)

theorem f80009902 : fetchDecode img 0x80009902 = some (E5R.Instr.branch (E5R.BrCond.eq) 10 0 0x0000004a#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc529) (by decide +kernel) (by decide +kernel)

theorem f80009904 : fetchDecode img 0x80009904 = some (E5R.Instr.lui 11 0x80025000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x800255b7) (by decide +kernel) (by decide +kernel)

theorem f80009908 : fetchDecode img 0x80009908 = some (E5R.Instr.opimm (E5R.AluOp.add) 11 11 0xfffffcb0#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xcb058593) (by decide +kernel) (by decide +kernel)

theorem f8000990c : fetchDecode img 0x8000990c = some (E5R.Instr.opimm (E5R.AluOp.add) 10 0 0x00000004#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4511) (by decide +kernel) (by decide +kernel)

theorem f8000990e : fetchDecode img 0x8000990e = some (E5R.Instr.auipc 1 0x0000d000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xd097) (by decide +kernel) (by decide +kernel)

theorem f80009912 : fetchDecode img 0x80009912 = some (E5R.Instr.jalr 1 1 0x00000020#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x20080e7) (by decide +kernel) (by decide +kernel)

theorem f80009916 : fetchDecode img 0x80009916 = some (E5R.Instr.op (E5R.AluOp.add) 10 22 21, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x15b0533) (by decide +kernel) (by decide +kernel)

theorem f8000991a : fetchDecode img 0x8000991a = some (E5R.Instr.load (E5R.Width.b) false 10 10 0x00000000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x54503) (by decide +kernel) (by decide +kernel)

theorem f8000991e : fetchDecode img 0x8000991e = some (E5R.Instr.opimm (E5R.AluOp.and) 10 10 0x00000010#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8941) (by decide +kernel) (by decide +kernel)

theorem f80009920 : fetchDecode img 0x80009920 = some (E5R.Instr.branch (E5R.BrCond.ne) 10 0 0x0000002c#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xe515) (by decide +kernel) (by decide +kernel)

theorem f80009922 : fetchDecode img 0x80009922 = some (E5R.Instr.lui 11 0x80025000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x800255b7) (by decide +kernel) (by decide +kernel)

theorem f80009926 : fetchDecode img 0x80009926 = some (E5R.Instr.opimm (E5R.AluOp.add) 11 11 0xfffffcb0#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xcb058593) (by decide +kernel) (by decide +kernel)

theorem f8000992a : fetchDecode img 0x8000992a = some (E5R.Instr.opimm (E5R.AluOp.add) 10 0 0x00000006#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4519) (by decide +kernel) (by decide +kernel)

theorem f8000992c : fetchDecode img 0x8000992c = some (E5R.Instr.auipc 1 0x0000d000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xd097) (by decide +kernel) (by decide +kernel)

theorem f80009930 : fetchDecode img 0x80009930 = some (E5R.Instr.jalr 1 1 0x00000002#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2080e7) (by decide +kernel) (by decide +kernel)

theorem f80009934 : fetchDecode img 0x80009934 = some (E5R.Instr.opimm (E5R.AluOp.sll) 20 20 0x00000001#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xa06) (by decide +kernel) (by decide +kernel)

theorem f80009936 : fetchDecode img 0x80009936 = some (E5R.Instr.op (E5R.AluOp.add) 21 21 20, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x9ad2) (by decide +kernel) (by decide +kernel)

theorem f80009938 : fetchDecode img 0x80009938 = some (E5R.Instr.opimm (E5R.AluOp.srl) 10 21 0x00000008#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8ad513) (by decide +kernel) (by decide +kernel)

theorem f8000993c : fetchDecode img 0x8000993c = some (E5R.Instr.branch (E5R.BrCond.ne) 10 0 0x00000062#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xe12d) (by decide +kernel) (by decide +kernel)

theorem f8000993e : fetchDecode img 0x8000993e = some (E5R.Instr.opimm (E5R.AluOp.and) 10 21 0x000000ff#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xffaf513) (by decide +kernel) (by decide +kernel)

theorem f80009942 : fetchDecode img 0x80009942 = some (E5R.Instr.op (E5R.AluOp.add) 10 10 22, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x955a) (by decide +kernel) (by decide +kernel)

theorem f80009944 : fetchDecode img 0x80009944 = some (E5R.Instr.load (E5R.Width.b) false 10 10 0x00000000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x54503) (by decide +kernel) (by decide +kernel)

theorem f80009948 : fetchDecode img 0x80009948 = some (E5R.Instr.opimm (E5R.AluOp.and) 10 10 0x00000010#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8941) (by decide +kernel) (by decide +kernel)

theorem f8000994a : fetchDecode img 0x8000994a = some (E5R.Instr.branch (E5R.BrCond.eq) 10 0 0xffffffb0#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xd945) (by decide +kernel) (by decide +kernel)

theorem f8000994c : fetchDecode img 0x8000994c = some (E5R.Instr.load (E5R.Width.b) false 10 18 0x00000017#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1794503) (by decide +kernel) (by decide +kernel)

theorem f80009950 : fetchDecode img 0x80009950 = some (E5R.Instr.opimm (E5R.AluOp.add) 11 0 0x00000010#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x45c1) (by decide +kernel) (by decide +kernel)

theorem f80009952 : fetchDecode img 0x80009952 = some (E5R.Instr.branch (E5R.BrCond.ltu) 19 11 0x00000006#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xb9e363) (by decide +kernel) (by decide +kernel)

theorem f80009956 : fetchDecode img 0x80009956 = some (E5R.Instr.opimm (E5R.AluOp.add) 19 0 0x00000010#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x49c1) (by decide +kernel) (by decide +kernel)

theorem f80009958 : fetchDecode img 0x80009958 = some (E5R.Instr.opimm (E5R.AluOp.add) 11 0 0x000000ff#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xff00593) (by decide +kernel) (by decide +kernel)

theorem f8000995c : fetchDecode img 0x8000995c = some (E5R.Instr.branch (E5R.BrCond.ne) 10 11 0x00000006#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xb51363) (by decide +kernel) (by decide +kernel)

theorem f80009960 : fetchDecode img 0x80009960 = some (E5R.Instr.opimm (E5R.AluOp.add) 19 0 0x00000001#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4985) (by decide +kernel) (by decide +kernel)

theorem f80009962 : fetchDecode img 0x80009962 = some (E5R.Instr.lui 18 0x80025000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x80025937) (by decide +kernel) (by decide +kernel)

theorem f80009966 : fetchDecode img 0x80009966 = some (E5R.Instr.opimm (E5R.AluOp.add) 18 18 0xfffffcfc#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xcfc90913) (by decide +kernel) (by decide +kernel)

theorem f8000996a : fetchDecode img 0x8000996a = some (E5R.Instr.op (E5R.AluOp.add) 8 0 19, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x844e) (by decide +kernel) (by decide +kernel)

theorem f8000996c : fetchDecode img 0x8000996c = some (E5R.Instr.load (E5R.Width.b) false 9 23 0x00000000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xbc483) (by decide +kernel) (by decide +kernel)

theorem f80009970 : fetchDecode img 0x80009970 = some (E5R.Instr.opimm (E5R.AluOp.add) 23 23 0x00000001#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xb85) (by decide +kernel) (by decide +kernel)

theorem f80009972 : fetchDecode img 0x80009972 = some (E5R.Instr.opimm (E5R.AluOp.add) 10 0 0x00000000#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4501) (by decide +kernel) (by decide +kernel)

theorem f80009974 : fetchDecode img 0x80009974 = some (E5R.Instr.op (E5R.AluOp.add) 11 0 18, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x85ca) (by decide +kernel) (by decide +kernel)

theorem f80009976 : fetchDecode img 0x80009976 = some (E5R.Instr.auipc 1 0x0000d000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xd097) (by decide +kernel) (by decide +kernel)

theorem f8000997a : fetchDecode img 0x8000997a = some (E5R.Instr.jalr 1 1 0xffffffb8#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfb8080e7) (by decide +kernel) (by decide +kernel)

theorem f8000997e : fetchDecode img 0x8000997e = some (E5R.Instr.opimm (E5R.AluOp.add) 8 8 0xffffffff#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x147d) (by decide +kernel) (by decide +kernel)

theorem f80009980 : fetchDecode img 0x80009980 = some (E5R.Instr.store (E5R.Width.b) 22 9 0x00000000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x9b0023) (by decide +kernel) (by decide +kernel)

theorem f80009984 : fetchDecode img 0x80009984 = some (E5R.Instr.branch (E5R.BrCond.ne) 8 0 0xffffffe8#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xf465) (by decide +kernel) (by decide +kernel)

theorem f80009986 : fetchDecode img 0x80009986 = some (E5R.Instr.op (E5R.AluOp.add) 10 0 19, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x854e) (by decide +kernel) (by decide +kernel)

theorem f80009988 : fetchDecode img 0x80009988 = some (E5R.Instr.load (E5R.Width.w) true 1 2 0x0000002c#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x50b2) (by decide +kernel) (by decide +kernel)

theorem f8000998a : fetchDecode img 0x8000998a = some (E5R.Instr.load (E5R.Width.w) true 8 2 0x00000028#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x5422) (by decide +kernel) (by decide +kernel)

theorem f8000998c : fetchDecode img 0x8000998c = some (E5R.Instr.load (E5R.Width.w) true 9 2 0x00000024#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x5492) (by decide +kernel) (by decide +kernel)

theorem f8000998e : fetchDecode img 0x8000998e = some (E5R.Instr.load (E5R.Width.w) true 18 2 0x00000020#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x5902) (by decide +kernel) (by decide +kernel)

theorem f80009990 : fetchDecode img 0x80009990 = some (E5R.Instr.load (E5R.Width.w) true 19 2 0x0000001c#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x49f2) (by decide +kernel) (by decide +kernel)

theorem f80009992 : fetchDecode img 0x80009992 = some (E5R.Instr.load (E5R.Width.w) true 20 2 0x00000018#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4a62) (by decide +kernel) (by decide +kernel)

theorem f80009994 : fetchDecode img 0x80009994 = some (E5R.Instr.load (E5R.Width.w) true 21 2 0x00000014#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4ad2) (by decide +kernel) (by decide +kernel)

theorem f80009996 : fetchDecode img 0x80009996 = some (E5R.Instr.load (E5R.Width.w) true 22 2 0x00000010#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4b42) (by decide +kernel) (by decide +kernel)

theorem f80009998 : fetchDecode img 0x80009998 = some (E5R.Instr.load (E5R.Width.w) true 23 2 0x0000000c#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4bb2) (by decide +kernel) (by decide +kernel)

theorem f8000999a : fetchDecode img 0x8000999a = some (E5R.Instr.opimm (E5R.AluOp.add) 2 2 0x00000030#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x6145) (by decide +kernel) (by decide +kernel)

theorem f8000999c : fetchDecode img 0x8000999c = some (E5R.Instr.jalr 0 1 0x00000000#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8082) (by decide +kernel) (by decide +kernel)

theorem f8001692e : fetchDecode img 0x8001692e = some (E5R.Instr.opimm (E5R.AluOp.add) 2 2 0xffffffe0#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1101) (by decide +kernel) (by decide +kernel)

theorem f80016930 : fetchDecode img 0x80016930 = some (E5R.Instr.op (E5R.AluOp.add) 12 0 11, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x862e) (by decide +kernel) (by decide +kernel)

theorem f80016932 : fetchDecode img 0x80016932 = some (E5R.Instr.opimm (E5R.AluOp.add) 11 0 0x00000008#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x45a1) (by decide +kernel) (by decide +kernel)

theorem f80016934 : fetchDecode img 0x80016934 = some (E5R.Instr.store (E5R.Width.b) 2 10 0x0000000f#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xa107a3) (by decide +kernel) (by decide +kernel)

theorem f80016938 : fetchDecode img 0x80016938 = some (E5R.Instr.branch (E5R.BrCond.geu) 10 11 0x00000008#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xb57463) (by decide +kernel) (by decide +kernel)

theorem f8001693c : fetchDecode img 0x8001693c = some (E5R.Instr.opimm (E5R.AluOp.add) 2 2 0x00000020#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x6105) (by decide +kernel) (by decide +kernel)

theorem f8001693e : fetchDecode img 0x8001693e = some (E5R.Instr.jalr 0 1 0x00000000#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8082) (by decide +kernel) (by decide +kernel)

end E5R.Rmk.SendFetch
