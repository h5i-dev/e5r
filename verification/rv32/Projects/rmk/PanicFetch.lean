/-
  Instruction facts for the panic path of the pinned RMK image: `core::slice::index::
  slice_index_fail` (0x8001fafc..0x8001fbca), `core::panicking::panic_bounds_check`
  (0x8001f83a..0x8001f876), `core::panicking::panic_fmt` (0x8001f956..0x8001f984) and the
  panic-halt handler `rust_begin_unwind` (0x8001e148, `j .`), generated from the model's own decoder
  (/dev/shm generator, the `fetchDecode_of` form of Projects/rmk/Deframer/TailFetch.lean) and
  checked by the kernel against the packed ELF.

  Original e5r code, Apache-2.0. Regenerate rather than edit by hand.
-/
import Projects.rmk.Fetch

set_option maxRecDepth 100000

namespace E5R.Rmk.PanicFetch
open E5R E5R.Rmk

theorem f8001fafc : fetchDecode img 0x8001fafc = some (E5R.Instr.opimm (E5R.AluOp.add) 2 2 0xffffffe0#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1101) (by decide +kernel) (by decide +kernel)

theorem f8001fafe : fetchDecode img 0x8001fafe = some (E5R.Instr.store (E5R.Width.w) 2 1 0x0000001c#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xce06) (by decide +kernel) (by decide +kernel)

theorem f8001fb00 : fetchDecode img 0x8001fb00 = some (E5R.Instr.store (E5R.Width.w) 2 8 0x00000018#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xcc22) (by decide +kernel) (by decide +kernel)

theorem f8001fb02 : fetchDecode img 0x8001fb02 = some (E5R.Instr.opimm (E5R.AluOp.add) 8 2 0x00000020#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1000) (by decide +kernel) (by decide +kernel)

theorem f8001fb04 : fetchDecode img 0x8001fb04 = some (E5R.Instr.branch (E5R.BrCond.geu) 12 10 0x00000042#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4a67163) (by decide +kernel) (by decide +kernel)

theorem f8001fb08 : fetchDecode img 0x8001fb08 = some (E5R.Instr.store (E5R.Width.w) 8 10 0xffffffe0#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfea42023) (by decide +kernel) (by decide +kernel)

theorem f8001fb0c : fetchDecode img 0x8001fb0c = some (E5R.Instr.store (E5R.Width.w) 8 12 0xffffffe4#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfec42223) (by decide +kernel) (by decide +kernel)

theorem f8001fb10 : fetchDecode img 0x8001fb10 = some (E5R.Instr.opimm (E5R.AluOp.add) 10 8 0xffffffe0#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfe040513) (by decide +kernel) (by decide +kernel)

theorem f8001fb14 : fetchDecode img 0x8001fb14 = some (E5R.Instr.lui 11 0x80020000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x800205b7) (by decide +kernel) (by decide +kernel)

theorem f8001fb18 : fetchDecode img 0x8001fb18 = some (E5R.Instr.opimm (E5R.AluOp.add) 11 11 0x0000020c#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x20c58593) (by decide +kernel) (by decide +kernel)

theorem f8001fb1c : fetchDecode img 0x8001fb1c = some (E5R.Instr.opimm (E5R.AluOp.add) 12 8 0xffffffe4#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfe440613) (by decide +kernel) (by decide +kernel)

theorem f8001fb20 : fetchDecode img 0x8001fb20 = some (E5R.Instr.store (E5R.Width.w) 8 10 0xffffffe8#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfea42423) (by decide +kernel) (by decide +kernel)

theorem f8001fb24 : fetchDecode img 0x8001fb24 = some (E5R.Instr.store (E5R.Width.w) 8 11 0xffffffec#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfeb42623) (by decide +kernel) (by decide +kernel)

theorem f8001fb28 : fetchDecode img 0x8001fb28 = some (E5R.Instr.store (E5R.Width.w) 8 12 0xfffffff0#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfec42823) (by decide +kernel) (by decide +kernel)

theorem f8001fb2c : fetchDecode img 0x8001fb2c = some (E5R.Instr.store (E5R.Width.w) 8 11 0xfffffff4#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfeb42a23) (by decide +kernel) (by decide +kernel)

theorem f8001fb30 : fetchDecode img 0x8001fb30 = some (E5R.Instr.lui 10 0x80022000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x80022537) (by decide +kernel) (by decide +kernel)

theorem f8001fb34 : fetchDecode img 0x8001fb34 = some (E5R.Instr.opimm (E5R.AluOp.add) 10 10 0xffffffc8#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfc850513) (by decide +kernel) (by decide +kernel)

theorem f8001fb38 : fetchDecode img 0x8001fb38 = some (E5R.Instr.opimm (E5R.AluOp.add) 11 8 0xffffffe8#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfe840593) (by decide +kernel) (by decide +kernel)

theorem f8001fb3c : fetchDecode img 0x8001fb3c = some (E5R.Instr.op (E5R.AluOp.add) 12 0 13, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8636) (by decide +kernel) (by decide +kernel)

theorem f8001fb3e : fetchDecode img 0x8001fb3e = some (E5R.Instr.auipc 1 0x00000000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x97) (by decide +kernel) (by decide +kernel)

theorem f8001fb42 : fetchDecode img 0x8001fb42 = some (E5R.Instr.jalr 1 1 0xfffffe18#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xe18080e7) (by decide +kernel) (by decide +kernel)

theorem f8001fb46 : fetchDecode img 0x8001fb46 = some (E5R.Instr.branch (E5R.BrCond.ltu) 12 11 0x00000046#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4b66363) (by decide +kernel) (by decide +kernel)

theorem f8001fb4a : fetchDecode img 0x8001fb4a = some (E5R.Instr.branch (E5R.BrCond.geu) 11 10 0x00000042#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4a5f163) (by decide +kernel) (by decide +kernel)

theorem f8001fb4e : fetchDecode img 0x8001fb4e = some (E5R.Instr.store (E5R.Width.w) 8 10 0xffffffe0#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfea42023) (by decide +kernel) (by decide +kernel)

theorem f8001fb52 : fetchDecode img 0x8001fb52 = some (E5R.Instr.store (E5R.Width.w) 8 11 0xffffffe4#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfeb42223) (by decide +kernel) (by decide +kernel)

theorem f8001fb56 : fetchDecode img 0x8001fb56 = some (E5R.Instr.opimm (E5R.AluOp.add) 10 8 0xffffffe0#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfe040513) (by decide +kernel) (by decide +kernel)

theorem f8001fb5a : fetchDecode img 0x8001fb5a = some (E5R.Instr.lui 11 0x80020000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x800205b7) (by decide +kernel) (by decide +kernel)

theorem f8001fb5e : fetchDecode img 0x8001fb5e = some (E5R.Instr.opimm (E5R.AluOp.add) 11 11 0x0000020c#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x20c58593) (by decide +kernel) (by decide +kernel)

theorem f8001fb62 : fetchDecode img 0x8001fb62 = some (E5R.Instr.opimm (E5R.AluOp.add) 12 8 0xffffffe4#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfe440613) (by decide +kernel) (by decide +kernel)

theorem f8001fb66 : fetchDecode img 0x8001fb66 = some (E5R.Instr.store (E5R.Width.w) 8 10 0xffffffe8#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfea42423) (by decide +kernel) (by decide +kernel)

theorem f8001fb6a : fetchDecode img 0x8001fb6a = some (E5R.Instr.store (E5R.Width.w) 8 11 0xffffffec#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfeb42623) (by decide +kernel) (by decide +kernel)

theorem f8001fb6e : fetchDecode img 0x8001fb6e = some (E5R.Instr.store (E5R.Width.w) 8 12 0xfffffff0#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfec42823) (by decide +kernel) (by decide +kernel)

theorem f8001fb72 : fetchDecode img 0x8001fb72 = some (E5R.Instr.store (E5R.Width.w) 8 11 0xfffffff4#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfeb42a23) (by decide +kernel) (by decide +kernel)

theorem f8001fb76 : fetchDecode img 0x8001fb76 = some (E5R.Instr.lui 10 0x80022000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x80022537) (by decide +kernel) (by decide +kernel)

theorem f8001fb7a : fetchDecode img 0x8001fb7a = some (E5R.Instr.opimm (E5R.AluOp.add) 10 10 0xfffffa2d#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xa2d50513) (by decide +kernel) (by decide +kernel)

theorem f8001fb7e : fetchDecode img 0x8001fb7e = some (E5R.Instr.opimm (E5R.AluOp.add) 11 8 0xffffffe8#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfe840593) (by decide +kernel) (by decide +kernel)

theorem f8001fb82 : fetchDecode img 0x8001fb82 = some (E5R.Instr.op (E5R.AluOp.add) 12 0 13, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8636) (by decide +kernel) (by decide +kernel)

theorem f8001fb84 : fetchDecode img 0x8001fb84 = some (E5R.Instr.auipc 1 0x00000000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x97) (by decide +kernel) (by decide +kernel)

theorem f8001fb88 : fetchDecode img 0x8001fb88 = some (E5R.Instr.jalr 1 1 0xfffffdd2#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xdd2080e7) (by decide +kernel) (by decide +kernel)

theorem f8001fb8c : fetchDecode img 0x8001fb8c = some (E5R.Instr.store (E5R.Width.w) 8 11 0xffffffe0#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfeb42023) (by decide +kernel) (by decide +kernel)

theorem f8001fb90 : fetchDecode img 0x8001fb90 = some (E5R.Instr.store (E5R.Width.w) 8 12 0xffffffe4#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfec42223) (by decide +kernel) (by decide +kernel)

theorem f8001fb94 : fetchDecode img 0x8001fb94 = some (E5R.Instr.opimm (E5R.AluOp.add) 10 8 0xffffffe0#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfe040513) (by decide +kernel) (by decide +kernel)

theorem f8001fb98 : fetchDecode img 0x8001fb98 = some (E5R.Instr.lui 11 0x80020000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x800205b7) (by decide +kernel) (by decide +kernel)

theorem f8001fb9c : fetchDecode img 0x8001fb9c = some (E5R.Instr.opimm (E5R.AluOp.add) 11 11 0x0000020c#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x20c58593) (by decide +kernel) (by decide +kernel)

theorem f8001fba0 : fetchDecode img 0x8001fba0 = some (E5R.Instr.opimm (E5R.AluOp.add) 12 8 0xffffffe4#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfe440613) (by decide +kernel) (by decide +kernel)

theorem f8001fba4 : fetchDecode img 0x8001fba4 = some (E5R.Instr.store (E5R.Width.w) 8 10 0xffffffe8#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfea42423) (by decide +kernel) (by decide +kernel)

theorem f8001fba8 : fetchDecode img 0x8001fba8 = some (E5R.Instr.store (E5R.Width.w) 8 11 0xffffffec#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfeb42623) (by decide +kernel) (by decide +kernel)

theorem f8001fbac : fetchDecode img 0x8001fbac = some (E5R.Instr.store (E5R.Width.w) 8 12 0xfffffff0#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfec42823) (by decide +kernel) (by decide +kernel)

theorem f8001fbb0 : fetchDecode img 0x8001fbb0 = some (E5R.Instr.store (E5R.Width.w) 8 11 0xfffffff4#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfeb42a23) (by decide +kernel) (by decide +kernel)

theorem f8001fbb4 : fetchDecode img 0x8001fbb4 = some (E5R.Instr.lui 10 0x80022000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x80022537) (by decide +kernel) (by decide +kernel)

theorem f8001fbb8 : fetchDecode img 0x8001fbb8 = some (E5R.Instr.opimm (E5R.AluOp.add) 10 10 0xffffff49#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xf4950513) (by decide +kernel) (by decide +kernel)

theorem f8001fbbc : fetchDecode img 0x8001fbbc = some (E5R.Instr.opimm (E5R.AluOp.add) 11 8 0xffffffe8#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfe840593) (by decide +kernel) (by decide +kernel)

theorem f8001fbc0 : fetchDecode img 0x8001fbc0 = some (E5R.Instr.op (E5R.AluOp.add) 12 0 13, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8636) (by decide +kernel) (by decide +kernel)

theorem f8001fbc2 : fetchDecode img 0x8001fbc2 = some (E5R.Instr.auipc 1 0x00000000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x97) (by decide +kernel) (by decide +kernel)

theorem f8001fbc6 : fetchDecode img 0x8001fbc6 = some (E5R.Instr.jalr 1 1 0xfffffd94#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xd94080e7) (by decide +kernel) (by decide +kernel)

theorem f8001f83a : fetchDecode img 0x8001f83a = some (E5R.Instr.opimm (E5R.AluOp.add) 2 2 0xffffffe0#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1101) (by decide +kernel) (by decide +kernel)

theorem f8001f83c : fetchDecode img 0x8001f83c = some (E5R.Instr.store (E5R.Width.w) 2 1 0x0000001c#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xce06) (by decide +kernel) (by decide +kernel)

theorem f8001f83e : fetchDecode img 0x8001f83e = some (E5R.Instr.store (E5R.Width.w) 2 8 0x00000018#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xcc22) (by decide +kernel) (by decide +kernel)

theorem f8001f840 : fetchDecode img 0x8001f840 = some (E5R.Instr.opimm (E5R.AluOp.add) 8 2 0x00000020#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1000) (by decide +kernel) (by decide +kernel)

theorem f8001f842 : fetchDecode img 0x8001f842 = some (E5R.Instr.opimm (E5R.AluOp.add) 14 8 0xffffff80#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xf8040713) (by decide +kernel) (by decide +kernel)

theorem f8001f846 : fetchDecode img 0x8001f846 = some (E5R.Instr.store (E5R.Width.w) 14 10 0x00000060#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xd328) (by decide +kernel) (by decide +kernel)

theorem f8001f848 : fetchDecode img 0x8001f848 = some (E5R.Instr.store (E5R.Width.w) 14 11 0x00000064#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xd36c) (by decide +kernel) (by decide +kernel)

theorem f8001f84a : fetchDecode img 0x8001f84a = some (E5R.Instr.opimm (E5R.AluOp.add) 10 8 0xffffffe4#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfe440513) (by decide +kernel) (by decide +kernel)

theorem f8001f84e : fetchDecode img 0x8001f84e = some (E5R.Instr.lui 11 0x80020000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x800205b7) (by decide +kernel) (by decide +kernel)

theorem f8001f852 : fetchDecode img 0x8001f852 = some (E5R.Instr.opimm (E5R.AluOp.add) 11 11 0x0000020c#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x20c58593) (by decide +kernel) (by decide +kernel)

theorem f8001f856 : fetchDecode img 0x8001f856 = some (E5R.Instr.opimm (E5R.AluOp.add) 13 8 0xffffffe0#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfe040693) (by decide +kernel) (by decide +kernel)

theorem f8001f85a : fetchDecode img 0x8001f85a = some (E5R.Instr.store (E5R.Width.w) 14 10 0x00000068#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xd728) (by decide +kernel) (by decide +kernel)

theorem f8001f85c : fetchDecode img 0x8001f85c = some (E5R.Instr.store (E5R.Width.w) 14 11 0x0000006c#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xd76c) (by decide +kernel) (by decide +kernel)

theorem f8001f85e : fetchDecode img 0x8001f85e = some (E5R.Instr.store (E5R.Width.w) 14 13 0x00000070#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xdb34) (by decide +kernel) (by decide +kernel)

theorem f8001f860 : fetchDecode img 0x8001f860 = some (E5R.Instr.store (E5R.Width.w) 14 11 0x00000074#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xdb6c) (by decide +kernel) (by decide +kernel)

theorem f8001f862 : fetchDecode img 0x8001f862 = some (E5R.Instr.lui 10 0x80022000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x80022537) (by decide +kernel) (by decide +kernel)

theorem f8001f866 : fetchDecode img 0x8001f866 = some (E5R.Instr.opimm (E5R.AluOp.add) 10 10 0xfffffbd6#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xbd650513) (by decide +kernel) (by decide +kernel)

theorem f8001f86a : fetchDecode img 0x8001f86a = some (E5R.Instr.opimm (E5R.AluOp.add) 11 8 0xffffffe8#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfe840593) (by decide +kernel) (by decide +kernel)

theorem f8001f86e : fetchDecode img 0x8001f86e = some (E5R.Instr.auipc 1 0x00000000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x97) (by decide +kernel) (by decide +kernel)

theorem f8001f872 : fetchDecode img 0x8001f872 = some (E5R.Instr.jalr 1 1 0x000000e8#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xe8080e7) (by decide +kernel) (by decide +kernel)

theorem f8001f956 : fetchDecode img 0x8001f956 = some (E5R.Instr.opimm (E5R.AluOp.add) 2 2 0xffffffe0#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1101) (by decide +kernel) (by decide +kernel)

theorem f8001f958 : fetchDecode img 0x8001f958 = some (E5R.Instr.store (E5R.Width.w) 2 1 0x0000001c#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xce06) (by decide +kernel) (by decide +kernel)

theorem f8001f95a : fetchDecode img 0x8001f95a = some (E5R.Instr.store (E5R.Width.w) 2 8 0x00000018#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xcc22) (by decide +kernel) (by decide +kernel)

theorem f8001f95c : fetchDecode img 0x8001f95c = some (E5R.Instr.opimm (E5R.AluOp.add) 8 2 0x00000020#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1000) (by decide +kernel) (by decide +kernel)

theorem f8001f95e : fetchDecode img 0x8001f95e = some (E5R.Instr.store (E5R.Width.w) 8 10 0xffffffe4#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfea42223) (by decide +kernel) (by decide +kernel)

theorem f8001f962 : fetchDecode img 0x8001f962 = some (E5R.Instr.store (E5R.Width.w) 8 11 0xffffffe8#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfeb42423) (by decide +kernel) (by decide +kernel)

theorem f8001f966 : fetchDecode img 0x8001f966 = some (E5R.Instr.opimm (E5R.AluOp.add) 10 8 0xffffffe4#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfe440513) (by decide +kernel) (by decide +kernel)

theorem f8001f96a : fetchDecode img 0x8001f96a = some (E5R.Instr.opimm (E5R.AluOp.add) 11 0 0x00000001#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4585) (by decide +kernel) (by decide +kernel)

theorem f8001f96c : fetchDecode img 0x8001f96c = some (E5R.Instr.store (E5R.Width.w) 8 10 0xffffffec#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfea42623) (by decide +kernel) (by decide +kernel)

theorem f8001f970 : fetchDecode img 0x8001f970 = some (E5R.Instr.store (E5R.Width.w) 8 12 0xfffffff0#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfec42823) (by decide +kernel) (by decide +kernel)

theorem f8001f974 : fetchDecode img 0x8001f974 = some (E5R.Instr.store (E5R.Width.h) 8 11 0xfffffff4#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfeb41a23) (by decide +kernel) (by decide +kernel)

theorem f8001f978 : fetchDecode img 0x8001f978 = some (E5R.Instr.opimm (E5R.AluOp.add) 10 8 0xffffffec#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfec40513) (by decide +kernel) (by decide +kernel)

theorem f8001f97c : fetchDecode img 0x8001f97c = some (E5R.Instr.auipc 1 0xffffe000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xffffe097) (by decide +kernel) (by decide +kernel)

theorem f8001f980 : fetchDecode img 0x8001f980 = some (E5R.Instr.jalr 1 1 0x000007cc#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x7cc080e7) (by decide +kernel) (by decide +kernel)

theorem f8001e148 : fetchDecode img 0x8001e148 = some (E5R.Instr.jal 0 0x00000000#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xa001) (by decide +kernel) (by decide +kernel)

end E5R.Rmk.PanicFetch
