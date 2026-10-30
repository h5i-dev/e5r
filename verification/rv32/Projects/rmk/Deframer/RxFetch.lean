/-
  Instruction facts for the session's UART receive poll (0x80004374..0x800043a8, inside the main
  task's poll: read LSR, if data ready read RBR into the buffer, up to the free space) and
  `uart_16550::backend::assert_offset` (0x8001692e..0x80016940), in the pinned RMK image, generated
  from the model's own decoder (/dev/shm generator, the `fetchDecode_of` form of
  Projects/rmk/Deframer/TailFetch.lean) and checked by the kernel against the packed ELF.

  Original e5r code, Apache-2.0. Regenerate rather than edit by hand.
-/
import Projects.rmk.Fetch

set_option maxRecDepth 100000

namespace E5R.Rmk.RxFetch
open E5R E5R.Rmk

theorem f80004374 : fetchDecode img 0x80004374 = some (E5R.Instr.opimm (E5R.AluOp.add) 10 0 0x00000005#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4515) (by decide +kernel) (by decide +kernel)

theorem f80004376 : fetchDecode img 0x80004376 = some (E5R.Instr.op (E5R.AluOp.add) 11 0 24, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x85e2) (by decide +kernel) (by decide +kernel)

theorem f80004378 : fetchDecode img 0x80004378 = some (E5R.Instr.auipc 1 0x00012000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x12097) (by decide +kernel) (by decide +kernel)

theorem f8000437c : fetchDecode img 0x8000437c = some (E5R.Instr.jalr 1 1 0x000005b6#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x5b6080e7) (by decide +kernel) (by decide +kernel)

theorem f80004380 : fetchDecode img 0x80004380 = some (E5R.Instr.load (E5R.Width.b) false 10 21 0x00000000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xac503) (by decide +kernel) (by decide +kernel)

theorem f80004384 : fetchDecode img 0x80004384 = some (E5R.Instr.opimm (E5R.AluOp.and) 10 10 0x00000001#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8905) (by decide +kernel) (by decide +kernel)

theorem f80004386 : fetchDecode img 0x80004386 = some (E5R.Instr.branch (E5R.BrCond.eq) 10 0 0x00000022#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc10d) (by decide +kernel) (by decide +kernel)

theorem f80004388 : fetchDecode img 0x80004388 = some (E5R.Instr.op (E5R.AluOp.add) 8 18 9, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x990433) (by decide +kernel) (by decide +kernel)

theorem f8000438c : fetchDecode img 0x8000438c = some (E5R.Instr.opimm (E5R.AluOp.add) 10 0 0x00000000#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4501) (by decide +kernel) (by decide +kernel)

theorem f8000438e : fetchDecode img 0x8000438e = some (E5R.Instr.op (E5R.AluOp.add) 11 0 24, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x85e2) (by decide +kernel) (by decide +kernel)

theorem f80004390 : fetchDecode img 0x80004390 = some (E5R.Instr.auipc 1 0x00012000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x12097) (by decide +kernel) (by decide +kernel)

theorem f80004394 : fetchDecode img 0x80004394 = some (E5R.Instr.jalr 1 1 0x0000059e#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x59e080e7) (by decide +kernel) (by decide +kernel)

theorem f80004398 : fetchDecode img 0x80004398 = some (E5R.Instr.load (E5R.Width.b) false 10 19 0x00000000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x9c503) (by decide +kernel) (by decide +kernel)

theorem f8000439c : fetchDecode img 0x8000439c = some (E5R.Instr.opimm (E5R.AluOp.add) 9 9 0x00000001#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x485) (by decide +kernel) (by decide +kernel)

theorem f8000439e : fetchDecode img 0x8000439e = some (E5R.Instr.store (E5R.Width.b) 8 10 0x00000000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xa40023) (by decide +kernel) (by decide +kernel)

theorem f800043a2 : fetchDecode img 0x800043a2 = some (E5R.Instr.branch (E5R.BrCond.ne) 20 9 0xffffffd2#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfc9a19e3) (by decide +kernel) (by decide +kernel)

theorem f800043a6 : fetchDecode img 0x800043a6 = some (E5R.Instr.op (E5R.AluOp.add) 9 0 20, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x84d2) (by decide +kernel) (by decide +kernel)

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

end E5R.Rmk.RxFetch
