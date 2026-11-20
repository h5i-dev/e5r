/-
  Instruction facts for the session's UART receive poll (0x80004374..0x800043a8, inside the main
  task's poll: read LSR, if data ready read RBR into the buffer, up to the free space) and
  `uart_16550::backend::assert_offset` (0x8001692e..0x80016940), in the pinned RMK image, generated
  from the model's own decoder (/dev/shm generator, the `fetchDecode_of` form of
  Projects/rmk/Deframer/TailFetch.lean) and checked by the kernel against the packed ELF.

  Original nocompiler code, Apache-2.0. Regenerate rather than edit by hand.
-/
import Projects.rmk.Fetch

set_option maxRecDepth 100000

namespace NoCompiler.Rmk.RxFetch
open NoCompiler NoCompiler.Rmk

theorem f80004374 : fetchDecode img 0x80004374 = some (NoCompiler.Instr.opimm (NoCompiler.AluOp.add) 10 0 0x00000005#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4515) (by decide +kernel) (by decide +kernel)

theorem f80004376 : fetchDecode img 0x80004376 = some (NoCompiler.Instr.op (NoCompiler.AluOp.add) 11 0 24, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x85e2) (by decide +kernel) (by decide +kernel)

theorem f80004378 : fetchDecode img 0x80004378 = some (NoCompiler.Instr.auipc 1 0x00012000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x12097) (by decide +kernel) (by decide +kernel)

theorem f8000437c : fetchDecode img 0x8000437c = some (NoCompiler.Instr.jalr 1 1 0x000005b6#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x5b6080e7) (by decide +kernel) (by decide +kernel)

theorem f80004380 : fetchDecode img 0x80004380 = some (NoCompiler.Instr.load (NoCompiler.Width.b) false 10 21 0x00000000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xac503) (by decide +kernel) (by decide +kernel)

theorem f80004384 : fetchDecode img 0x80004384 = some (NoCompiler.Instr.opimm (NoCompiler.AluOp.and) 10 10 0x00000001#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8905) (by decide +kernel) (by decide +kernel)

theorem f80004386 : fetchDecode img 0x80004386 = some (NoCompiler.Instr.branch (NoCompiler.BrCond.eq) 10 0 0x00000022#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc10d) (by decide +kernel) (by decide +kernel)

theorem f80004388 : fetchDecode img 0x80004388 = some (NoCompiler.Instr.op (NoCompiler.AluOp.add) 8 18 9, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x990433) (by decide +kernel) (by decide +kernel)

theorem f8000438c : fetchDecode img 0x8000438c = some (NoCompiler.Instr.opimm (NoCompiler.AluOp.add) 10 0 0x00000000#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x4501) (by decide +kernel) (by decide +kernel)

theorem f8000438e : fetchDecode img 0x8000438e = some (NoCompiler.Instr.op (NoCompiler.AluOp.add) 11 0 24, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x85e2) (by decide +kernel) (by decide +kernel)

theorem f80004390 : fetchDecode img 0x80004390 = some (NoCompiler.Instr.auipc 1 0x00012000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x12097) (by decide +kernel) (by decide +kernel)

theorem f80004394 : fetchDecode img 0x80004394 = some (NoCompiler.Instr.jalr 1 1 0x0000059e#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x59e080e7) (by decide +kernel) (by decide +kernel)

theorem f80004398 : fetchDecode img 0x80004398 = some (NoCompiler.Instr.load (NoCompiler.Width.b) false 10 19 0x00000000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x9c503) (by decide +kernel) (by decide +kernel)

theorem f8000439c : fetchDecode img 0x8000439c = some (NoCompiler.Instr.opimm (NoCompiler.AluOp.add) 9 9 0x00000001#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x485) (by decide +kernel) (by decide +kernel)

theorem f8000439e : fetchDecode img 0x8000439e = some (NoCompiler.Instr.store (NoCompiler.Width.b) 8 10 0x00000000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xa40023) (by decide +kernel) (by decide +kernel)

theorem f800043a2 : fetchDecode img 0x800043a2 = some (NoCompiler.Instr.branch (NoCompiler.BrCond.ne) 20 9 0xffffffd2#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xfc9a19e3) (by decide +kernel) (by decide +kernel)

theorem f800043a6 : fetchDecode img 0x800043a6 = some (NoCompiler.Instr.op (NoCompiler.AluOp.add) 9 0 20, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x84d2) (by decide +kernel) (by decide +kernel)

theorem f8001692e : fetchDecode img 0x8001692e = some (NoCompiler.Instr.opimm (NoCompiler.AluOp.add) 2 2 0xffffffe0#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1101) (by decide +kernel) (by decide +kernel)

theorem f80016930 : fetchDecode img 0x80016930 = some (NoCompiler.Instr.op (NoCompiler.AluOp.add) 12 0 11, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x862e) (by decide +kernel) (by decide +kernel)

theorem f80016932 : fetchDecode img 0x80016932 = some (NoCompiler.Instr.opimm (NoCompiler.AluOp.add) 11 0 0x00000008#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x45a1) (by decide +kernel) (by decide +kernel)

theorem f80016934 : fetchDecode img 0x80016934 = some (NoCompiler.Instr.store (NoCompiler.Width.b) 2 10 0x0000000f#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xa107a3) (by decide +kernel) (by decide +kernel)

theorem f80016938 : fetchDecode img 0x80016938 = some (NoCompiler.Instr.branch (NoCompiler.BrCond.geu) 10 11 0x00000008#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xb57463) (by decide +kernel) (by decide +kernel)

theorem f8001693c : fetchDecode img 0x8001693c = some (NoCompiler.Instr.opimm (NoCompiler.AluOp.add) 2 2 0x00000020#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x6105) (by decide +kernel) (by decide +kernel)

theorem f8001693e : fetchDecode img 0x8001693e = some (NoCompiler.Instr.jalr 0 1 0x00000000#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8082) (by decide +kernel) (by decide +kernel)

end NoCompiler.Rmk.RxFetch
