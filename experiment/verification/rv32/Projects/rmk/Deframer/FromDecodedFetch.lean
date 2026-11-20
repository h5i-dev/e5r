/-
  Instruction facts for `rmk_types::protocol::rynk::message::RynkMessage::from_decoded`
  (0x8001c3c6..0x8001c3ec), the call the session makes after `park_pending`, in the pinned RMK
  image, generated from the model's own decoder (/dev/shm generator, the `fetchDecode_of` form of
  Projects/rmk/Deframer/TailFetch.lean) and checked by the kernel against the packed ELF.

  Original nocompiler code, Apache-2.0. Regenerate rather than edit by hand.
-/
import Projects.rmk.Fetch

set_option maxRecDepth 100000

namespace NoCompiler.Rmk.FromDecodedFetch
open NoCompiler NoCompiler.Rmk

theorem f8001c3c6 : fetchDecode img 0x8001c3c6 = some (NoCompiler.Instr.opimm (NoCompiler.AluOp.add) 14 0 0x00000003#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x470d) (by decide +kernel) (by decide +kernel)

theorem f8001c3c8 : fetchDecode img 0x8001c3c8 = some (NoCompiler.Instr.branch (NoCompiler.BrCond.ltu) 12 14 0x00000024#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x2e66263) (by decide +kernel) (by decide +kernel)

theorem f8001c3cc : fetchDecode img 0x8001c3cc = some (NoCompiler.Instr.load (NoCompiler.Width.b) false 14 11 0x00000001#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x15c703) (by decide +kernel) (by decide +kernel)

theorem f8001c3d0 : fetchDecode img 0x8001c3d0 = some (NoCompiler.Instr.load (NoCompiler.Width.b) false 15 11 0x00000000#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x5c783) (by decide +kernel) (by decide +kernel)

theorem f8001c3d4 : fetchDecode img 0x8001c3d4 = some (NoCompiler.Instr.load (NoCompiler.Width.b) false 16 11 0x00000002#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x25c803) (by decide +kernel) (by decide +kernel)

theorem f8001c3d8 : fetchDecode img 0x8001c3d8 = some (NoCompiler.Instr.opimm (NoCompiler.AluOp.sll) 14 14 0x00000008#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x722) (by decide +kernel) (by decide +kernel)

theorem f8001c3da : fetchDecode img 0x8001c3da = some (NoCompiler.Instr.op (NoCompiler.AluOp.or) 14 14 15, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8f5d) (by decide +kernel) (by decide +kernel)

theorem f8001c3dc : fetchDecode img 0x8001c3dc = some (NoCompiler.Instr.store (NoCompiler.Width.w) 10 11 0x00000000#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc10c) (by decide +kernel) (by decide +kernel)

theorem f8001c3de : fetchDecode img 0x8001c3de = some (NoCompiler.Instr.store (NoCompiler.Width.w) 10 12 0x00000004#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc150) (by decide +kernel) (by decide +kernel)

theorem f8001c3e0 : fetchDecode img 0x8001c3e0 = some (NoCompiler.Instr.store (NoCompiler.Width.h) 10 14 0x00000008#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xe51423) (by decide +kernel) (by decide +kernel)

theorem f8001c3e4 : fetchDecode img 0x8001c3e4 = some (NoCompiler.Instr.store (NoCompiler.Width.b) 10 16 0x0000000a#32, 0x00000004#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x1050523) (by decide +kernel) (by decide +kernel)

theorem f8001c3e8 : fetchDecode img 0x8001c3e8 = some (NoCompiler.Instr.store (NoCompiler.Width.w) 10 13 0x0000000c#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0xc554) (by decide +kernel) (by decide +kernel)

theorem f8001c3ea : fetchDecode img 0x8001c3ea = some (NoCompiler.Instr.jalr 0 1 0x00000000#32, 0x00000002#32) :=
  fetchDecode_of _ (by decide) (by decide) (bits := 0x8082) (by decide +kernel) (by decide +kernel)

end NoCompiler.Rmk.FromDecodedFetch
