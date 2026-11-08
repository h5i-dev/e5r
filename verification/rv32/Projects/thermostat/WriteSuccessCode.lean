-- Expected instructions generated from observation; Lean checks every byte against the ELF.
import Projects.thermostat.PackedFetch
namespace E5R.Thermostat
open E5R
theorem ws2147485494 : fetchDecode img 2147485494#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 10 2 0x00000018#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147485494#32 (by decide) (by decide) (bits := 0x00000828#32) (by decide +kernel) (by decide +kernel)
theorem ws2147485496 : fetchDecode img 2147485496#32 = some (E5R.Instr.op (E5R.AluOp.add) 11 0 19, 2#32) := by exact PackedFetch.fetchDecode_of 2147485496#32 (by decide) (by decide) (bits := 0x000085ce#32) (by decide +kernel) (by decide +kernel)
theorem ws2147485498 : fetchDecode img 2147485498#32 = some (E5R.Instr.op (E5R.AluOp.add) 12 0 18, 2#32) := by exact PackedFetch.fetchDecode_of 2147485498#32 (by decide) (by decide) (bits := 0x0000864a#32) (by decide +kernel) (by decide +kernel)
theorem ws2147485500 : fetchDecode img 2147485500#32 = some (E5R.Instr.auipc 1 0x00001000#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485500#32 (by decide) (by decide) (bits := 0x00001097#32) (by decide +kernel) (by decide +kernel)
theorem ws2147485504 : fetchDecode img 2147485504#32 = some (E5R.Instr.jalr 1 1 0x0000077c#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485504#32 (by decide) (by decide) (bits := 0x77c080e7#32) (by decide +kernel) (by decide +kernel)
theorem ws2147485508 : fetchDecode img 2147485508#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 12 0 0x00000001#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147485508#32 (by decide) (by decide) (bits := 0x00004605#32) (by decide +kernel) (by decide +kernel)
theorem ws2147485510 : fetchDecode img 2147485510#32 = some (E5R.Instr.branch (E5R.BrCond.ne) 10 12 0x00000016#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485510#32 (by decide) (by decide) (bits := 0x00c51b63#32) (by decide +kernel) (by decide +kernel)
theorem ws2147485514 : fetchDecode img 2147485514#32 = some (E5R.Instr.op (E5R.AluOp.add) 18 0 11, 2#32) := by exact PackedFetch.fetchDecode_of 2147485514#32 (by decide) (by decide) (bits := 0x0000892e#32) (by decide +kernel) (by decide +kernel)
theorem ws2147485516 : fetchDecode img 2147485516#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 10 0 0x00000010#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147485516#32 (by decide) (by decide) (bits := 0x00004541#32) (by decide +kernel) (by decide +kernel)
theorem ws2147485518 : fetchDecode img 2147485518#32 = some (E5R.Instr.lui 12 0x80005000#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485518#32 (by decide) (by decide) (bits := 0x80005637#32) (by decide +kernel) (by decide +kernel)
theorem ws2147485522 : fetchDecode img 2147485522#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 12 12 0x000006a8#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485522#32 (by decide) (by decide) (bits := 0x6a860613#32) (by decide +kernel) (by decide +kernel)
theorem ws2147485526 : fetchDecode img 2147485526#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 20 0 0x000000c8#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485526#32 (by decide) (by decide) (bits := 0x0c800a13#32) (by decide +kernel) (by decide +kernel)
theorem ws2147485530 : fetchDecode img 2147485530#32 = some (E5R.Instr.jal 0 0xfffffe52#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147485530#32 (by decide) (by decide) (bits := 0x0000bd89#32) (by decide +kernel) (by decide +kernel)
theorem ws2147485532 : fetchDecode img 2147485532#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 10 0 0x00000000#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147485532#32 (by decide) (by decide) (bits := 0x00004501#32) (by decide +kernel) (by decide +kernel)
theorem ws2147485534 : fetchDecode img 2147485534#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 18 0 0x00000000#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147485534#32 (by decide) (by decide) (bits := 0x00004901#32) (by decide +kernel) (by decide +kernel)
theorem ws2147485536 : fetchDecode img 2147485536#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 20 0 0x000001f4#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485536#32 (by decide) (by decide) (bits := 0x1f400a13#32) (by decide +kernel) (by decide +kernel)
theorem ws2147485540 : fetchDecode img 2147485540#32 = some (E5R.Instr.jal 0 0xfffffe48#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147485540#32 (by decide) (by decide) (bits := 0x0000b5a1#32) (by decide +kernel) (by decide +kernel)

end E5R.Thermostat
