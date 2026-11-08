-- Expected instructions generated from observation; Lean checks every byte against the ELF.
import Projects.thermostat.PackedFetch
namespace E5R.Thermostat
open E5R
theorem be2147484994 : fetchDecode img 2147484994#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 22 0 0x00000001#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147484994#32 (by decide) (by decide) (bits := 0x00004b05#32) (by decide +kernel) (by decide +kernel)
theorem be2147484996 : fetchDecode img 2147484996#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 20 0 0x00000191#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147484996#32 (by decide) (by decide) (bits := 0x19100a13#32) (by decide +kernel) (by decide +kernel)
theorem be2147485000 : fetchDecode img 2147485000#32 = some (E5R.Instr.branch (E5R.BrCond.eq) 10 0 0x00000060#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147485000#32 (by decide) (by decide) (bits := 0x0000c125#32) (by decide +kernel) (by decide +kernel)
theorem be2147485002 : fetchDecode img 2147485002#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 12 0 0x00000007#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147485002#32 (by decide) (by decide) (bits := 0x0000461d#32) (by decide +kernel) (by decide +kernel)
theorem be2147485004 : fetchDecode img 2147485004#32 = some (E5R.Instr.branch (E5R.BrCond.ltu) 11 12 0x00000056#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485004#32 (by decide) (by decide) (bits := 0x04c5eb63#32) (by decide +kernel) (by decide +kernel)
theorem be2147485008 : fetchDecode img 2147485008#32 = some (E5R.Instr.op (E5R.AluOp.add) 25 0 11, 2#32) := by exact PackedFetch.fetchDecode_of 2147485008#32 (by decide) (by decide) (bits := 0x00008cae#32) (by decide +kernel) (by decide +kernel)
theorem be2147485010 : fetchDecode img 2147485010#32 = some (E5R.Instr.lui 11 0x80006000#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485010#32 (by decide) (by decide) (bits := 0x800065b7#32) (by decide +kernel) (by decide +kernel)
theorem be2147485014 : fetchDecode img 2147485014#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 11 11 0xfffffb75#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485014#32 (by decide) (by decide) (bits := 0xb7558593#32) (by decide +kernel) (by decide +kernel)
theorem be2147485018 : fetchDecode img 2147485018#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 12 0 0x00000007#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147485018#32 (by decide) (by decide) (bits := 0x0000461d#32) (by decide +kernel) (by decide +kernel)
theorem be2147485020 : fetchDecode img 2147485020#32 = some (E5R.Instr.op (E5R.AluOp.add) 24 0 10, 2#32) := by exact PackedFetch.fetchDecode_of 2147485020#32 (by decide) (by decide) (bits := 0x00008c2a#32) (by decide +kernel) (by decide +kernel)
theorem be2147485022 : fetchDecode img 2147485022#32 = some (E5R.Instr.auipc 1 0x00005000#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485022#32 (by decide) (by decide) (bits := 0x00005097#32) (by decide +kernel) (by decide +kernel)
theorem be2147485026 : fetchDecode img 2147485026#32 = some (E5R.Instr.jalr 1 1 0xfffffc04#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485026#32 (by decide) (by decide) (bits := 0xc04080e7#32) (by decide +kernel) (by decide +kernel)
theorem be2147485030 : fetchDecode img 2147485030#32 = some (E5R.Instr.branch (E5R.BrCond.ne) 10 0 0x0000003c#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147485030#32 (by decide) (by decide) (bits := 0x0000ed15#32) (by decide +kernel) (by decide +kernel)

end E5R.Thermostat
