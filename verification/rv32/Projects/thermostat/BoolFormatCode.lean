-- Expected instructions generated from observation; Lean checks every byte against the ELF.
import Projects.thermostat.PackedFetch
namespace E5R.Thermostat
open E5R
theorem bf2147504402 : fetchDecode img 2147504402#32 = some (E5R.Instr.load (E5R.Width.b) false 12 10 0x00000000#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147504402#32 (by decide) (by decide) (bits := 0x00054603#32) (by decide +kernel) (by decide +kernel)
theorem bf2147504406 : fetchDecode img 2147504406#32 = some (E5R.Instr.op (E5R.AluOp.add) 10 0 11, 2#32) := by exact PackedFetch.fetchDecode_of 2147504406#32 (by decide) (by decide) (bits := 0x0000852e#32) (by decide +kernel) (by decide +kernel)
theorem bf2147504408 : fetchDecode img 2147504408#32 = some (E5R.Instr.branch (E5R.BrCond.eq) 12 0 0x00000014#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147504408#32 (by decide) (by decide) (bits := 0x0000ca11#32) (by decide +kernel) (by decide +kernel)
theorem bf2147504410 : fetchDecode img 2147504410#32 = some (E5R.Instr.lui 11 0x80006000#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147504410#32 (by decide) (by decide) (bits := 0x800065b7#32) (by decide +kernel) (by decide +kernel)
theorem bf2147504414 : fetchDecode img 2147504414#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 11 11 0xfffffbfc#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147504414#32 (by decide) (by decide) (bits := 0xbfc58593#32) (by decide +kernel) (by decide +kernel)
theorem bf2147504418 : fetchDecode img 2147504418#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 12 0 0x00000004#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147504418#32 (by decide) (by decide) (bits := 0x00004611#32) (by decide +kernel) (by decide +kernel)
theorem bf2147504420 : fetchDecode img 2147504420#32 = some (E5R.Instr.auipc 6 0xfffff000#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147504420#32 (by decide) (by decide) (bits := 0xfffff317#32) (by decide +kernel) (by decide +kernel)
theorem bf2147504424 : fetchDecode img 2147504424#32 = some (E5R.Instr.jalr 0 6 0x0000066c#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147504424#32 (by decide) (by decide) (bits := 0x66c30067#32) (by decide +kernel) (by decide +kernel)
theorem bf2147504428 : fetchDecode img 2147504428#32 = some (E5R.Instr.lui 11 0x80006000#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147504428#32 (by decide) (by decide) (bits := 0x800065b7#32) (by decide +kernel) (by decide +kernel)
theorem bf2147504432 : fetchDecode img 2147504432#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 11 11 0xfffffefb#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147504432#32 (by decide) (by decide) (bits := 0xefb58593#32) (by decide +kernel) (by decide +kernel)
theorem bf2147504436 : fetchDecode img 2147504436#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 12 0 0x00000005#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147504436#32 (by decide) (by decide) (bits := 0x00004615#32) (by decide +kernel) (by decide +kernel)
theorem bf2147504438 : fetchDecode img 2147504438#32 = some (E5R.Instr.auipc 6 0xfffff000#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147504438#32 (by decide) (by decide) (bits := 0xfffff317#32) (by decide +kernel) (by decide +kernel)
theorem bf2147504442 : fetchDecode img 2147504442#32 = some (E5R.Instr.jalr 0 6 0x0000065a#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147504442#32 (by decide) (by decide) (bits := 0x65a30067#32) (by decide +kernel) (by decide +kernel)

end E5R.Thermostat
