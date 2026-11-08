-- Expected instructions generated from observation; Lean checks every byte against the ELF.
import Projects.thermostat.PackedFetch
namespace E5R.Thermostat
open E5R
theorem er2147485266 : fetchDecode img 2147485266#32 = some (E5R.Instr.store (E5R.Width.b) 2 10 0x00000018#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485266#32 (by decide) (by decide) (bits := 0x00a10c23#32) (by decide +kernel) (by decide +kernel)
theorem er2147485270 : fetchDecode img 2147485270#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 10 2 0x00000018#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147485270#32 (by decide) (by decide) (bits := 0x00000828#32) (by decide +kernel) (by decide +kernel)
theorem er2147485272 : fetchDecode img 2147485272#32 = some (E5R.Instr.op (E5R.AluOp.add) 11 0 19, 2#32) := by exact PackedFetch.fetchDecode_of 2147485272#32 (by decide) (by decide) (bits := 0x000085ce#32) (by decide +kernel) (by decide +kernel)
theorem er2147485274 : fetchDecode img 2147485274#32 = some (E5R.Instr.op (E5R.AluOp.add) 12 0 18, 2#32) := by exact PackedFetch.fetchDecode_of 2147485274#32 (by decide) (by decide) (bits := 0x0000864a#32) (by decide +kernel) (by decide +kernel)
theorem er2147485276 : fetchDecode img 2147485276#32 = some (E5R.Instr.auipc 1 0x00001000#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485276#32 (by decide) (by decide) (bits := 0x00001097#32) (by decide +kernel) (by decide +kernel)
theorem er2147485280 : fetchDecode img 2147485280#32 = some (E5R.Instr.jalr 1 1 0x000007ee#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485280#32 (by decide) (by decide) (bits := 0x7ee080e7#32) (by decide +kernel) (by decide +kernel)
theorem er2147485284 : fetchDecode img 2147485284#32 = some (E5R.Instr.op (E5R.AluOp.add) 20 0 10, 2#32) := by exact PackedFetch.fetchDecode_of 2147485284#32 (by decide) (by decide) (bits := 0x00008a2a#32) (by decide +kernel) (by decide +kernel)
theorem er2147485286 : fetchDecode img 2147485286#32 = some (E5R.Instr.branch (E5R.BrCond.ltu) 18 11 0x00000006#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485286#32 (by decide) (by decide) (bits := 0x00b96363#32) (by decide +kernel) (by decide +kernel)
theorem er2147485290 : fetchDecode img 2147485290#32 = some (E5R.Instr.op (E5R.AluOp.add) 18 0 11, 2#32) := by exact PackedFetch.fetchDecode_of 2147485290#32 (by decide) (by decide) (bits := 0x0000892e#32) (by decide +kernel) (by decide +kernel)
theorem er2147485292 : fetchDecode img 2147485292#32 = some (E5R.Instr.lui 12 0x80005000#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485292#32 (by decide) (by decide) (bits := 0x80005637#32) (by decide +kernel) (by decide +kernel)
theorem er2147485296 : fetchDecode img 2147485296#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 12 12 0x000006a8#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485296#32 (by decide) (by decide) (bits := 0x6a860613#32) (by decide +kernel) (by decide +kernel)
theorem er2147485300 : fetchDecode img 2147485300#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 10 0 0x00000010#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147485300#32 (by decide) (by decide) (bits := 0x00004541#32) (by decide +kernel) (by decide +kernel)
theorem er2147485302 : fetchDecode img 2147485302#32 = some (E5R.Instr.jal 0 0xffffff36#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147485302#32 (by decide) (by decide) (bits := 0x0000bf1d#32) (by decide +kernel) (by decide +kernel)

end E5R.Thermostat
