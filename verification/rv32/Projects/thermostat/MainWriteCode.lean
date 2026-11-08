-- Expected instructions generated from observation; Lean checks every byte against the ELF.
import Projects.thermostat.PackedFetch
namespace E5R.Thermostat
open E5R
theorem mw2147490138 : fetchDecode img 2147490138#32 = some (E5R.Instr.lui 10 0x00001000#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147490138#32 (by decide) (by decide) (bits := 0x00006505#32) (by decide +kernel) (by decide +kernel)
theorem mw2147490140 : fetchDecode img 2147490140#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 10 10 0x000001a8#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147490140#32 (by decide) (by decide) (bits := 0x1a850513#32) (by decide +kernel) (by decide +kernel)
theorem mw2147490144 : fetchDecode img 2147490144#32 = some (E5R.Instr.op (E5R.AluOp.add) 10 10 2, 2#32) := by exact PackedFetch.fetchDecode_of 2147490144#32 (by decide) (by decide) (bits := 0x0000950a#32) (by decide +kernel) (by decide +kernel)
theorem mw2147490146 : fetchDecode img 2147490146#32 = some (E5R.Instr.op (E5R.AluOp.add) 11 0 24, 2#32) := by exact PackedFetch.fetchDecode_of 2147490146#32 (by decide) (by decide) (bits := 0x000085e2#32) (by decide +kernel) (by decide +kernel)
theorem mw2147490148 : fetchDecode img 2147490148#32 = some (E5R.Instr.auipc 1 0xfffff000#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147490148#32 (by decide) (by decide) (bits := 0xfffff097#32) (by decide +kernel) (by decide +kernel)
theorem mw2147490152 : fetchDecode img 2147490152#32 = some (E5R.Instr.jalr 1 1 0xfffffb62#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147490152#32 (by decide) (by decide) (bits := 0xb62080e7#32) (by decide +kernel) (by decide +kernel)
theorem mw2147490156 : fetchDecode img 2147490156#32 = some (E5R.Instr.load (E5R.Width.b) false 13 8 0x00000532#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147490156#32 (by decide) (by decide) (bits := 0x53244683#32) (by decide +kernel) (by decide +kernel)
theorem mw2147490160 : fetchDecode img 2147490160#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 9 0 0x00000004#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147490160#32 (by decide) (by decide) (bits := 0x00004491#32) (by decide +kernel) (by decide +kernel)
theorem mw2147490162 : fetchDecode img 2147490162#32 = some (E5R.Instr.branch (E5R.BrCond.ne) 13 18 0x00000026#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147490162#32 (by decide) (by decide) (bits := 0x03269363#32) (by decide +kernel) (by decide +kernel)
theorem mw2147490200 : fetchDecode img 2147490200#32 = some (E5R.Instr.load (E5R.Width.w) true 12 8 0x00000524#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147490200#32 (by decide) (by decide) (bits := 0x52442603#32) (by decide +kernel) (by decide +kernel)
theorem mw2147490204 : fetchDecode img 2147490204#32 = some (E5R.Instr.load (E5R.Width.w) true 11 8 0x00000528#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147490204#32 (by decide) (by decide) (bits := 0x52842583#32) (by decide +kernel) (by decide +kernel)
theorem mw2147490208 : fetchDecode img 2147490208#32 = some (E5R.Instr.load (E5R.Width.w) true 20 8 0x0000052c#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147490208#32 (by decide) (by decide) (bits := 0x52c42a03#32) (by decide +kernel) (by decide +kernel)
theorem mw2147490212 : fetchDecode img 2147490212#32 = some (E5R.Instr.load (E5R.Width.h) false 10 8 0x00000530#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147490212#32 (by decide) (by decide) (bits := 0x53045503#32) (by decide +kernel) (by decide +kernel)
theorem mw2147490216 : fetchDecode img 2147490216#32 = some (E5R.Instr.load (E5R.Width.b) false 6 8 0x00000533#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147490216#32 (by decide) (by decide) (bits := 0x53344303#32) (by decide +kernel) (by decide +kernel)
theorem mw2147490220 : fetchDecode img 2147490220#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 9 2 0x000007ff#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147490220#32 (by decide) (by decide) (bits := 0x7ff10493#32) (by decide +kernel) (by decide +kernel)
theorem mw2147490224 : fetchDecode img 2147490224#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 9 9 0x000004e9#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147490224#32 (by decide) (by decide) (bits := 0x4e948493#32) (by decide +kernel) (by decide +kernel)
theorem mw2147490228 : fetchDecode img 2147490228#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 24 0 0xfffffffe#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147490228#32 (by decide) (by decide) (bits := 0x00005c79#32) (by decide +kernel) (by decide +kernel)
theorem mw2147490230 : fetchDecode img 2147490230#32 = some (E5R.Instr.jal 0 0xfffffd5a#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147490230#32 (by decide) (by decide) (bits := 0x0000bba9#32) (by decide +kernel) (by decide +kernel)

end E5R.Thermostat
