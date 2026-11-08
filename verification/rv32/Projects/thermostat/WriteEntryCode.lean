-- Expected instructions generated from observation; Lean checks every byte against the ELF.
import Projects.thermostat.PackedFetch
namespace E5R.Thermostat
open E5R
theorem we2147485154 : fetchDecode img 2147485154#32 = some (E5R.Instr.load (E5R.Width.b) false 10 23 0x00000018#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485154#32 (by decide) (by decide) (bits := 0x018bc503#32) (by decide +kernel) (by decide +kernel)
theorem we2147485158 : fetchDecode img 2147485158#32 = some (E5R.Instr.store (E5R.Width.b) 2 10 0x00000009#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485158#32 (by decide) (by decide) (bits := 0x00a104a3#32) (by decide +kernel) (by decide +kernel)
theorem we2147485162 : fetchDecode img 2147485162#32 = some (E5R.Instr.op (E5R.AluOp.add) 10 0 21, 2#32) := by exact PackedFetch.fetchDecode_of 2147485162#32 (by decide) (by decide) (bits := 0x00008556#32) (by decide +kernel) (by decide +kernel)
theorem we2147485164 : fetchDecode img 2147485164#32 = some (E5R.Instr.auipc 1 0x00002000#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485164#32 (by decide) (by decide) (bits := 0x00002097#32) (by decide +kernel) (by decide +kernel)
theorem we2147485168 : fetchDecode img 2147485168#32 = some (E5R.Instr.jalr 1 1 0xfffff982#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485168#32 (by decide) (by decide) (bits := 0x982080e7#32) (by decide +kernel) (by decide +kernel)

end E5R.Thermostat
