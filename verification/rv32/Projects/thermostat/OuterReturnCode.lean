-- Expected instructions generated from observation; Lean checks every byte against the ELF.
import Projects.thermostat.PackedFetch
namespace E5R.Thermostat
open E5R
theorem ep2147485124 : fetchDecode img 2147485124#32 = some (E5R.Instr.load (E5R.Width.w) true 1 2 0x0000005c#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147485124#32 (by decide) (by decide) (bits := 0x000040f6#32) (by decide +kernel) (by decide +kernel)
theorem ep2147485126 : fetchDecode img 2147485126#32 = some (E5R.Instr.load (E5R.Width.w) true 8 2 0x00000058#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147485126#32 (by decide) (by decide) (bits := 0x00004466#32) (by decide +kernel) (by decide +kernel)
theorem ep2147485128 : fetchDecode img 2147485128#32 = some (E5R.Instr.load (E5R.Width.w) true 9 2 0x00000054#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147485128#32 (by decide) (by decide) (bits := 0x000044d6#32) (by decide +kernel) (by decide +kernel)
theorem ep2147485130 : fetchDecode img 2147485130#32 = some (E5R.Instr.load (E5R.Width.w) true 18 2 0x00000050#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147485130#32 (by decide) (by decide) (bits := 0x00004946#32) (by decide +kernel) (by decide +kernel)
theorem ep2147485132 : fetchDecode img 2147485132#32 = some (E5R.Instr.load (E5R.Width.w) true 19 2 0x0000004c#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147485132#32 (by decide) (by decide) (bits := 0x000049b6#32) (by decide +kernel) (by decide +kernel)
theorem ep2147485134 : fetchDecode img 2147485134#32 = some (E5R.Instr.load (E5R.Width.w) true 20 2 0x00000048#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147485134#32 (by decide) (by decide) (bits := 0x00004a26#32) (by decide +kernel) (by decide +kernel)
theorem ep2147485136 : fetchDecode img 2147485136#32 = some (E5R.Instr.load (E5R.Width.w) true 21 2 0x00000044#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147485136#32 (by decide) (by decide) (bits := 0x00004a96#32) (by decide +kernel) (by decide +kernel)
theorem ep2147485138 : fetchDecode img 2147485138#32 = some (E5R.Instr.load (E5R.Width.w) true 22 2 0x00000040#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147485138#32 (by decide) (by decide) (bits := 0x00004b06#32) (by decide +kernel) (by decide +kernel)
theorem ep2147485140 : fetchDecode img 2147485140#32 = some (E5R.Instr.load (E5R.Width.w) true 23 2 0x0000003c#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147485140#32 (by decide) (by decide) (bits := 0x00005bf2#32) (by decide +kernel) (by decide +kernel)
theorem ep2147485142 : fetchDecode img 2147485142#32 = some (E5R.Instr.load (E5R.Width.w) true 24 2 0x00000038#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147485142#32 (by decide) (by decide) (bits := 0x00005c62#32) (by decide +kernel) (by decide +kernel)
theorem ep2147485144 : fetchDecode img 2147485144#32 = some (E5R.Instr.load (E5R.Width.w) true 25 2 0x00000034#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147485144#32 (by decide) (by decide) (bits := 0x00005cd2#32) (by decide +kernel) (by decide +kernel)
theorem ep2147485146 : fetchDecode img 2147485146#32 = some (E5R.Instr.load (E5R.Width.w) true 26 2 0x00000030#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147485146#32 (by decide) (by decide) (bits := 0x00005d42#32) (by decide +kernel) (by decide +kernel)
theorem ep2147485148 : fetchDecode img 2147485148#32 = some (E5R.Instr.load (E5R.Width.w) true 27 2 0x0000002c#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147485148#32 (by decide) (by decide) (bits := 0x00005db2#32) (by decide +kernel) (by decide +kernel)
theorem ep2147485150 : fetchDecode img 2147485150#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 2 2 0x00000060#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147485150#32 (by decide) (by decide) (bits := 0x00006125#32) (by decide +kernel) (by decide +kernel)
theorem ep2147485152 : fetchDecode img 2147485152#32 = some (E5R.Instr.jalr 0 1 0x00000000#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147485152#32 (by decide) (by decide) (bits := 0x00008082#32) (by decide +kernel) (by decide +kernel)

end E5R.Thermostat
