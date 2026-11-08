-- Expected instructions generated from observation; Lean checks every byte against the ELF.
import Projects.thermostat.PackedFetch
namespace E5R.Thermostat
open E5R
theorem snc2147489650 : fetchDecode img 2147489650#32 = some (E5R.Instr.lui 10 0x00001000#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147489650#32 (by decide) (by decide) (bits := 0x00006505#32) (by decide +kernel) (by decide +kernel)
theorem snc2147489652 : fetchDecode img 2147489652#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 10 10 0x000001a8#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147489652#32 (by decide) (by decide) (bits := 0x1a850513#32) (by decide +kernel) (by decide +kernel)
theorem snc2147489656 : fetchDecode img 2147489656#32 = some (E5R.Instr.op (E5R.AluOp.add) 10 10 2, 2#32) := by exact PackedFetch.fetchDecode_of 2147489656#32 (by decide) (by decide) (bits := 0x0000950a#32) (by decide +kernel) (by decide +kernel)
theorem snc2147489658 : fetchDecode img 2147489658#32 = some (E5R.Instr.op (E5R.AluOp.add) 11 0 9, 2#32) := by exact PackedFetch.fetchDecode_of 2147489658#32 (by decide) (by decide) (bits := 0x000085a6#32) (by decide +kernel) (by decide +kernel)
theorem snc2147489660 : fetchDecode img 2147489660#32 = some (E5R.Instr.auipc 1 0xfffff000#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147489660#32 (by decide) (by decide) (bits := 0xfffff097#32) (by decide +kernel) (by decide +kernel)
theorem snc2147489664 : fetchDecode img 2147489664#32 = some (E5R.Instr.jalr 1 1 0xfffffb92#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147489664#32 (by decide) (by decide) (bits := 0xb92080e7#32) (by decide +kernel) (by decide +kernel)

end E5R.Thermostat
