-- Expected instructions generated from observation; Lean checks every byte against the ELF.
import Projects.thermostat.PackedFetch
namespace E5R.Thermostat
open E5R
theorem rf2147485090 : fetchDecode img 2147485090#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 18 0 0x00000000#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147485090#32 (by decide) (by decide) (bits := 0x00004901#32) (by decide +kernel) (by decide +kernel)
theorem rf2147485092 : fetchDecode img 2147485092#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 10 0 0x00000000#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147485092#32 (by decide) (by decide) (bits := 0x00004501#32) (by decide +kernel) (by decide +kernel)
theorem rf2147485094 : fetchDecode img 2147485094#32 = some (E5R.Instr.jal 0 0x00000004#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147485094#32 (by decide) (by decide) (bits := 0x0000a011#32) (by decide +kernel) (by decide +kernel)
theorem rf2147485096 : fetchDecode img 2147485096#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 18 0 0x00000000#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147485096#32 (by decide) (by decide) (bits := 0x00004901#32) (by decide +kernel) (by decide +kernel)

end E5R.Thermostat
