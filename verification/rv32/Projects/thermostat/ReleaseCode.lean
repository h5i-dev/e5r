-- Expected instructions generated from observation; Lean checks every byte against the ELF.
import Projects.thermostat.PackedFetch
namespace E5R.Thermostat
open E5R
theorem u2147485256 : fetchDecode img 2147485256#32 = some (E5R.Instr.load (E5R.Width.w) true 11 23 0x00000000#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485256#32 (by decide) (by decide) (bits := 0x000ba583#32) (by decide +kernel) (by decide +kernel)
theorem u2147485260 : fetchDecode img 2147485260#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 11 11 0x00000001#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147485260#32 (by decide) (by decide) (bits := 0x00000585#32) (by decide +kernel) (by decide +kernel)
theorem u2147485262 : fetchDecode img 2147485262#32 = some (E5R.Instr.store (E5R.Width.w) 23 11 0x00000000#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485262#32 (by decide) (by decide) (bits := 0x00bba023#32) (by decide +kernel) (by decide +kernel)

end E5R.Thermostat
