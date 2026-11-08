-- Expected instructions generated from observation; Lean checks every byte against the ELF.
import Projects.thermostat.PackedFetch
namespace E5R.Thermostat
open E5R
theorem rp2147499592 : fetchDecode img 2147499592#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 10 0 0x00000001#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147499592#32 (by decide) (by decide) (bits := 0x00004505#32) (by decide +kernel) (by decide +kernel)
theorem rp2147499594 : fetchDecode img 2147499594#32 = some (E5R.Instr.op (E5R.AluOp.add) 11 0 12, 2#32) := by exact PackedFetch.fetchDecode_of 2147499594#32 (by decide) (by decide) (bits := 0x000085b2#32) (by decide +kernel) (by decide +kernel)
theorem rp2147499596 : fetchDecode img 2147499596#32 = some (E5R.Instr.jalr 0 1 0x00000000#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147499596#32 (by decide) (by decide) (bits := 0x00008082#32) (by decide +kernel) (by decide +kernel)

end E5R.Thermostat
