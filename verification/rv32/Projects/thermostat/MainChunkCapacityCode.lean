-- Expected instructions generated from observation; Lean checks every byte against the ELF.
import Projects.thermostat.PackedFetch
namespace E5R.Thermostat
open E5R
theorem cf2147490736 : fetchDecode img 2147490736#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 18 0 0x00000000#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147490736#32 (by decide) (by decide) (bits := 0x00004901#32) (by decide +kernel) (by decide +kernel)
theorem cf2147490738 : fetchDecode img 2147490738#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 9 0 0x00000003#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147490738#32 (by decide) (by decide) (bits := 0x0000448d#32) (by decide +kernel) (by decide +kernel)
theorem cf2147490740 : fetchDecode img 2147490740#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 27 0 0x0000019d#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147490740#32 (by decide) (by decide) (bits := 0x19d00d93#32) (by decide +kernel) (by decide +kernel)
theorem cf2147490744 : fetchDecode img 2147490744#32 = some (E5R.Instr.jal 0 0xffffeee2#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147490744#32 (by decide) (by decide) (bits := 0xee3fe06f#32) (by decide +kernel) (by decide +kernel)

end E5R.Thermostat
