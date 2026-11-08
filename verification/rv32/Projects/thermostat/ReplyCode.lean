-- Expected instructions generated from observation; Lean checks every byte against the ELF.
import Projects.thermostat.PackedFetch
namespace E5R.Thermostat
open E5R
theorem v2147485468 : fetchDecode img 2147485468#32 = some (E5R.Instr.store (E5R.Width.h) 2 27 0x0000001e#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485468#32 (by decide) (by decide) (bits := 0x01b11f23#32) (by decide +kernel) (by decide +kernel)
theorem v2147485472 : fetchDecode img 2147485472#32 = some (E5R.Instr.store (E5R.Width.h) 2 25 0x00000020#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485472#32 (by decide) (by decide) (bits := 0x03911023#32) (by decide +kernel) (by decide +kernel)
theorem v2147485476 : fetchDecode img 2147485476#32 = some (E5R.Instr.store (E5R.Width.b) 2 21 0x00000018#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485476#32 (by decide) (by decide) (bits := 0x01510c23#32) (by decide +kernel) (by decide +kernel)
theorem v2147485480 : fetchDecode img 2147485480#32 = some (E5R.Instr.store (E5R.Width.b) 2 24 0x00000019#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485480#32 (by decide) (by decide) (bits := 0x01810ca3#32) (by decide +kernel) (by decide +kernel)
theorem v2147485484 : fetchDecode img 2147485484#32 = some (E5R.Instr.load (E5R.Width.w) true 10 2 0x00000004#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147485484#32 (by decide) (by decide) (bits := 0x00004512#32) (by decide +kernel) (by decide +kernel)
theorem v2147485486 : fetchDecode img 2147485486#32 = some (E5R.Instr.store (E5R.Width.h) 2 10 0x0000001a#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485486#32 (by decide) (by decide) (bits := 0x00a11d23#32) (by decide +kernel) (by decide +kernel)
theorem v2147485490 : fetchDecode img 2147485490#32 = some (E5R.Instr.store (E5R.Width.h) 2 26 0x0000001c#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485490#32 (by decide) (by decide) (bits := 0x01a11e23#32) (by decide +kernel) (by decide +kernel)

end E5R.Thermostat
