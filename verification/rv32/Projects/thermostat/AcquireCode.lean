-- Expected instructions generated from observation; Lean checks every byte against the ELF.
import Projects.thermostat.PackedFetch
namespace E5R.Thermostat
open E5R
theorem ac2147485204 : fetchDecode img 2147485204#32 = some (E5R.Instr.load (E5R.Width.w) true 10 23 0x00000000#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485204#32 (by decide) (by decide) (bits := 0x000ba503#32) (by decide +kernel) (by decide +kernel)
theorem ac2147485208 : fetchDecode img 2147485208#32 = some (E5R.Instr.branch (E5R.BrCond.ne) 10 0 0x0000014e#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485208#32 (by decide) (by decide) (bits := 0x14051763#32) (by decide +kernel) (by decide +kernel)
theorem ac2147485212 : fetchDecode img 2147485212#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 10 0 0xffffffff#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147485212#32 (by decide) (by decide) (bits := 0x0000557d#32) (by decide +kernel) (by decide +kernel)
theorem ac2147485214 : fetchDecode img 2147485214#32 = some (E5R.Instr.store (E5R.Width.w) 23 10 0x00000000#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485214#32 (by decide) (by decide) (bits := 0x00aba023#32) (by decide +kernel) (by decide +kernel)

end E5R.Thermostat
