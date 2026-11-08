-- Expected instructions generated from observation; Lean checks every byte against the ELF.
import Projects.thermostat.PackedFetch
namespace E5R.Thermostat
open E5R
theorem tx2147485674 : fetchDecode img 2147485674#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 12 12 0x00000001#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147485674#32 (by decide) (by decide) (bits := 0x00000605#32) (by decide +kernel) (by decide +kernel)
theorem tx2147485676 : fetchDecode img 2147485676#32 = some (E5R.Instr.store (E5R.Width.b) 15 16 0x00000000#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485676#32 (by decide) (by decide) (bits := 0x01078023#32) (by decide +kernel) (by decide +kernel)
theorem tx2147485680 : fetchDecode img 2147485680#32 = some (E5R.Instr.branch (E5R.BrCond.eq) 12 14 0x0000001a#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485680#32 (by decide) (by decide) (bits := 0x00e60d63#32) (by decide +kernel) (by decide +kernel)
theorem tx2147485684 : fetchDecode img 2147485684#32 = some (E5R.Instr.load (E5R.Width.b) false 16 12 0x00000000#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485684#32 (by decide) (by decide) (bits := 0x00064803#32) (by decide +kernel) (by decide +kernel)

end E5R.Thermostat
