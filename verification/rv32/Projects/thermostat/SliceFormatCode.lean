-- Expected instructions generated from observation; Lean checks every byte against the ELF.
import Projects.thermostat.PackedFetch
namespace E5R.Thermostat
open E5R
theorem sf2147492492 : fetchDecode img 2147492492#32 = some (E5R.Instr.load (E5R.Width.w) true 12 10 0x00000000#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147492492#32 (by decide) (by decide) (bits := 0x00004110#32) (by decide +kernel) (by decide +kernel)
theorem sf2147492494 : fetchDecode img 2147492494#32 = some (E5R.Instr.load (E5R.Width.w) true 13 10 0x00000004#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147492494#32 (by decide) (by decide) (bits := 0x00004154#32) (by decide +kernel) (by decide +kernel)
theorem sf2147492496 : fetchDecode img 2147492496#32 = some (E5R.Instr.op (E5R.AluOp.add) 14 0 11, 2#32) := by exact PackedFetch.fetchDecode_of 2147492496#32 (by decide) (by decide) (bits := 0x0000872e#32) (by decide +kernel) (by decide +kernel)
theorem sf2147492498 : fetchDecode img 2147492498#32 = some (E5R.Instr.op (E5R.AluOp.add) 10 0 12, 2#32) := by exact PackedFetch.fetchDecode_of 2147492498#32 (by decide) (by decide) (bits := 0x00008532#32) (by decide +kernel) (by decide +kernel)
theorem sf2147492500 : fetchDecode img 2147492500#32 = some (E5R.Instr.op (E5R.AluOp.add) 11 0 13, 2#32) := by exact PackedFetch.fetchDecode_of 2147492500#32 (by decide) (by decide) (bits := 0x000085b6#32) (by decide +kernel) (by decide +kernel)
theorem sf2147492502 : fetchDecode img 2147492502#32 = some (E5R.Instr.op (E5R.AluOp.add) 12 0 14, 2#32) := by exact PackedFetch.fetchDecode_of 2147492502#32 (by decide) (by decide) (bits := 0x0000863a#32) (by decide +kernel) (by decide +kernel)
theorem sf2147492504 : fetchDecode img 2147492504#32 = some (E5R.Instr.auipc 6 0x00003000#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147492504#32 (by decide) (by decide) (bits := 0x00003317#32) (by decide +kernel) (by decide +kernel)
theorem sf2147492508 : fetchDecode img 2147492508#32 = some (E5R.Instr.jalr 0 6 0xfffffea6#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147492508#32 (by decide) (by decide) (bits := 0xea630067#32) (by decide +kernel) (by decide +kernel)
theorem sf2147504446 : fetchDecode img 2147504446#32 = some (E5R.Instr.op (E5R.AluOp.add) 13 0 11, 2#32) := by exact PackedFetch.fetchDecode_of 2147504446#32 (by decide) (by decide) (bits := 0x000086ae#32) (by decide +kernel) (by decide +kernel)
theorem sf2147504448 : fetchDecode img 2147504448#32 = some (E5R.Instr.op (E5R.AluOp.add) 11 0 10, 2#32) := by exact PackedFetch.fetchDecode_of 2147504448#32 (by decide) (by decide) (bits := 0x000085aa#32) (by decide +kernel) (by decide +kernel)
theorem sf2147504450 : fetchDecode img 2147504450#32 = some (E5R.Instr.op (E5R.AluOp.add) 10 0 12, 2#32) := by exact PackedFetch.fetchDecode_of 2147504450#32 (by decide) (by decide) (bits := 0x00008532#32) (by decide +kernel) (by decide +kernel)
theorem sf2147504452 : fetchDecode img 2147504452#32 = some (E5R.Instr.op (E5R.AluOp.add) 12 0 13, 2#32) := by exact PackedFetch.fetchDecode_of 2147504452#32 (by decide) (by decide) (bits := 0x00008636#32) (by decide +kernel) (by decide +kernel)
theorem sf2147504454 : fetchDecode img 2147504454#32 = some (E5R.Instr.auipc 6 0xfffff000#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147504454#32 (by decide) (by decide) (bits := 0xfffff317#32) (by decide +kernel) (by decide +kernel)
theorem sf2147504458 : fetchDecode img 2147504458#32 = some (E5R.Instr.jalr 0 6 0x0000064a#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147504458#32 (by decide) (by decide) (bits := 0x64a30067#32) (by decide +kernel) (by decide +kernel)

end E5R.Thermostat
