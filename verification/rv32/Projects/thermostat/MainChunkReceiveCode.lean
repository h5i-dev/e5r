-- Expected instructions generated from observation; Lean checks every byte against the ELF.
import Projects.thermostat.PackedFetch
namespace E5R.Thermostat
open E5R
theorem cr2147487628 : fetchDecode img 2147487628#32 = some (E5R.Instr.load (E5R.Width.w) true 11 8 0x00000070#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147487628#32 (by decide) (by decide) (bits := 0x0000582c#32) (by decide +kernel) (by decide +kernel)
theorem cr2147487630 : fetchDecode img 2147487630#32 = some (E5R.Instr.branch (E5R.BrCond.eq) 11 10 0x00000c22#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147487630#32 (by decide) (by decide) (bits := 0x42a581e3#32) (by decide +kernel) (by decide +kernel)
theorem cr2147487634 : fetchDecode img 2147487634#32 = some (E5R.Instr.branch (E5R.BrCond.ltu) 11 10 0x00000d72#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147487634#32 (by decide) (by decide) (bits := 0x56a5e9e3#32) (by decide +kernel) (by decide +kernel)
theorem cr2147487638 : fetchDecode img 2147487638#32 = some (E5R.Instr.load (E5R.Width.w) true 12 8 0x0000006c#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147487638#32 (by decide) (by decide) (bits := 0x00005470#32) (by decide +kernel) (by decide +kernel)
theorem cr2147487640 : fetchDecode img 2147487640#32 = some (E5R.Instr.load (E5R.Width.w) true 13 8 0x000001b8#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147487640#32 (by decide) (by decide) (bits := 0x1b842683#32) (by decide +kernel) (by decide +kernel)
theorem cr2147487644 : fetchDecode img 2147487644#32 = some (E5R.Instr.op (E5R.AluOp.sub) 11 11 10, 2#32) := by exact PackedFetch.fetchDecode_of 2147487644#32 (by decide) (by decide) (bits := 0x00008d89#32) (by decide +kernel) (by decide +kernel)
theorem cr2147487646 : fetchDecode img 2147487646#32 = some (E5R.Instr.op (E5R.AluOp.add) 10 10 12, 2#32) := by exact PackedFetch.fetchDecode_of 2147487646#32 (by decide) (by decide) (bits := 0x00009532#32) (by decide +kernel) (by decide +kernel)
theorem cr2147487648 : fetchDecode img 2147487648#32 = some (E5R.Instr.store (E5R.Width.w) 8 13 0x000001cc#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147487648#32 (by decide) (by decide) (bits := 0x1cd42623#32) (by decide +kernel) (by decide +kernel)
theorem cr2147487652 : fetchDecode img 2147487652#32 = some (E5R.Instr.store (E5R.Width.w) 8 10 0x000001d0#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147487652#32 (by decide) (by decide) (bits := 0x1ca42823#32) (by decide +kernel) (by decide +kernel)
theorem cr2147487656 : fetchDecode img 2147487656#32 = some (E5R.Instr.store (E5R.Width.w) 8 11 0x000001d4#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147487656#32 (by decide) (by decide) (bits := 0x1cb42a23#32) (by decide +kernel) (by decide +kernel)
theorem cr2147487660 : fetchDecode img 2147487660#32 = some (E5R.Instr.store (E5R.Width.b) 8 0 0x000001d8#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147487660#32 (by decide) (by decide) (bits := 0x1c040c23#32) (by decide +kernel) (by decide +kernel)
theorem cr2147487664 : fetchDecode img 2147487664#32 = some (E5R.Instr.load (E5R.Width.b) false 11 19 0x00000005#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147487664#32 (by decide) (by decide) (bits := 0x0059c583#32) (by decide +kernel) (by decide +kernel)
theorem cr2147487668 : fetchDecode img 2147487668#32 = some (E5R.Instr.opimm (E5R.AluOp.and) 11 11 0x00000001#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147487668#32 (by decide) (by decide) (bits := 0x00008985#32) (by decide +kernel) (by decide +kernel)
theorem cr2147487670 : fetchDecode img 2147487670#32 = some (E5R.Instr.branch (E5R.BrCond.ne) 11 0 0xfffffeca#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147487670#32 (by decide) (by decide) (bits := 0xec0595e3#32) (by decide +kernel) (by decide +kernel)
theorem cr2147487674 : fetchDecode img 2147487674#32 = some (E5R.Instr.fence, 4#32) := by exact PackedFetch.fetchDecode_of 2147487674#32 (by decide) (by decide) (bits := 0x0100000f#32) (by decide +kernel) (by decide +kernel)
theorem cr2147487678 : fetchDecode img 2147487678#32 = some (E5R.Instr.jal 0 0xfffffff2#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147487678#32 (by decide) (by decide) (bits := 0x0000bfcd#32) (by decide +kernel) (by decide +kernel)

end E5R.Thermostat
