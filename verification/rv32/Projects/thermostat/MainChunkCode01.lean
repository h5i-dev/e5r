-- Observed instructions; kernel checked against the pinned ELF.
import Projects.thermostat.PackedFetch
namespace E5R.Thermostat
open E5R
theorem cc2147487582 : fetchDecode img 2147487582#32 = some (E5R.Instr.store (E5R.Width.w) 8 24 0x000001c4#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147487582#32 (by decide) (by decide) (bits := 0x1d842223#32) (by decide +kernel) (by decide +kernel)
theorem cc2147487586 : fetchDecode img 2147487586#32 = some (E5R.Instr.branch (E5R.BrCond.ge) 0 10 0xffffff38#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147487586#32 (by decide) (by decide) (bits := 0xf2a05ce3#32) (by decide +kernel) (by decide +kernel)
theorem cc2147487590 : fetchDecode img 2147487590#32 = some (E5R.Instr.branch (E5R.BrCond.ne) 10 22 0x00000106#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147487590#32 (by decide) (by decide) (bits := 0x11651363#32) (by decide +kernel) (by decide +kernel)
theorem cc2147487594 : fetchDecode img 2147487594#32 = some (E5R.Instr.load (E5R.Width.w) true 10 8 0x000001c8#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147487594#32 (by decide) (by decide) (bits := 0x1c842503#32) (by decide +kernel) (by decide +kernel)
theorem cc2147487598 : fetchDecode img 2147487598#32 = some (E5R.Instr.load (E5R.Width.w) true 11 8 0x00000070#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147487598#32 (by decide) (by decide) (bits := 0x0000582c#32) (by decide +kernel) (by decide +kernel)
theorem cc2147487600 : fetchDecode img 2147487600#32 = some (E5R.Instr.branch (E5R.BrCond.geu) 10 11 0x00000dd8#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147487600#32 (by decide) (by decide) (bits := 0x5cb57ce3#32) (by decide +kernel) (by decide +kernel)
theorem cc2147487604 : fetchDecode img 2147487604#32 = some (E5R.Instr.load (E5R.Width.w) true 11 8 0x0000006c#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147487604#32 (by decide) (by decide) (bits := 0x0000546c#32) (by decide +kernel) (by decide +kernel)
theorem cc2147487606 : fetchDecode img 2147487606#32 = some (E5R.Instr.op (E5R.AluOp.add) 10 10 11, 2#32) := by exact PackedFetch.fetchDecode_of 2147487606#32 (by decide) (by decide) (bits := 0x0000952e#32) (by decide +kernel) (by decide +kernel)
theorem cc2147487608 : fetchDecode img 2147487608#32 = some (E5R.Instr.store (E5R.Width.b) 10 20 0x00000000#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147487608#32 (by decide) (by decide) (bits := 0x01450023#32) (by decide +kernel) (by decide +kernel)
theorem cc2147487612 : fetchDecode img 2147487612#32 = some (E5R.Instr.load (E5R.Width.w) true 10 8 0x000001c8#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147487612#32 (by decide) (by decide) (bits := 0x1c842503#32) (by decide +kernel) (by decide +kernel)
theorem cc2147487616 : fetchDecode img 2147487616#32 = some (E5R.Instr.load (E5R.Width.w) true 24 8 0x000001c4#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147487616#32 (by decide) (by decide) (bits := 0x1c442c03#32) (by decide +kernel) (by decide +kernel)
theorem cc2147487620 : fetchDecode img 2147487620#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 10 10 0x00000001#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147487620#32 (by decide) (by decide) (bits := 0x00000505#32) (by decide +kernel) (by decide +kernel)
theorem cc2147487622 : fetchDecode img 2147487622#32 = some (E5R.Instr.store (E5R.Width.w) 8 10 0x000001c8#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147487622#32 (by decide) (by decide) (bits := 0x1ca42423#32) (by decide +kernel) (by decide +kernel)
theorem cc2147487626 : fetchDecode img 2147487626#32 = some (E5R.Instr.jal 0 0xffffff10#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147487626#32 (by decide) (by decide) (bits := 0x0000bf01#32) (by decide +kernel) (by decide +kernel)
end E5R.Thermostat
