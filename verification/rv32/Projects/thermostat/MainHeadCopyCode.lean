-- Actual main Head copy and framing dispatch, checked against the pinned ELF.
import Projects.thermostat.PackedFetch
namespace E5R.Thermostat
open E5R
theorem hc2147486710 : fetchDecode img 2147486710#32 = some (E5R.Instr.lui 10 0x00001000#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147486710#32 (by decide) (by decide) (bits := 0x00006505#32) (by decide +kernel) (by decide +kernel)
theorem hc2147486712 : fetchDecode img 2147486712#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 10 10 0x000001a8#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147486712#32 (by decide) (by decide) (bits := 0x1a850513#32) (by decide +kernel) (by decide +kernel)
theorem hc2147486716 : fetchDecode img 2147486716#32 = some (E5R.Instr.op (E5R.AluOp.add) 11 2 10, 4#32) := by exact PackedFetch.fetchDecode_of 2147486716#32 (by decide) (by decide) (bits := 0x00a105b3#32) (by decide +kernel) (by decide +kernel)
theorem hc2147486720 : fetchDecode img 2147486720#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 12 0 0x00000130#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147486720#32 (by decide) (by decide) (bits := 0x13000613#32) (by decide +kernel) (by decide +kernel)
theorem hc2147486724 : fetchDecode img 2147486724#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 10 2 0x000007ff#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147486724#32 (by decide) (by decide) (bits := 0x7ff10513#32) (by decide +kernel) (by decide +kernel)
theorem hc2147486728 : fetchDecode img 2147486728#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 10 10 0x000004f9#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147486728#32 (by decide) (by decide) (bits := 0x4f950513#32) (by decide +kernel) (by decide +kernel)
theorem hc2147486732 : fetchDecode img 2147486732#32 = some (E5R.Instr.auipc 1 0x00004000#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147486732#32 (by decide) (by decide) (bits := 0x00004097#32) (by decide +kernel) (by decide +kernel)
theorem hc2147486736 : fetchDecode img 2147486736#32 = some (E5R.Instr.jalr 1 1 0x00000576#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147486736#32 (by decide) (by decide) (bits := 0x576080e7#32) (by decide +kernel) (by decide +kernel)
theorem hc2147486740 : fetchDecode img 2147486740#32 = some (E5R.Instr.load (E5R.Width.w) true 20 8 0x00000198#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147486740#32 (by decide) (by decide) (bits := 0x19842a03#32) (by decide +kernel) (by decide +kernel)
theorem hc2147486744 : fetchDecode img 2147486744#32 = some (E5R.Instr.load (E5R.Width.w) true 9 8 0x00000074#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147486744#32 (by decide) (by decide) (bits := 0x00005864#32) (by decide +kernel) (by decide +kernel)
theorem hc2147486746 : fetchDecode img 2147486746#32 = some (E5R.Instr.store (E5R.Width.w) 8 20 0x000001bc#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147486746#32 (by decide) (by decide) (bits := 0x1b442e23#32) (by decide +kernel) (by decide +kernel)
theorem hc2147486750 : fetchDecode img 2147486750#32 = some (E5R.Instr.branch (E5R.BrCond.eq) 9 18 0x00000236#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147486750#32 (by decide) (by decide) (bits := 0x23248b63#32) (by decide +kernel) (by decide +kernel)
theorem hc2147486754 : fetchDecode img 2147486754#32 = some (E5R.Instr.branch (E5R.BrCond.ne) 9 22 0x0000039e#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147486754#32 (by decide) (by decide) (bits := 0x39649f63#32) (by decide +kernel) (by decide +kernel)

end E5R.Thermostat
