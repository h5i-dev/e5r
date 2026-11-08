import Projects.thermostat.MainRouterCode
namespace E5R.Thermostat
open E5R
theorem rt2147488722 : fetchDecode img 2147488722#32 = some (E5R.Instr.branch (E5R.BrCond.ne) 10 22 0x0000002a#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147488722#32 (by decide) (by decide) (bits := 0x03651563#32) (by decide +kernel) (by decide +kernel)
theorem rt2147488726 : fetchDecode img 2147488726#32 = some (E5R.Instr.load (E5R.Width.w) true 13 8 0x000002b0#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147488726#32 (by decide) (by decide) (bits := 0x2b042683#32) (by decide +kernel) (by decide +kernel)
theorem rt2147488730 : fetchDecode img 2147488730#32 = some (E5R.Instr.load (E5R.Width.w) true 10 8 0x000002b4#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147488730#32 (by decide) (by decide) (bits := 0x2b442503#32) (by decide +kernel) (by decide +kernel)
theorem rt2147488734 : fetchDecode img 2147488734#32 = some (E5R.Instr.load (E5R.Width.b) false 12 10 0x00000174#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147488734#32 (by decide) (by decide) (bits := 0x17454603#32) (by decide +kernel) (by decide +kernel)
theorem rt2147488738 : fetchDecode img 2147488738#32 = some (E5R.Instr.load (E5R.Width.b) false 13 13 0x00000008#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147488738#32 (by decide) (by decide) (bits := 0x0086c683#32) (by decide +kernel) (by decide +kernel)
theorem rt2147488742 : fetchDecode img 2147488742#32 = some (E5R.Instr.branch (E5R.BrCond.eq) 13 12 0x000004d6#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147488742#32 (by decide) (by decide) (bits := 0x4cc68b63#32) (by decide +kernel) (by decide +kernel)
theorem rt2147488746 : fetchDecode img 2147488746#32 = some (E5R.Instr.opimm (E5R.AluOp.xor) 12 12 0x00000001#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147488746#32 (by decide) (by decide) (bits := 0x00164613#32) (by decide +kernel) (by decide +kernel)
theorem rt2147488750 : fetchDecode img 2147488750#32 = some (E5R.Instr.op (E5R.AluOp.or) 12 12 13, 2#32) := by exact PackedFetch.fetchDecode_of 2147488750#32 (by decide) (by decide) (bits := 0x00008e55#32) (by decide +kernel) (by decide +kernel)
theorem rt2147488752 : fetchDecode img 2147488752#32 = some (E5R.Instr.opimm (E5R.AluOp.sltu) 12 12 0x00000001#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147488752#32 (by decide) (by decide) (bits := 0x00163613#32) (by decide +kernel) (by decide +kernel)
theorem rt2147488756 : fetchDecode img 2147488756#32 = some (E5R.Instr.branch (E5R.BrCond.ne) 12 0 0x000004c8#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147488756#32 (by decide) (by decide) (bits := 0x4c061463#32) (by decide +kernel) (by decide +kernel)
end E5R.Thermostat
