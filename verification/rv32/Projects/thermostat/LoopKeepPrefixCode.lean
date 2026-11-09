import Projects.thermostat.PackedFetch
namespace E5R.Thermostat.LoopKeepPrefixCode
open E5R E5R.Thermostat
theorem at2147489726 : fetchDecode img 2147489726#32=some (E5R.Instr.load (E5R.Width.w) true 12 8 0x0000003c#32,2#32) := by
  exact PackedFetch.fetchDecode_of 2147489726#32 (by decide) (by decide) (bits := 0x00005c50#32) (by decide +kernel) (by decide +kernel)
theorem at2147489728 : fetchDecode img 2147489728#32=some (E5R.Instr.load (E5R.Width.w) true 11 8 0x00000054#32,2#32) := by
  exact PackedFetch.fetchDecode_of 2147489728#32 (by decide) (by decide) (bits := 0x0000486c#32) (by decide +kernel) (by decide +kernel)
theorem at2147489730 : fetchDecode img 2147489730#32=some (E5R.Instr.branch (E5R.BrCond.ltu) 12 11 0x00000520#32,4#32) := by
  exact PackedFetch.fetchDecode_of 2147489730#32 (by decide) (by decide) (bits := 0x52b66063#32) (by decide +kernel) (by decide +kernel)
theorem at2147489734 : fetchDecode img 2147489734#32=some (E5R.Instr.load (E5R.Width.w) true 10 8 0x0000005c#32,2#32) := by
  exact PackedFetch.fetchDecode_of 2147489734#32 (by decide) (by decide) (bits := 0x00004c68#32) (by decide +kernel) (by decide +kernel)
theorem at2147489736 : fetchDecode img 2147489736#32=some (E5R.Instr.branch (E5R.BrCond.ltu) 11 10 0x0000052c#32,4#32) := by
  exact PackedFetch.fetchDecode_of 2147489736#32 (by decide) (by decide) (bits := 0x52a5e663#32) (by decide +kernel) (by decide +kernel)
theorem at2147489740 : fetchDecode img 2147489740#32=some (E5R.Instr.load (E5R.Width.w) true 13 8 0x00000038#32,2#32) := by
  exact PackedFetch.fetchDecode_of 2147489740#32 (by decide) (by decide) (bits := 0x00005c14#32) (by decide +kernel) (by decide +kernel)
theorem at2147489742 : fetchDecode img 2147489742#32=some (E5R.Instr.op (E5R.AluOp.sub) 12 11 10,4#32) := by
  exact PackedFetch.fetchDecode_of 2147489742#32 (by decide) (by decide) (bits := 0x40a58633#32) (by decide +kernel) (by decide +kernel)
theorem at2147489746 : fetchDecode img 2147489746#32=some (E5R.Instr.op (E5R.AluOp.add) 11 13 10,4#32) := by
  exact PackedFetch.fetchDecode_of 2147489746#32 (by decide) (by decide) (bits := 0x00a685b3#32) (by decide +kernel) (by decide +kernel)
theorem at2147489750 : fetchDecode img 2147489750#32=some (E5R.Instr.op (E5R.AluOp.add) 10 0 13,2#32) := by
  exact PackedFetch.fetchDecode_of 2147489750#32 (by decide) (by decide) (bits := 0x00008536#32) (by decide +kernel) (by decide +kernel)
theorem at2147489752 : fetchDecode img 2147489752#32=some (E5R.Instr.auipc 1 0x00004000#32,4#32) := by
  exact PackedFetch.fetchDecode_of 2147489752#32 (by decide) (by decide) (bits := 0x00004097#32) (by decide +kernel) (by decide +kernel)
theorem at2147489756 : fetchDecode img 2147489756#32=some (E5R.Instr.jalr 1 1 0xfffffec8#32,4#32) := by
  exact PackedFetch.fetchDecode_of 2147489756#32 (by decide) (by decide) (bits := 0xec8080e7#32) (by decide +kernel) (by decide +kernel)
end E5R.Thermostat.LoopKeepPrefixCode
