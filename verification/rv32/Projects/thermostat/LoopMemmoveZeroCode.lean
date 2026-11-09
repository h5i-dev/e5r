import Projects.thermostat.PackedFetch
namespace E5R.Thermostat.LoopMemmoveZeroCode
open E5R E5R.Thermostat
theorem at2147505824 : fetchDecode img 2147505824#32=some (E5R.Instr.auipc 6 0x00000000#32,4#32) := by
  exact PackedFetch.fetchDecode_of 2147505824#32 (by decide) (by decide) (bits := 0x00000317#32) (by decide +kernel) (by decide +kernel)
theorem at2147505828 : fetchDecode img 2147505828#32=some (E5R.Instr.jalr 0 6 0xfffffc70#32,4#32) := by
  exact PackedFetch.fetchDecode_of 2147505828#32 (by decide) (by decide) (bits := 0xc7030067#32) (by decide +kernel) (by decide +kernel)
theorem at2147504912 : fetchDecode img 2147504912#32=some (E5R.Instr.opimm (E5R.AluOp.add) 2 2 0xffffffe0#32,2#32) := by
  exact PackedFetch.fetchDecode_of 2147504912#32 (by decide) (by decide) (bits := 0x00001101#32) (by decide +kernel) (by decide +kernel)
theorem at2147504914 : fetchDecode img 2147504914#32=some (E5R.Instr.store (E5R.Width.w) 2 8 0x0000001c#32,2#32) := by
  exact PackedFetch.fetchDecode_of 2147504914#32 (by decide) (by decide) (bits := 0x0000ce22#32) (by decide +kernel) (by decide +kernel)
theorem at2147504916 : fetchDecode img 2147504916#32=some (E5R.Instr.op (E5R.AluOp.sub) 13 10 11,4#32) := by
  exact PackedFetch.fetchDecode_of 2147504916#32 (by decide) (by decide) (bits := 0x40b506b3#32) (by decide +kernel) (by decide +kernel)
theorem at2147504920 : fetchDecode img 2147504920#32=some (E5R.Instr.branch (E5R.BrCond.geu) 13 12 0x00000074#32,4#32) := by
  exact PackedFetch.fetchDecode_of 2147504920#32 (by decide) (by decide) (bits := 0x06c6fa63#32) (by decide +kernel) (by decide +kernel)
theorem at2147505036 : fetchDecode img 2147505036#32=some (E5R.Instr.opimm (E5R.AluOp.add) 13 0 0x00000010#32,2#32) := by
  exact PackedFetch.fetchDecode_of 2147505036#32 (by decide) (by decide) (bits := 0x000046c1#32) (by decide +kernel) (by decide +kernel)
theorem at2147505038 : fetchDecode img 2147505038#32=some (E5R.Instr.branch (E5R.BrCond.ltu) 12 13 0x00000072#32,4#32) := by
  exact PackedFetch.fetchDecode_of 2147505038#32 (by decide) (by decide) (bits := 0x06d66963#32) (by decide +kernel) (by decide +kernel)
theorem at2147505152 : fetchDecode img 2147505152#32=some (E5R.Instr.op (E5R.AluOp.add) 13 0 10,2#32) := by
  exact PackedFetch.fetchDecode_of 2147505152#32 (by decide) (by decide) (bits := 0x000086aa#32) (by decide +kernel) (by decide +kernel)
theorem at2147505154 : fetchDecode img 2147505154#32=some (E5R.Instr.op (E5R.AluOp.add) 14 10 12,4#32) := by
  exact PackedFetch.fetchDecode_of 2147505154#32 (by decide) (by decide) (bits := 0x00c50733#32) (by decide +kernel) (by decide +kernel)
theorem at2147505158 : fetchDecode img 2147505158#32=some (E5R.Instr.branch (E5R.BrCond.ltu) 10 14 0x0000021c#32,4#32) := by
  exact PackedFetch.fetchDecode_of 2147505158#32 (by decide) (by decide) (bits := 0x20e56e63#32) (by decide +kernel) (by decide +kernel)
theorem at2147505162 : fetchDecode img 2147505162#32=some (E5R.Instr.jal 0 0x00000228#32,2#32) := by
  exact PackedFetch.fetchDecode_of 2147505162#32 (by decide) (by decide) (bits := 0x0000a425#32) (by decide +kernel) (by decide +kernel)
theorem at2147505714 : fetchDecode img 2147505714#32=some (E5R.Instr.load (E5R.Width.w) true 8 2 0x0000001c#32,2#32) := by
  exact PackedFetch.fetchDecode_of 2147505714#32 (by decide) (by decide) (bits := 0x00004472#32) (by decide +kernel) (by decide +kernel)
theorem at2147505716 : fetchDecode img 2147505716#32=some (E5R.Instr.opimm (E5R.AluOp.add) 2 2 0x00000020#32,2#32) := by
  exact PackedFetch.fetchDecode_of 2147505716#32 (by decide) (by decide) (bits := 0x00006105#32) (by decide +kernel) (by decide +kernel)
theorem at2147505718 : fetchDecode img 2147505718#32=some (E5R.Instr.jalr 0 1 0x00000000#32,2#32) := by
  exact PackedFetch.fetchDecode_of 2147505718#32 (by decide) (by decide) (bits := 0x00008082#32) (by decide +kernel) (by decide +kernel)
end E5R.Thermostat.LoopMemmoveZeroCode
