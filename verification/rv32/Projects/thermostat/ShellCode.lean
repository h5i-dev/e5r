-- Expected instructions generated from observation; Lean checks every byte against the ELF.
import Projects.thermostat.PackedFetch
namespace E5R.Thermostat
open E5R
theorem s2147485218 : fetchDecode img 2147485218#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 20 23 0x00000004#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485218#32 (by decide) (by decide) (bits := 0x004b8a13#32) (by decide +kernel) (by decide +kernel)
theorem s2147485222 : fetchDecode img 2147485222#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 10 2 0x00000018#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147485222#32 (by decide) (by decide) (bits := 0x00000828#32) (by decide +kernel) (by decide +kernel)
theorem s2147485224 : fetchDecode img 2147485224#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 11 2 0x00000009#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485224#32 (by decide) (by decide) (bits := 0x00910593#32) (by decide +kernel) (by decide +kernel)
theorem s2147485228 : fetchDecode img 2147485228#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 13 2 0x0000000a#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485228#32 (by decide) (by decide) (bits := 0x00a10693#32) (by decide +kernel) (by decide +kernel)
theorem s2147485232 : fetchDecode img 2147485232#32 = some (E5R.Instr.op (E5R.AluOp.add) 12 0 20, 2#32) := by exact PackedFetch.fetchDecode_of 2147485232#32 (by decide) (by decide) (bits := 0x00008652#32) (by decide +kernel) (by decide +kernel)
theorem s2147485234 : fetchDecode img 2147485234#32 = some (E5R.Instr.auipc 1 0x00001000#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485234#32 (by decide) (by decide) (bits := 0x00001097#32) (by decide +kernel) (by decide +kernel)
theorem s2147485238 : fetchDecode img 2147485238#32 = some (E5R.Instr.jalr 1 1 0x000007f4#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485238#32 (by decide) (by decide) (bits := 0x7f4080e7#32) (by decide +kernel) (by decide +kernel)
theorem s2147485242 : fetchDecode img 2147485242#32 = some (E5R.Instr.load (E5R.Width.b) false 21 2 0x00000022#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485242#32 (by decide) (by decide) (bits := 0x02214a83#32) (by decide +kernel) (by decide +kernel)
theorem s2147485246 : fetchDecode img 2147485246#32 = some (E5R.Instr.load (E5R.Width.b) false 10 2 0x00000018#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485246#32 (by decide) (by decide) (bits := 0x01814503#32) (by decide +kernel) (by decide +kernel)
theorem s2147485250 : fetchDecode img 2147485250#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 11 0 0x00000002#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147485250#32 (by decide) (by decide) (bits := 0x00004589#32) (by decide +kernel) (by decide +kernel)
theorem s2147485252 : fetchDecode img 2147485252#32 = some (E5R.Instr.branch (E5R.BrCond.ne) 21 11 0x00000034#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485252#32 (by decide) (by decide) (bits := 0x02ba9a63#32) (by decide +kernel) (by decide +kernel)
theorem s2147491366 : fetchDecode img 2147491366#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 2 2 0xfffffff0#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147491366#32 (by decide) (by decide) (bits := 0x00001141#32) (by decide +kernel) (by decide +kernel)
theorem s2147491368 : fetchDecode img 2147491368#32 = some (E5R.Instr.store (E5R.Width.w) 2 1 0x0000000c#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147491368#32 (by decide) (by decide) (bits := 0x0000c606#32) (by decide +kernel) (by decide +kernel)
theorem s2147491370 : fetchDecode img 2147491370#32 = some (E5R.Instr.auipc 1 0xffffe000#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147491370#32 (by decide) (by decide) (bits := 0xffffe097#32) (by decide +kernel) (by decide +kernel)
theorem s2147491374 : fetchDecode img 2147491374#32 = some (E5R.Instr.jalr 1 1 0x00000228#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147491374#32 (by decide) (by decide) (bits := 0x228080e7#32) (by decide +kernel) (by decide +kernel)
theorem s2147491378 : fetchDecode img 2147491378#32 = some (E5R.Instr.load (E5R.Width.w) true 1 2 0x0000000c#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147491378#32 (by decide) (by decide) (bits := 0x000040b2#32) (by decide +kernel) (by decide +kernel)
theorem s2147491380 : fetchDecode img 2147491380#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 2 2 0x00000010#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147491380#32 (by decide) (by decide) (bits := 0x00000141#32) (by decide +kernel) (by decide +kernel)
theorem s2147491382 : fetchDecode img 2147491382#32 = some (E5R.Instr.jalr 0 1 0x00000000#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147491382#32 (by decide) (by decide) (bits := 0x00008082#32) (by decide +kernel) (by decide +kernel)

end E5R.Thermostat
