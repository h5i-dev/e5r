-- Expected instructions generated from observation; Lean checks every byte against the ELF.
import Projects.thermostat.PackedFetch
namespace E5R.Thermostat
open E5R
theorem mc2147504482 : fetchDecode img 2147504482#32 = some (E5R.Instr.branch (E5R.BrCond.eq) 12 0 0x00000016#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147504482#32 (by decide) (by decide) (bits := 0x0000ca19#32) (by decide +kernel) (by decide +kernel)
theorem mc2147504484 : fetchDecode img 2147504484#32 = some (E5R.Instr.load (E5R.Width.b) false 13 10 0x00000000#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147504484#32 (by decide) (by decide) (bits := 0x00054683#32) (by decide +kernel) (by decide +kernel)
theorem mc2147504488 : fetchDecode img 2147504488#32 = some (E5R.Instr.load (E5R.Width.b) false 14 11 0x00000000#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147504488#32 (by decide) (by decide) (bits := 0x0005c703#32) (by decide +kernel) (by decide +kernel)
theorem mc2147504492 : fetchDecode img 2147504492#32 = some (E5R.Instr.branch (E5R.BrCond.ne) 13 14 0x00000010#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147504492#32 (by decide) (by decide) (bits := 0x00e69863#32) (by decide +kernel) (by decide +kernel)
theorem mc2147504496 : fetchDecode img 2147504496#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 12 12 0xffffffff#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147504496#32 (by decide) (by decide) (bits := 0x0000167d#32) (by decide +kernel) (by decide +kernel)
theorem mc2147504498 : fetchDecode img 2147504498#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 11 11 0x00000001#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147504498#32 (by decide) (by decide) (bits := 0x00000585#32) (by decide +kernel) (by decide +kernel)
theorem mc2147504500 : fetchDecode img 2147504500#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 10 10 0x00000001#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147504500#32 (by decide) (by decide) (bits := 0x00000505#32) (by decide +kernel) (by decide +kernel)
theorem mc2147504502 : fetchDecode img 2147504502#32 = some (E5R.Instr.branch (E5R.BrCond.ne) 12 0 0xffffffee#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147504502#32 (by decide) (by decide) (bits := 0x0000f67d#32) (by decide +kernel) (by decide +kernel)
theorem mc2147504504 : fetchDecode img 2147504504#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 10 0 0x00000000#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147504504#32 (by decide) (by decide) (bits := 0x00004501#32) (by decide +kernel) (by decide +kernel)
theorem mc2147504506 : fetchDecode img 2147504506#32 = some (E5R.Instr.jalr 0 1 0x00000000#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147504506#32 (by decide) (by decide) (bits := 0x00008082#32) (by decide +kernel) (by decide +kernel)
theorem mc2147504508 : fetchDecode img 2147504508#32 = some (E5R.Instr.op (E5R.AluOp.sub) 10 13 14, 4#32) := by exact PackedFetch.fetchDecode_of 2147504508#32 (by decide) (by decide) (bits := 0x40e68533#32) (by decide +kernel) (by decide +kernel)
theorem mc2147504512 : fetchDecode img 2147504512#32 = some (E5R.Instr.jalr 0 1 0x00000000#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147504512#32 (by decide) (by decide) (bits := 0x00008082#32) (by decide +kernel) (by decide +kernel)

end E5R.Thermostat
