-- Expected instructions generated from observation; Lean checks every byte against the ELF.
import Projects.thermostat.PackedFetch
namespace E5R.Thermostat
open E5R
theorem mcp2147489668 : fetchDecode img 2147489668#32 = some (E5R.Instr.load (E5R.Width.w) true 10 8 0x00000524#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147489668#32 (by decide) (by decide) (bits := 0x52442503#32) (by decide +kernel) (by decide +kernel)
theorem mcp2147489672 : fetchDecode img 2147489672#32 = some (E5R.Instr.branch (E5R.BrCond.ne) 10 24 0x00000022#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147489672#32 (by decide) (by decide) (bits := 0x03851163#32) (by decide +kernel) (by decide +kernel)
theorem mcp2147489706 : fetchDecode img 2147489706#32 = some (E5R.Instr.load (E5R.Width.w) true 10 8 0x00000524#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147489706#32 (by decide) (by decide) (bits := 0x52442503#32) (by decide +kernel) (by decide +kernel)
theorem mcp2147489710 : fetchDecode img 2147489710#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 21 0 0xffffffff#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147489710#32 (by decide) (by decide) (bits := 0x00005afd#32) (by decide +kernel) (by decide +kernel)
theorem mcp2147489712 : fetchDecode img 2147489712#32 = some (E5R.Instr.branch (E5R.BrCond.ne) 10 21 0xfffff1bc#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147489712#32 (by decide) (by decide) (bits := 0x9b551e63#32) (by decide +kernel) (by decide +kernel)
theorem mcp2147489716 : fetchDecode img 2147489716#32 = some (E5R.Instr.load (E5R.Width.w) true 10 8 0x00000528#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147489716#32 (by decide) (by decide) (bits := 0x52842503#32) (by decide +kernel) (by decide +kernel)
theorem mcp2147489720 : fetchDecode img 2147489720#32 = some (E5R.Instr.opimm (E5R.AluOp.and) 10 10 0x00000001#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147489720#32 (by decide) (by decide) (bits := 0x00008905#32) (by decide +kernel) (by decide +kernel)
theorem mcp2147489722 : fetchDecode img 2147489722#32 = some (E5R.Instr.branch (E5R.BrCond.ne) 10 0 0xfffff1be#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147489722#32 (by decide) (by decide) (bits := 0x9a051f63#32) (by decide +kernel) (by decide +kernel)

end E5R.Thermostat
