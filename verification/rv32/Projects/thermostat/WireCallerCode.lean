-- Expected instructions generated from observation; Lean checks every byte against the ELF.
import Projects.thermostat.PackedFetch
namespace E5R.Thermostat
open E5R
theorem wc2147485172 : fetchDecode img 2147485172#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 11 0 0x000000ff#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485172#32 (by decide) (by decide) (bits := 0x0ff00593#32) (by decide +kernel) (by decide +kernel)
theorem wc2147485176 : fetchDecode img 2147485176#32 = some (E5R.Instr.opimm (E5R.AluOp.and) 12 10 0x000000ff#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485176#32 (by decide) (by decide) (bits := 0x0ff57613#32) (by decide +kernel) (by decide +kernel)
theorem wc2147485180 : fetchDecode img 2147485180#32 = some (E5R.Instr.opimm (E5R.AluOp.srl) 20 10 0x00000010#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485180#32 (by decide) (by decide) (bits := 0x01055a13#32) (by decide +kernel) (by decide +kernel)
theorem wc2147485184 : fetchDecode img 2147485184#32 = some (E5R.Instr.branch (E5R.BrCond.eq) 12 11 0xffffffa2#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485184#32 (by decide) (by decide) (bits := 0xfab601e3#32) (by decide +kernel) (by decide +kernel)
theorem wc2147485188 : fetchDecode img 2147485188#32 = some (E5R.Instr.opimm (E5R.AluOp.srl) 11 10 0x00000008#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485188#32 (by decide) (by decide) (bits := 0x00855593#32) (by decide +kernel) (by decide +kernel)
theorem wc2147485192 : fetchDecode img 2147485192#32 = some (E5R.Instr.store (E5R.Width.b) 2 10 0x0000000a#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485192#32 (by decide) (by decide) (bits := 0x00a10523#32) (by decide +kernel) (by decide +kernel)
theorem wc2147485196 : fetchDecode img 2147485196#32 = some (E5R.Instr.store (E5R.Width.b) 2 11 0x0000000b#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485196#32 (by decide) (by decide) (bits := 0x00b105a3#32) (by decide +kernel) (by decide +kernel)
theorem wc2147485200 : fetchDecode img 2147485200#32 = some (E5R.Instr.store (E5R.Width.h) 2 20 0x0000000c#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485200#32 (by decide) (by decide) (bits := 0x01411623#32) (by decide +kernel) (by decide +kernel)

end E5R.Thermostat
