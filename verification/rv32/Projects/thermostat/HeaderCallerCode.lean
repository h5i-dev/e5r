-- Expected instructions generated from observation; Lean checks every byte against the ELF.
import Projects.thermostat.PackedFetch
namespace E5R.Thermostat
open E5R
theorem hq2147484974 : fetchDecode img 2147484974#32 = some (E5R.Instr.lui 11 0x80006000#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147484974#32 (by decide) (by decide) (bits := 0x800065b7#32) (by decide +kernel) (by decide +kernel)
theorem hq2147484978 : fetchDecode img 2147484978#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 11 11 0xfffffb68#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147484978#32 (by decide) (by decide) (bits := 0xb6858593#32) (by decide +kernel) (by decide +kernel)
theorem hq2147484982 : fetchDecode img 2147484982#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 12 0 0x0000000d#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147484982#32 (by decide) (by decide) (bits := 0x00004635#32) (by decide +kernel) (by decide +kernel)
theorem hq2147484984 : fetchDecode img 2147484984#32 = some (E5R.Instr.op (E5R.AluOp.add) 10 0 21, 2#32) := by exact PackedFetch.fetchDecode_of 2147484984#32 (by decide) (by decide) (bits := 0x00008556#32) (by decide +kernel) (by decide +kernel)
theorem hq2147484986 : fetchDecode img 2147484986#32 = some (E5R.Instr.auipc 1 0x00002000#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147484986#32 (by decide) (by decide) (bits := 0x00002097#32) (by decide +kernel) (by decide +kernel)
theorem hq2147484990 : fetchDecode img 2147484990#32 = some (E5R.Instr.jalr 1 1 0x00000186#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147484990#32 (by decide) (by decide) (bits := 0x186080e7#32) (by decide +kernel) (by decide +kernel)

end E5R.Thermostat
