import Projects.thermostat.PackedFetch
namespace E5R.Thermostat.ChunkRejectCode
open E5R E5R.Thermostat
theorem cr2147487852 : fetchDecode img 2147487852#32=some (E5R.Instr.branch (E5R.BrCond.ne) 10 18 0x000007bc#32,4#32) := by exact PackedFetch.fetchDecode_of 2147487852#32 (by decide) (by decide) (bits := 0x7b251e63#32) (by decide +kernel) (by decide +kernel)
theorem cr2147489832 : fetchDecode img 2147489832#32=some (E5R.Instr.opimm (E5R.AluOp.add) 18 0 0x00000000#32,2#32) := by exact PackedFetch.fetchDecode_of 2147489832#32 (by decide) (by decide) (bits := 0x00004901#32) (by decide +kernel) (by decide +kernel)
theorem cr2147489834 : fetchDecode img 2147489834#32=some (E5R.Instr.opimm (E5R.AluOp.add) 9 0 0x00000003#32,2#32) := by exact PackedFetch.fetchDecode_of 2147489834#32 (by decide) (by decide) (bits := 0x0000448d#32) (by decide +kernel) (by decide +kernel)
theorem cr2147489836 : fetchDecode img 2147489836#32=some (E5R.Instr.jal 0 0xfffff26e#32,4#32) := by exact PackedFetch.fetchDecode_of 2147489836#32 (by decide) (by decide) (bits := 0xa6eff06f#32) (by decide +kernel) (by decide +kernel)
end E5R.Thermostat.ChunkRejectCode
