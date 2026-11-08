-- Expected instructions generated from observation; Lean checks every byte against the ELF.
import Projects.thermostat.PackedFetch
namespace E5R.Thermostat
open E5R
theorem up2147485688 : fetchDecode img 2147485688#32 = some (E5R.Instr.load (E5R.Width.b) false 17 13 0x00000005#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485688#32 (by decide) (by decide) (bits := 0x0056c883#32) (by decide +kernel) (by decide +kernel)
theorem up2147485692 : fetchDecode img 2147485692#32 = some (E5R.Instr.opimm (E5R.AluOp.and) 17 17 0x00000020#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485692#32 (by decide) (by decide) (bits := 0x0208f893#32) (by decide +kernel) (by decide +kernel)
theorem up2147485696 : fetchDecode img 2147485696#32 = some (E5R.Instr.branch (E5R.BrCond.ne) 17 0 0xffffffea#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147485696#32 (by decide) (by decide) (bits := 0xfe0895e3#32) (by decide +kernel) (by decide +kernel)
theorem up2147485700 : fetchDecode img 2147485700#32 = some (E5R.Instr.fence, 4#32) := by exact PackedFetch.fetchDecode_of 2147485700#32 (by decide) (by decide) (bits := 0x0100000f#32) (by decide +kernel) (by decide +kernel)
theorem up2147485704 : fetchDecode img 2147485704#32 = some (E5R.Instr.jal 0 0xfffffff0#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147485704#32 (by decide) (by decide) (bits := 0x0000bfc5#32) (by decide +kernel) (by decide +kernel)
theorem up2147486622 : fetchDecode img 2147486622#32 = some (E5R.Instr.fence, 4#32) := by exact PackedFetch.fetchDecode_of 2147486622#32 (by decide) (by decide) (bits := 0x0100000f#32) (by decide +kernel) (by decide +kernel)
theorem up2147486626 : fetchDecode img 2147486626#32 = some (E5R.Instr.load (E5R.Width.b) false 10 19 0x00000005#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147486626#32 (by decide) (by decide) (bits := 0x0059c503#32) (by decide +kernel) (by decide +kernel)
theorem up2147486630 : fetchDecode img 2147486630#32 = some (E5R.Instr.opimm (E5R.AluOp.and) 10 10 0x00000001#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147486630#32 (by decide) (by decide) (bits := 0x00008905#32) (by decide +kernel) (by decide +kernel)
theorem up2147486632 : fetchDecode img 2147486632#32 = some (E5R.Instr.branch (E5R.BrCond.eq) 10 0 0xfffffff6#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147486632#32 (by decide) (by decide) (bits := 0x0000d97d#32) (by decide +kernel) (by decide +kernel)
theorem up2147486634 : fetchDecode img 2147486634#32 = some (E5R.Instr.load (E5R.Width.b) false 10 19 0x00000000#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147486634#32 (by decide) (by decide) (bits := 0x0009c503#32) (by decide +kernel) (by decide +kernel)
theorem up2147486638 : fetchDecode img 2147486638#32 = some (E5R.Instr.store (E5R.Width.b) 12 10 0x00000000#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147486638#32 (by decide) (by decide) (bits := 0x00a60023#32) (by decide +kernel) (by decide +kernel)

end E5R.Thermostat
