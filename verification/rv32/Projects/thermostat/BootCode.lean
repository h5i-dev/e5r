-- Expected instructions generated from observation; Lean checks every byte against the ELF.
import Projects.thermostat.PackedFetch
namespace E5R.Thermostat
open E5R
theorem bt2147483648 : fetchDecode img 2147483648#32 = some (E5R.Instr.csr (E5R.CsrOp.rw) 0 (E5R.CsrSrc.imm 0x00000000#32) 772, 4#32) := by exact PackedFetch.fetchDecode_of 2147483648#32 (by decide) (by decide) (bits := 0x30405073#32) (by decide +kernel) (by decide +kernel)
theorem bt2147483652 : fetchDecode img 2147483652#32 = some (E5R.Instr.csr (E5R.CsrOp.rc) 0 (E5R.CsrSrc.imm 0x00000008#32) 768, 4#32) := by exact PackedFetch.fetchDecode_of 2147483652#32 (by decide) (by decide) (bits := 0x30047073#32) (by decide +kernel) (by decide +kernel)
theorem bt2147483656 : fetchDecode img 2147483656#32 = some (E5R.Instr.auipc 2 0x01000000#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147483656#32 (by decide) (by decide) (bits := 0x01000117#32) (by decide +kernel) (by decide +kernel)
theorem bt2147483660 : fetchDecode img 2147483660#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 2 2 0xfffffff8#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147483660#32 (by decide) (by decide) (bits := 0xff810113#32) (by decide +kernel) (by decide +kernel)
theorem bt2147483664 : fetchDecode img 2147483664#32 = some (E5R.Instr.auipc 5 0x00006000#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147483664#32 (by decide) (by decide) (bits := 0x00006297#32) (by decide +kernel) (by decide +kernel)
theorem bt2147483668 : fetchDecode img 2147483668#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 5 5 0xffffff08#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147483668#32 (by decide) (by decide) (bits := 0xf0828293#32) (by decide +kernel) (by decide +kernel)
theorem bt2147483672 : fetchDecode img 2147483672#32 = some (E5R.Instr.auipc 6 0x00006000#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147483672#32 (by decide) (by decide) (bits := 0x00006317#32) (by decide +kernel) (by decide +kernel)
theorem bt2147483676 : fetchDecode img 2147483676#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 6 6 0xffffff00#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147483676#32 (by decide) (by decide) (bits := 0xf0030313#32) (by decide +kernel) (by decide +kernel)
theorem bt2147483680 : fetchDecode img 2147483680#32 = some (E5R.Instr.branch (E5R.BrCond.geu) 5 6 0x0000000c#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147483680#32 (by decide) (by decide) (bits := 0x0062f663#32) (by decide +kernel) (by decide +kernel)
theorem bt2147483684 : fetchDecode img 2147483684#32 = some (E5R.Instr.store (E5R.Width.w) 5 0 0x00000000#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147483684#32 (by decide) (by decide) (bits := 0x0002a023#32) (by decide +kernel) (by decide +kernel)
theorem bt2147483688 : fetchDecode img 2147483688#32 = some (E5R.Instr.opimm (E5R.AluOp.add) 5 5 0x00000004#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147483688#32 (by decide) (by decide) (bits := 0x00000291#32) (by decide +kernel) (by decide +kernel)
theorem bt2147483690 : fetchDecode img 2147483690#32 = some (E5R.Instr.jal 0 0xfffffff6#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147483690#32 (by decide) (by decide) (bits := 0x0000bfdd#32) (by decide +kernel) (by decide +kernel)
theorem bt2147483692 : fetchDecode img 2147483692#32 = some (E5R.Instr.auipc 1 0x00001000#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147483692#32 (by decide) (by decide) (bits := 0x00001097#32) (by decide +kernel) (by decide +kernel)
theorem bt2147483696 : fetchDecode img 2147483696#32 = some (E5R.Instr.jalr 1 1 0xfffff836#32, 4#32) := by exact PackedFetch.fetchDecode_of 2147483696#32 (by decide) (by decide) (bits := 0x836080e7#32) (by decide +kernel) (by decide +kernel)
theorem bt2147483700 : fetchDecode img 2147483700#32 = some (E5R.Instr.jal 0 0x00000000#32, 2#32) := by exact PackedFetch.fetchDecode_of 2147483700#32 (by decide) (by decide) (bits := 0x0000a001#32) (by decide +kernel) (by decide +kernel)

end E5R.Thermostat
