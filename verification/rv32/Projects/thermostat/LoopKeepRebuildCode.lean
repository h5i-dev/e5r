import Projects.thermostat.PackedFetch
namespace E5R.Thermostat.LoopKeepRebuildCode
open E5R E5R.Thermostat
theorem at2147489760 : fetchDecode img 2147489760#32=some (E5R.Instr.load (E5R.Width.w) true 10 8 0x0000005c#32,2#32) := by
  exact PackedFetch.fetchDecode_of 2147489760#32 (by decide) (by decide) (bits := 0x00004c68#32) (by decide +kernel) (by decide +kernel)
theorem at2147489762 : fetchDecode img 2147489762#32=some (E5R.Instr.load (E5R.Width.w) true 12 8 0x00000054#32,2#32) := by
  exact PackedFetch.fetchDecode_of 2147489762#32 (by decide) (by decide) (bits := 0x00004870#32) (by decide +kernel) (by decide +kernel)
theorem at2147489764 : fetchDecode img 2147489764#32=some (E5R.Instr.load (E5R.Width.w) true 11 8 0x00000048#32,2#32) := by
  exact PackedFetch.fetchDecode_of 2147489764#32 (by decide) (by decide) (bits := 0x0000442c#32) (by decide +kernel) (by decide +kernel)
theorem at2147489766 : fetchDecode img 2147489766#32=some (E5R.Instr.load (E5R.Width.w) true 13 8 0x00000038#32,2#32) := by
  exact PackedFetch.fetchDecode_of 2147489766#32 (by decide) (by decide) (bits := 0x00005c14#32) (by decide +kernel) (by decide +kernel)
theorem at2147489768 : fetchDecode img 2147489768#32=some (E5R.Instr.load (E5R.Width.w) true 14 8 0x0000003c#32,2#32) := by
  exact PackedFetch.fetchDecode_of 2147489768#32 (by decide) (by decide) (bits := 0x00005c58#32) (by decide +kernel) (by decide +kernel)
theorem at2147489770 : fetchDecode img 2147489770#32=some (E5R.Instr.op (E5R.AluOp.sub) 12 12 10,2#32) := by
  exact PackedFetch.fetchDecode_of 2147489770#32 (by decide) (by decide) (bits := 0x00008e09#32) (by decide +kernel) (by decide +kernel)
theorem at2147489772 : fetchDecode img 2147489772#32=some (E5R.Instr.opimm (E5R.AluOp.add) 15 2 0x000007ff#32,4#32) := by
  exact PackedFetch.fetchDecode_of 2147489772#32 (by decide) (by decide) (bits := 0x7ff10793#32) (by decide +kernel) (by decide +kernel)
theorem at2147489776 : fetchDecode img 2147489776#32=some (E5R.Instr.opimm (E5R.AluOp.add) 15 15 0x000004d9#32,4#32) := by
  exact PackedFetch.fetchDecode_of 2147489776#32 (by decide) (by decide) (bits := 0x4d978793#32) (by decide +kernel) (by decide +kernel)
theorem at2147489780 : fetchDecode img 2147489780#32=some (E5R.Instr.store (E5R.Width.w) 8 15 0x000001b4#32,4#32) := by
  exact PackedFetch.fetchDecode_of 2147489780#32 (by decide) (by decide) (bits := 0x1af42a23#32) (by decide +kernel) (by decide +kernel)
theorem at2147489784 : fetchDecode img 2147489784#32=some (E5R.Instr.store (E5R.Width.w) 8 11 0x000001b8#32,4#32) := by
  exact PackedFetch.fetchDecode_of 2147489784#32 (by decide) (by decide) (bits := 0x1ab42c23#32) (by decide +kernel) (by decide +kernel)
theorem at2147489788 : fetchDecode img 2147489788#32=some (E5R.Instr.store (E5R.Width.b) 8 0 0x000001c0#32,4#32) := by
  exact PackedFetch.fetchDecode_of 2147489788#32 (by decide) (by decide) (bits := 0x1c040023#32) (by decide +kernel) (by decide +kernel)
theorem at2147489792 : fetchDecode img 2147489792#32=some (E5R.Instr.opimm (E5R.AluOp.add) 10 2 0x000007ff#32,4#32) := by
  exact PackedFetch.fetchDecode_of 2147489792#32 (by decide) (by decide) (bits := 0x7ff10513#32) (by decide +kernel) (by decide +kernel)
theorem at2147489796 : fetchDecode img 2147489796#32=some (E5R.Instr.opimm (E5R.AluOp.add) 10 10 0x000004d1#32,4#32) := by
  exact PackedFetch.fetchDecode_of 2147489796#32 (by decide) (by decide) (bits := 0x4d150513#32) (by decide +kernel) (by decide +kernel)
theorem at2147489800 : fetchDecode img 2147489800#32=some (E5R.Instr.store (E5R.Width.w) 8 10 0x000001a4#32,4#32) := by
  exact PackedFetch.fetchDecode_of 2147489800#32 (by decide) (by decide) (bits := 0x1aa42223#32) (by decide +kernel) (by decide +kernel)
theorem at2147489804 : fetchDecode img 2147489804#32=some (E5R.Instr.store (E5R.Width.w) 8 15 0x000001a8#32,4#32) := by
  exact PackedFetch.fetchDecode_of 2147489804#32 (by decide) (by decide) (bits := 0x1af42423#32) (by decide +kernel) (by decide +kernel)
theorem at2147489808 : fetchDecode img 2147489808#32=some (E5R.Instr.store (E5R.Width.w) 8 11 0x000001ac#32,4#32) := by
  exact PackedFetch.fetchDecode_of 2147489808#32 (by decide) (by decide) (bits := 0x1ab42623#32) (by decide +kernel) (by decide +kernel)
theorem at2147489812 : fetchDecode img 2147489812#32=some (E5R.Instr.store (E5R.Width.w) 8 10 0x000001b0#32,4#32) := by
  exact PackedFetch.fetchDecode_of 2147489812#32 (by decide) (by decide) (bits := 0x1aa42823#32) (by decide +kernel) (by decide +kernel)
theorem at2147489816 : fetchDecode img 2147489816#32=some (E5R.Instr.store (E5R.Width.w) 8 12 0x00000054#32,2#32) := by
  exact PackedFetch.fetchDecode_of 2147489816#32 (by decide) (by decide) (bits := 0x0000c870#32) (by decide +kernel) (by decide +kernel)
theorem at2147489818 : fetchDecode img 2147489818#32=some (E5R.Instr.store (E5R.Width.w) 8 13 0x00000064#32,2#32) := by
  exact PackedFetch.fetchDecode_of 2147489818#32 (by decide) (by decide) (bits := 0x0000d074#32) (by decide +kernel) (by decide +kernel)
theorem at2147489820 : fetchDecode img 2147489820#32=some (E5R.Instr.store (E5R.Width.w) 8 14 0x00000068#32,2#32) := by
  exact PackedFetch.fetchDecode_of 2147489820#32 (by decide) (by decide) (bits := 0x0000d438#32) (by decide +kernel) (by decide +kernel)
theorem at2147489822 : fetchDecode img 2147489822#32=some (E5R.Instr.store (E5R.Width.w) 8 13 0x0000006c#32,2#32) := by
  exact PackedFetch.fetchDecode_of 2147489822#32 (by decide) (by decide) (bits := 0x0000d474#32) (by decide +kernel) (by decide +kernel)
theorem at2147489824 : fetchDecode img 2147489824#32=some (E5R.Instr.store (E5R.Width.w) 8 14 0x00000070#32,2#32) := by
  exact PackedFetch.fetchDecode_of 2147489824#32 (by decide) (by decide) (bits := 0x0000d838#32) (by decide +kernel) (by decide +kernel)
theorem at2147489826 : fetchDecode img 2147489826#32=some (E5R.Instr.branch (E5R.BrCond.geu) 14 12 0xfffff1ee#32,4#32) := by
  exact PackedFetch.fetchDecode_of 2147489826#32 (by decide) (by decide) (bits := 0x9ec77763#32) (by decide +kernel) (by decide +kernel)
end E5R.Thermostat.LoopKeepRebuildCode
