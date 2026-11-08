import Projects.thermostat.FutureHeadLayout
import Projects.thermostat.FutureBodyLimit
import Projects.thermostat.ViewFrame
namespace E5R.Thermostat.MainHeadLayout
open E5R E5R.Thermostat

structure At (ram : Word → BitVec 8) : Prop where
  rx : ramRead ram (0x80fff814#32+108#32) .w=0x80ffec14#32
  config : ramRead ram (0x80fff814#32+432#32) .w=0x80fff860#32
  headLimit : ramRead ram (0x80fff814#32+76#32) .w=1024#32
  bodyLimit : ramRead ram (0x80fff814#32+80#32) .w=1024#32

theorem initialized (ram : Word → BitVec 8) (capacity : ramRead ram 0x80ffeba0#32 .w=2048#32) : At (FutureSetup.memory ram) := by
  rw [FutureSetup.memory_initialized ram capacity]
  constructor <;> simp [FutureSetup.initialized,ramRead,ramWrite,ramPut,byteOf]

theorem preserve {before after : Word → BitVec 8} (h : At before)
    (frame : ViewFrame.Region before after 0x80fff814#32 449) : At after :=
  ⟨(ViewFrame.word frame 108 (by decide)).trans h.rx,
    (ViewFrame.word frame 432 (by decide)).trans h.config,
    (ViewFrame.word frame 76 (by decide)).trans h.headLimit,
    (ViewFrame.word frame 80 (by decide)).trans h.bodyLimit⟩
end E5R.Thermostat.MainHeadLayout
