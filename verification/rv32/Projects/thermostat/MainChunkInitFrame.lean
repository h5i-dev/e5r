import Projects.thermostat.MainChunkInitData
import Projects.thermostat.MainChunkLayout
import Projects.thermostat.AppState
import Projects.thermostat.ViewFrame
import Projects.thermostat.WordRegions
namespace E5R.Thermostat.MainChunkInitFrame
open E5R E5R.Thermostat

theorem region (ram : Word → BitVec 8) (start base : Word) (n : Nat)
    (hm : WordRegions.Disjoint base n (0x80fff814#32+452#32) 8)
    (hs : WordRegions.Disjoint base n (0x80fff814#32+476#32) 32) :
    ViewFrame.Region ram (MainChunkInit.memory ram 0x80fff814#32 start) base n := by
  intro i
  exact MainChunkInitData.frame ram 0x80fff814#32 start _ (hm i) (hs i)

theorem low (ram : Word → BitVec 8) (start : Word) :
    ViewFrame.Region ram (MainChunkInit.memory ram 0x80fff814#32 start) 0x80fff814#32 452 :=
  region ram start _ _
    (WordRegions.before _ _ _ _ (by decide +kernel) (by decide +kernel))
    (WordRegions.before _ _ _ _ (by decide +kernel) (by decide +kernel))

theorem rx (ram : Word → BitVec 8) (start : Word) :
    ViewFrame.Region ram (MainChunkInit.memory ram 0x80fff814#32 start) 0x80ffec14#32 2048 :=
  region ram start _ _
    (WordRegions.before _ _ _ _ (by decide +kernel) (by decide +kernel))
    (WordRegions.before _ _ _ _ (by decide +kernel) (by decide +kernel))

theorem tx (ram : Word → BitVec 8) (start : Word) :
    ViewFrame.Region ram (MainChunkInit.memory ram 0x80fff814#32 start) 0x80fff414#32 1024 :=
  region ram start _ _
    (WordRegions.before _ _ _ _ (by decide +kernel) (by decide +kernel))
    (WordRegions.before _ _ _ _ (by decide +kernel) (by decide +kernel))

theorem app (ram : Word → BitVec 8) (start : Word) (state : Spec.Snapshot)
    (h : AppState.At ram state) : AppState.At (MainChunkInit.memory ram 0x80fff814#32 start) state := by
  apply AppState.preserve ram _ state h
  exact region ram start _ _
    (WordRegions.before _ _ _ _ (by decide +kernel) (by decide +kernel))
    (WordRegions.before _ _ _ _ (by decide +kernel) (by decide +kernel))

theorem low_sp (ram : Word → BitVec 8) (sp start : Word) :
    ViewFrame.Region ram (MainChunkInit.memory ram (sp+3204#32) start) sp 3656 := by
  intro i
  apply MainChunkInitData.frame
  · intro j
    rw [show (sp+3204#32)+452#32=sp+3656#32 by rw [BitVec.add_assoc,show 3204#32+452#32=3656#32 by decide +kernel]]
    simpa only [BitVec.add_zero] using FrameOffsets.ne sp 0 3656 i.val j.val
      (by have := i.isLt;omega) (by have := j.isLt;omega) (by have := i.isLt;have := j.isLt;omega)
  · intro j
    rw [show (sp+3204#32)+476#32=sp+3680#32 by rw [BitVec.add_assoc,show 3204#32+476#32=3680#32 by decide +kernel]]
    simpa only [BitVec.add_zero] using FrameOffsets.ne sp 0 3680 i.val j.val
      (by have := i.isLt;omega) (by have := j.isLt;omega) (by have := i.isLt;have := j.isLt;omega)

theorem layout {ram sp start} (h : MainChunkLayout.At ram sp) :
    MainChunkLayout.At (MainChunkInit.memory ram (sp+3204#32) start) sp :=
  MainChunkLayout.preserve h (fun off _ hi => ViewFrame.word (low_sp ram sp start) off hi)

end E5R.Thermostat.MainChunkInitFrame
