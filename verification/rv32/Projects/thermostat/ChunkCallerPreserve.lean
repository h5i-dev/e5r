import Projects.thermostat.ChunkCallerFrame
import Projects.thermostat.LoopReady
set_option autoImplicit false
namespace E5R.Thermostat.ChunkCallerPreserve
open E5R E5R.Thermostat
abbrev sp := 0x80ffeb90#32

/-- Discharge the capacity/error caller's App, borrow, bank and static-layout
    obligations from the body loop's checked register/store frames. -/
theorem contract {c d : Core} {before after : Word → BitVec 8} {s : Spec.Snapshot} {served : Nat}
    (frame : ChunkCallerFrame.At c d before after sp) (app : AppState.At before s)
    (bank : MainGprBank.At c) (serve : MainServeLayout.At before served)
    (capacity : ramRead before 0x80ffeba0#32 .w=2048#32) (routes : MainRouterTable.At before) :
    AppState.At after s ∧ MainGprBank.At d ∧ MainServeLayout.At after served ∧
      ramRead after 0x80ffeba0#32 .w=2048#32 ∧ MainRouterTable.At after := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · apply AppState.preserve before after s app
    have region := HeadRegionFrame.sub frame.low 44 25 (by decide)
    simpa only [ViewFrame.Region,sp,show 0x80ffeb90#32+44#32=0x80ffebbc#32 by decide +kernel] using region
  · apply MainGprBank.preserve _ bank
    intro r safe
    have kept : ∀ r : Reg, r∈[21,23,26] → MainChunkCoreFrame.Kept r := by decide +kernel
    exact frame.core r (kept r safe)
  · apply MainServeLayout.preserve _ serve
    intro off safe
    simpa only [sp,show 0x80ffeb90#32+3204#32=MainServeLayout.fp by decide +kernel] using frame.words off safe
  · have word := ViewFrame.word frame.low 16 (by decide)
    have value : ramRead after 0x80ffeba0#32 .w=ramRead before 0x80ffeba0#32 .w := by
      simpa only [sp,show 0x80ffeb90#32+16#32=0x80ffeba0#32 by decide +kernel] using word
    exact value.trans capacity
  · apply MainRouterTable.preserve routes
    have region := HeadRegionFrame.sub frame.low 72 60 (by decide)
    simpa only [sp,show 0x80ffeb90#32+72#32=0x80ffebd8#32 by decide +kernel] using region
end E5R.Thermostat.ChunkCallerPreserve
