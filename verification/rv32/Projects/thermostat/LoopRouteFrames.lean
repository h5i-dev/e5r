import Projects.thermostat.LoopTransactionMemory
import Projects.thermostat.MainRouterEntry
import Projects.thermostat.MainPathStateSave
set_option autoImplicit false
namespace E5R.Thermostat.LoopRouteFrames
open E5R E5R.Thermostat
abbrev sp := 0x80ffeb90#32
/-- Matcher ABI save slots are below all recurrence metadata. -/
theorem saved (ram : Word → BitVec 8) (origin : Core) :
    ViewFrame.Region ram (MainPathStateSave.memory ram origin) sp 3304 := by
  intro i
  rw [MainPathStateSave.memory_eq]
  exact OuterSave.frame ram 0x80ffeb30#32 origin _
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)) i)

/-- Actual route-future construction retains the upstream recurrence words. -/
theorem router {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot}
    {head : HttpRequestSpec.Head} {amount served : Nat} {close : Bool} {used : Word}
    (h : MainCloseReady.At c ram input s head amount served close) (metadata : LoopTransactionMemory.At ram used) :
    ∃ d, Quiet.Steps UartPlatform.board img 83 ⟨c,ram⟩ ⟨d,MainRouterSetup.memory ram⟩ ∧
      MainRouterEntry.At d (MainRouterSetup.memory ram) input s head amount served close ∧
      LoopTransactionMemory.At (MainRouterSetup.memory ram) used := by
  obtain ⟨d,steps,ready,_⟩ := MainRouterEntry.contract h metadata.routes
  have frame : ViewFrame.Region ram (MainRouterSetup.memory ram) sp 3304 := by
    simpa only [BitVec.add_zero] using MainRouterSetup.frame ram 0 3304 (by decide) (Or.inl (by decide))
  exact ⟨d,steps,ready,LoopTransactionMemory.caller metadata frame⟩
end E5R.Thermostat.LoopRouteFrames
