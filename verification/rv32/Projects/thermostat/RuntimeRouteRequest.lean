import Projects.thermostat.RuntimeRouterEntry
import Projects.thermostat.LoopTransactionMemory
set_option autoImplicit false
namespace E5R.Thermostat.RuntimeRouteRequest
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board

/-- Real Connection/version/count policy and initialized route-table call.
    All route and loop-layout inputs come from the upstream receive theorem;
    no selected handler, successful match or authenticated command is assumed. -/
theorem contract {c ram input s head amount rawUsed served}
    (h : RuntimeRequest.Ready c ram input s head amount rawUsed served)
    (metadata : LoopTransactionMemory.At ram (BitVec.ofNat 32 rawUsed)) :
    ∃ n d after close,
      n≤(77+86*(RuntimeRequestSpans.raw input rawUsed).length)*(RuntimeRequestInputs.entries head).length+71+83 ∧
      Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      RuntimeRouterEntry.At d after input s head amount rawUsed served (c.get 27) close ∧
      LoopTransactionMemory.At after (BitVec.ofNat 32 rawUsed) ∧ d.sameCsr c := by
  obtain ⟨first,a,mid,close,bound,steps,ready,ca,frame⟩ := RuntimeCloseRequest.contract h
  have metadataA := LoopTransactionMemory.caller metadata frame
  obtain ⟨d,dispatch,entry,cd,frame2⟩ := RuntimeRouterEntry.contract ready metadataA.routes
  exact ⟨first+83,d,_,close,by omega,steps.trans dispatch,entry,LoopTransactionMemory.caller metadataA frame2,cd.trans ca⟩
end E5R.Thermostat.RuntimeRouteRequest
