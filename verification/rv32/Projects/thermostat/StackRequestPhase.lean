import Projects.thermostat.RequestPhase
import Projects.thermostat.StackRuntimeRouteRequest
import Projects.thermostat.StackRuntimeFirstMatch
set_option autoImplicit false
namespace E5R.Thermostat.StackRequestPhase
open E5R E5R.Thermostat HttpRequestSpec ProtocolStreamSpec RequestPhase
abbrev B := StackBoard.board
theorem enter {c ram input s head amount rawUsed served original body}
    (h : RuntimeRequest.Ready c ram input s head amount rawUsed (served+1))
    (metadata : LoopTransactionMemory.At ram (BitVec.ofNat 32 rawUsed))
    (header : input.take head.len=original) (payload : RuntimeRequestSpans.body input head amount=body)
    (parsed : HttpRequestBytes.parse original 1024 1024=.done head) :
    ∃ n d after,Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      At d after (ProtocolStreamSpec.dispatch ⟨s,served,.head original⟩ original body head) := by
  obtain ⟨nr,a,mid,close,bound,route,entry,memory,csr⟩ := StackRuntimeRouteRequest.contract h metadata
  have originalSlash := RouteReceivedPath.accepted_path original 1024 1024 head parsed
  have pathEq : RuntimeRequestSpans.path input head=RuntimeRequestSpans.path original head := RuntimeHeaderPrefix.path header
    (by have := h.bounds.target.2.1;have := h.contained.1;omega)
  have leading : ∃ ys,RuntimeRequestSpans.path input head=47#8::ys := by rw [pathEq];exact originalSlash
  obtain ⟨nm,d,limit,matchTrace,pc,result,captures,regs,csrD,frame,live⟩ := StackRuntimeFirstMatch.contract entry leading
  have finalMetadata := LoopTransactionMemory.caller memory (HeadRegionFrame.sub frame 0 3304 (by decide))
  refine ⟨nr+nm,d,_,route.trans matchTrace,input,original,body,s,head,amount,rawUsed,served,c.get 27,close,
    live,header,payload,parsed,pc,result,captures,?_,rfl⟩
  simpa only [BitVec.add_zero] using finalMetadata
end E5R.Thermostat.StackRequestPhase
