import Projects.thermostat.ProtocolStreamSpec
import Projects.thermostat.RuntimeRouteRequest
import Projects.thermostat.RuntimeFirstMatch
import Projects.thermostat.RuntimeHeaderPrefix
import Projects.thermostat.RouteReceivedPath
set_option autoImplicit false
namespace E5R.Thermostat.RequestPhase
open E5R E5R.Thermostat HttpRequestSpec ProtocolStreamSpec
abbrev B := UartPlatform.board

def At (c : Core) (ram : Word → BitVec 8) (g : State) : Prop :=
  ∃ input original body s head amount rawUsed served lowValue close,
    RuntimeRouteEnvelope.At c ram input s head amount rawUsed (served+1) lowValue close ∧
    input.take head.len=original ∧ RuntimeRequestSpans.body input head amount=body ∧
    HttpRequestBytes.parse original 1024 1024=.done head ∧
    c.pc=0x800013d2#32 ∧ c.get 10=(if RuntimeRequestSpans.path input head=WireSpec.ascii "/state" then 1#32 else 0#32) ∧
    c.get 11=0#32 ∧ LoopTransactionMemory.At ram (BitVec.ofNat 32 rawUsed) ∧
    g=ProtocolStreamSpec.dispatch ⟨s,served,.head original⟩ original body head

/-- Actual Connection policy, initialized route entry and first matcher, from
    a real received Request. All parser/caller layouts remain proved upstream;
    no selected route, authentication or decoded command is a premise. -/
theorem enter {c ram input s head amount rawUsed served original body}
    (h : RuntimeRequest.Ready c ram input s head amount rawUsed (served+1))
    (metadata : LoopTransactionMemory.At ram (BitVec.ofNat 32 rawUsed))
    (header : input.take head.len=original) (payload : RuntimeRequestSpans.body input head amount=body)
    (parsed : HttpRequestBytes.parse original 1024 1024=.done head) :
    ∃ n d after,Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      At d after (ProtocolStreamSpec.dispatch ⟨s,served,.head original⟩ original body head) := by
  obtain ⟨nr,a,mid,close,bound,route,entry,memory,csr⟩ := RuntimeRouteRequest.contract h metadata
  have originalSlash := RouteReceivedPath.accepted_path original 1024 1024 head parsed
  have pathEq : RuntimeRequestSpans.path input head=RuntimeRequestSpans.path original head := RuntimeHeaderPrefix.path header
    (by have := h.bounds.target.2.1;have := h.contained.1;omega)
  have leading : ∃ ys,RuntimeRequestSpans.path input head=47#8::ys := by rw [pathEq];exact originalSlash
  obtain ⟨nm,d,limit,matchTrace,pc,result,captures,regs,csrD,frame,live⟩ := RuntimeFirstMatch.contract entry leading
  have finalMetadata := LoopTransactionMemory.caller memory (HeadRegionFrame.sub frame 0 3304 (by decide))
  refine ⟨nr+nm,d,_,route.trans matchTrace,input,original,body,s,head,amount,rawUsed,served,c.get 27,close,
    live,header,payload,parsed,pc,result,captures,?_,rfl⟩
  simpa only [BitVec.add_zero] using finalMetadata
end E5R.Thermostat.RequestPhase
