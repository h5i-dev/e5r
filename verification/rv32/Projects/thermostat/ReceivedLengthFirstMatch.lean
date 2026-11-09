import Projects.thermostat.LengthReceivedRequest
import Projects.thermostat.RuntimeRouteRequest
import Projects.thermostat.RuntimeFirstMatch
import Projects.thermostat.RouteReceivedPath
import Projects.thermostat.RuntimeHeaderPrefix
set_option autoImplicit false
namespace E5R.Thermostat.ReceivedLengthFirstMatch
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec

theorem contract {c ram s served} (h : LoopReady.At c ram s served)
    (wire : Nat → BitVec 8) (fuel : Nat) (head : Head) (amount : Nat)
    (headerPlan : MainHeaderStreamPlan.Plan) (bodyPlan : MainLengthStreamPlan.Plan)
    (space : fuel≤2048) (headerValid : MainHeaderStreamPlan.Valid headerPlan wire 0 fuel)
    (accepted : (consume wire fuel []).result=.done head) (framing : head.framing=.length amount)
    (bodyValid : MainLengthStreamPlan.Valid bodyPlan wire head.len amount) :
    let first := (consume wire fuel []).input
    let input := first++arrivals wire head.len amount
    ∃ n d after lowValue close,Observed.Steps UartPlatform.board img n ⟨c,ram⟩ ⟨d,after⟩
      (MainHeaderStreamPlan.logs headerPlan 0 (consume wire fuel []).received++MainLengthStreamPlan.logs bodyPlan head.len amount) [] ∧
      d.pc=0x800013d2#32 ∧ d.get 10=(if RuntimeRequestSpans.path input head=WireSpec.ascii "/state" then 1#32 else 0#32) ∧ d.get 11=0#32 ∧
      RuntimeRouteEnvelope.At d after input s head amount (head.len+amount) (served+1) lowValue close ∧
      LoopTransactionMemory.At after (BitVec.ofNat 32 (head.len+amount)) ∧
      input.take head.len=first ∧ RuntimeRequestSpans.body input head amount=arrivals wire head.len amount := by
  obtain ⟨nr,a,mid,receive,request,header,payload,static,metadata⟩ := LengthReceivedRequest.contract h wire fuel head amount headerPlan bodyPlan space headerValid accepted framing bodyValid
  obtain ⟨nroute,b,mb,close,_,route,entry,metadataB,_⟩ := RuntimeRouteRequest.contract request metadata
  have leading := RouteReceivedPath.received_path wire fuel head accepted
  have targetBound : head.target.1≤head.target.2 ∧ head.target.2≤head.len := by
    have := request.bounds.target.2.1;have := request.contained.1;omega
  have fullLeading : ∃ ys,RuntimeRequestSpans.path ((consume wire fuel []).input++arrivals wire head.len amount) head=47#8::ys := by
    have fullPath : RuntimeRequestSpans.path ((consume wire fuel []).input++arrivals wire head.len amount) head=RuntimeRequestSpans.path (consume wire fuel []).input head := RuntimeHeaderPrefix.path header targetBound
    rw [fullPath];exact leading
  obtain ⟨nm,d,_,matched,pc,result,captures,abi,csr,frame,live⟩ := RuntimeFirstMatch.contract entry fullLeading
  have metadataD := LoopTransactionMemory.caller metadataB (HeadRegionFrame.sub frame 0 3304 (by decide))
  refine ⟨nr+nroute+nm,d,_,a.get 27,close,?_,pc,result,captures,live,?_,header,payload⟩
  · simpa only [List.append_nil] using (receive.trans route.observed).trans matched.observed
  · simpa only [BitVec.add_zero] using metadataD
end E5R.Thermostat.ReceivedLengthFirstMatch
