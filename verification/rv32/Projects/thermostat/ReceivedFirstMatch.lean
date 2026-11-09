import Projects.thermostat.ReceivedRouteRequest
import Projects.thermostat.RuntimeFirstMatch
import Projects.thermostat.RouteReceivedPath
set_option autoImplicit false
namespace E5R.Thermostat.ReceivedFirstMatch
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board

/-- Actual receive to first matcher return, for every accepted Empty request.
    Matching /state is concluded from bytes, never a chosen-route premise. -/
theorem empty {c ram s served} (h : LoopReady.At c ram s served)
    (wire : Nat → BitVec 8) (fuel : Nat) (head : Head) (plan : MainHeaderStreamPlan.Plan)
    (space : fuel≤2048) (valid : MainHeaderStreamPlan.Valid plan wire 0 fuel)
    (accepted : (MainHeaderStreamSpec.consume wire fuel []).result=.done head) (kind : head.framing=.empty) :
    let input := (MainHeaderStreamSpec.consume wire fuel []).input
    ∃ n d after lowValue close, Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩
      (MainHeaderStreamPlan.logs plan 0 (MainHeaderStreamSpec.consume wire fuel []).received) [] ∧
      d.pc=0x800013d2#32 ∧ d.get 10=(if RuntimeRequestSpans.path input head=WireSpec.ascii "/state" then 1#32 else 0#32) ∧
      d.get 11=0#32 ∧ LoopTransactionMemory.At after (BitVec.ofNat 32 head.len) ∧
      RuntimeRouteEnvelope.At d after input s head 0 head.len (served+1) lowValue close ∧ d.sameCsr c := by
  obtain ⟨nr,a,mid,lowValue,close,receive,entry,metadata,ca⟩ := ReceivedRouteRequest.empty h wire fuel head plan space valid accepted kind
  obtain ⟨nm,d,_,matched,pc,result,captures,abi,cd,frame,live⟩ := RuntimeFirstMatch.contract entry (RouteReceivedPath.received_path wire fuel head accepted)
  have metadataFinal := LoopTransactionMemory.caller metadata (HeadRegionFrame.sub frame 0 3304 (by decide))
  refine ⟨nr+nm,d,MainPathStateSave.memory mid a,lowValue,close,?_,pc,result,captures,?_,live,cd.trans ca⟩
  · simpa only [List.append_nil] using receive.trans matched.observed
  · simpa only [BitVec.add_zero] using metadataFinal

/-- Complete chunked reception and real compaction retain the original head's
    first path byte; all matcher layout premises then come from actual stores. -/
theorem chunked {c ram s served} (h : LoopReady.At c ram s served)
    (wire : Nat → BitVec 8) (fuel arrivals : Nat) (head : Head)
    (headerPlan : MainHeaderStreamPlan.Plan) (bodyPlan : ChunkReceivePlan.Plan)
    (headSpace : fuel≤2048) (headerValid : MainHeaderStreamPlan.Valid headerPlan wire 0 fuel)
    (accepted : (MainHeaderStreamSpec.consume wire fuel []).result=.done head) (kind : head.framing=.chunked)
    (space : head.len+arrivals≤2048) (bodyValid : ChunkReceivePlan.Valid bodyPlan wire head.len arrivals)
    (done : (ChunkBufferSpec.consume wire arrivals head.len head.len cStart []).stop=.done) :
    let r := ChunkBufferSpec.consume wire arrivals head.len head.len cStart []
    ∃ received n d after raw lowValue close, received≤arrivals ∧ head.len+received=r.read ∧ raw.length=r.read ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩
        (MainHeaderStreamPlan.logs headerPlan 0 (MainHeaderStreamSpec.consume wire fuel []).received++ChunkReceivePlan.logs bodyPlan head.len received) [] ∧
      raw.take head.len=(MainHeaderStreamSpec.consume wire fuel []).input ∧ RuntimeRequestSpans.body raw head r.body.length=r.body ∧
      d.pc=0x800013d2#32 ∧ d.get 10=(if RuntimeRequestSpans.path raw head=WireSpec.ascii "/state" then 1#32 else 0#32) ∧ d.get 11=0#32 ∧
      LoopTransactionMemory.At after (BitVec.ofNat 32 r.read) ∧
      RuntimeRouteEnvelope.At d after raw s head r.body.length r.read (served+1) lowValue close ∧ d.sameCsr c := by
  obtain ⟨received,nr,a,mid,raw,lowValue,close,recvBound,exactRead,len,receive,entry,header,payload,metadata,ca⟩ :=
    ReceivedRouteRequest.chunked h wire fuel arrivals head headerPlan bodyPlan headSpace headerValid accepted kind space bodyValid done
  have parsed := MainHeaderStreamSpec.exact_result wire fuel [] (by decide +kernel)
  rw [accepted] at parsed
  have originalSlash := RouteReceivedPath.accepted_slash _ 1024 1024 head parsed.symm
  have firstInside : head.target.1<head.len := by have := entry.stored.bounds.target;have := entry.stored.contained.1;omega
  have rawSlash : MainQuerySpec.bytes raw head.target.1=47 := by
    rw [←header] at originalSlash
    simpa [MainQuerySpec.bytes,List.getElem?_take,firstInside] using originalSlash
  have ordered := entry.stored.bounds.target.2.1
  have available : head.target.2≤raw.length := by have := entry.stored.contained.1;have := entry.stored.usedBound;omega
  have leading := RouteReceivedPath.path_slash raw head.target.1 head.target.2 ordered available rawSlash
  obtain ⟨nm,d,_,matched,pc,result,captures,abi,cd,frame,live⟩ := RuntimeFirstMatch.contract entry leading
  have metadataFinal := LoopTransactionMemory.caller metadata (HeadRegionFrame.sub frame 0 3304 (by decide))
  refine ⟨received,nr+nm,d,MainPathStateSave.memory mid a,raw,lowValue,close,recvBound,exactRead,len,?_,header,payload,pc,result,captures,?_,live,cd.trans ca⟩
  · simpa only [List.append_nil] using receive.trans matched.observed
  · simpa only [BitVec.add_zero] using metadataFinal
end E5R.Thermostat.ReceivedFirstMatch
