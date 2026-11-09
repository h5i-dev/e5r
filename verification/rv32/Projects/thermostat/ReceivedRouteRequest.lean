import Projects.thermostat.EmptyReceivedRequest
import Projects.thermostat.ChunkReceivedRequest
import Projects.thermostat.RuntimeRouteRequest
set_option autoImplicit false
namespace E5R.Thermostat.ReceivedRouteRequest
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board

/-- Every accepted Empty request reaches the actual router call, with close
    and loop metadata derived from actual stores since the UART boundary. -/
theorem empty {c ram s served} (h : LoopReady.At c ram s served)
    (wire : Nat → BitVec 8) (fuel : Nat) (head : Head) (plan : MainHeaderStreamPlan.Plan)
    (space : fuel≤2048) (valid : MainHeaderStreamPlan.Valid plan wire 0 fuel)
    (accepted : (MainHeaderStreamSpec.consume wire fuel []).result=.done head) (kind : head.framing=.empty) :
    ∃ n d after lowValue close, Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩
      (MainHeaderStreamPlan.logs plan 0 (MainHeaderStreamSpec.consume wire fuel []).received) [] ∧
      RuntimeRouterEntry.At d after (MainHeaderStreamSpec.consume wire fuel []).input s head 0 head.len (served+1) lowValue close ∧
      LoopTransactionMemory.At after (BitVec.ofNat 32 head.len) ∧ d.sameCsr c := by
  obtain ⟨first,a,mid,receive,request,_,_,ca,_,metadata⟩ := EmptyReceivedRequest.contract h wire fuel head plan space valid accepted kind
  obtain ⟨last,d,after,close,_,route,entry,metadataFinal,cd⟩ := RuntimeRouteRequest.contract request metadata
  exact ⟨first+last,d,after,a.get 27,close,by simpa only [List.append_nil] using receive.trans route.observed,entry,metadataFinal,cd.trans ca⟩

/-- Every accepted complete bounded Chunked request reaches the same actual
    router, retaining independent decoded body/header correspondence and the
    physical filled/consumed/limit/table/capacity premises for loop closure. -/
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
        (MainHeaderStreamPlan.logs headerPlan 0 (MainHeaderStreamSpec.consume wire fuel []).received++
          ChunkReceivePlan.logs bodyPlan head.len received) [] ∧
      RuntimeRouterEntry.At d after raw s head r.body.length r.read (served+1) lowValue close ∧
      raw.take head.len=(MainHeaderStreamSpec.consume wire fuel []).input ∧ RuntimeRequestSpans.body raw head r.body.length=r.body ∧
      LoopTransactionMemory.At after (BitVec.ofNat 32 r.read) ∧ d.sameCsr c := by
  obtain ⟨received,first,a,mid,raw,recvBound,exactRead,len,receive,request,header,payload,ca,_,metadata⟩ :=
    ChunkReceivedRequest.contract h wire fuel arrivals head headerPlan bodyPlan headSpace headerValid accepted kind space bodyValid done
  obtain ⟨last,d,after,close,_,route,entry,metadataFinal,cd⟩ := RuntimeRouteRequest.contract request metadata
  exact ⟨received,first+last,d,after,raw,a.get 27,close,recvBound,exactRead,len,
    by simpa only [List.append_nil] using receive.trans route.observed,entry,header,payload,metadataFinal,cd.trans ca⟩
end E5R.Thermostat.ReceivedRouteRequest
