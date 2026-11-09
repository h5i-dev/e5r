import Projects.thermostat.RuntimeHeaderPrefix
import Projects.thermostat.ReceivedFirstMatch
import Projects.thermostat.RuntimeRouteRefusal
set_option autoImplicit false
namespace E5R.Thermostat.ReceivedRouteRefusalCycle
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board

/-- Accepted Empty request with a pure routing refusal returns exact404/405
    bytes and the reusable receive boundary; all caller layouts are derived. -/
theorem empty {c ram s served} (h : LoopReady.At c ram s served)
    (wire : Nat → BitVec 8) (fuel : Nat) (head : Head) (plan : MainHeaderStreamPlan.Plan)
    (space : fuel≤2048) (valid : MainHeaderStreamPlan.Valid plan wire 0 fuel)
    (accepted : (MainHeaderStreamSpec.consume wire fuel []).result=.done head) (kind : head.framing=.empty)
    (denied : ∀ kind : RouteLiteralInfo.Kind,RuntimeRequestSpans.path (MainHeaderStreamSpec.consume wire fuel []).input head=RouteLiteralInfo.text kind →
      RouteSpec.allows (RouteLiteralInfo.route kind) (MainMethodSpec.decode (MainMethodBytes.token (MainHeaderStreamSpec.consume wire fuel []).input head.method.2))=false)
    (missing : ¬RouteSpec.relayPath (RuntimeRequestSpans.path (MainHeaderStreamSpec.consume wire fuel []).input head))
    (hs : Bool → List UartTxLoop.Slot)
    (hhs : ∀ close,(hs close).length=(ResponseHeadSpec.bytes (RouteRefusalSpec.status (RuntimeRequestSpans.path (MainHeaderStreamSpec.consume wire fuel []).input head)) [] 0 close).length) :
    let input := (MainHeaderStreamSpec.consume wire fuel []).input
    ∃ n d after close, Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩
      (MainHeaderStreamPlan.logs plan 0 (MainHeaderStreamSpec.consume wire fuel []).received++UartTxLoop.reads (hs close))
      (UartTxLoop.events (ResponseHeadSpec.bytes (RouteRefusalSpec.status (RuntimeRequestSpans.path (MainHeaderStreamSpec.consume wire fuel []).input head)) [] 0 close)) ∧
      close=MainCloseSpec.mustClose head.minor (served+1) (RuntimeRequestSpans.raw input head.len) (RuntimeRequestInputs.entries head) ∧
      LoopReady.At d after s (if close then 0 else served+1) := by
  obtain ⟨nr,a,mid,lowValue,close,received,pc,result,captures,metadata,live,csr⟩ := ReceivedFirstMatch.empty h wire fuel head plan space valid accepted kind
  have leading := RouteReceivedPath.received_path wire fuel head accepted
  obtain ⟨nt,d,after,sent,ready⟩ := RuntimeRouteRefusal.contract live pc result denied missing leading metadata (hs close) (hhs close)
  refine ⟨nr+nt,d,after,close,?_,live.closeSpec,ready⟩
  simpa only [List.nil_append,List.append_assoc] using received.trans sent

/-- Complete bounded chunked route-refusal cycle. Original method/path are
    carried through actual body compaction by exact header-prefix equality. -/
theorem chunked {c ram s served} (h : LoopReady.At c ram s served)
    (wire : Nat → BitVec 8) (fuel arrivals : Nat) (head : Head)
    (headerPlan : MainHeaderStreamPlan.Plan) (bodyPlan : ChunkReceivePlan.Plan)
    (headSpace : fuel≤2048) (headerValid : MainHeaderStreamPlan.Valid headerPlan wire 0 fuel)
    (accepted : (MainHeaderStreamSpec.consume wire fuel []).result=.done head) (kind : head.framing=.chunked)
    (space : head.len+arrivals≤2048) (bodyValid : ChunkReceivePlan.Valid bodyPlan wire head.len arrivals)
    (done : (ChunkBufferSpec.consume wire arrivals head.len head.len cStart []).stop=.done)
    (denied : ∀ kind : RouteLiteralInfo.Kind,RuntimeRequestSpans.path (MainHeaderStreamSpec.consume wire fuel []).input head=RouteLiteralInfo.text kind →
      RouteSpec.allows (RouteLiteralInfo.route kind) (MainMethodSpec.decode (MainMethodBytes.token (MainHeaderStreamSpec.consume wire fuel []).input head.method.2))=false)
    (missing : ¬RouteSpec.relayPath (RuntimeRequestSpans.path (MainHeaderStreamSpec.consume wire fuel []).input head))
    (hs : Bool → List UartTxLoop.Slot)
    (hhs : ∀ close,(hs close).length=(ResponseHeadSpec.bytes (RouteRefusalSpec.status (RuntimeRequestSpans.path (MainHeaderStreamSpec.consume wire fuel []).input head)) [] 0 close).length) :
    let r := ChunkBufferSpec.consume wire arrivals head.len head.len cStart []
    ∃ received n d after raw close, received≤arrivals ∧ head.len+received=r.read ∧ raw.length=r.read ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩
        (MainHeaderStreamPlan.logs headerPlan 0 (MainHeaderStreamSpec.consume wire fuel []).received++ChunkReceivePlan.logs bodyPlan head.len received++
          UartTxLoop.reads (hs close))
        (UartTxLoop.events (ResponseHeadSpec.bytes (RouteRefusalSpec.status (RuntimeRequestSpans.path (MainHeaderStreamSpec.consume wire fuel []).input head)) [] 0 close)) ∧
      raw.take head.len=(MainHeaderStreamSpec.consume wire fuel []).input ∧ RuntimeRequestSpans.body raw head r.body.length=r.body ∧
      close=MainCloseSpec.mustClose head.minor (served+1) (RuntimeRequestSpans.raw raw r.read) (RuntimeRequestInputs.entries head) ∧
      LoopReady.At d after s (if close then 0 else served+1) := by
  obtain ⟨received,nr,a,mid,raw,lowValue,close,recvBound,exactRead,len,receive,header,payload,pc,result,captures,metadata,live,csr⟩ :=
    ReceivedFirstMatch.chunked h wire fuel arrivals head headerPlan bodyPlan headSpace headerValid accepted kind space bodyValid done
  have targetBound : head.target.1≤head.target.2 ∧ head.target.2≤head.len := by
    have := live.stored.bounds.target.2.1;have := live.stored.contained.1;omega
  have rawPath : RuntimeRequestSpans.path raw head=RuntimeRequestSpans.path (MainHeaderStreamSpec.consume wire fuel []).input head := RuntimeHeaderPrefix.path header targetBound
  have rawMethod : MainMethodSpec.decode (MainMethodBytes.token raw head.method.2)=MainMethodSpec.decode (MainMethodBytes.token (MainHeaderStreamSpec.consume wire fuel []).input head.method.2) := by
    rw [RuntimeHeaderPrefix.method header (by have := live.stored.bounds.target;have := live.stored.contained.1;omega)]
  have rawDenied : ∀ kind : RouteLiteralInfo.Kind,RuntimeRequestSpans.path raw head=RouteLiteralInfo.text kind →
      RouteSpec.allows (RouteLiteralInfo.route kind) (MainMethodSpec.decode (MainMethodBytes.token raw head.method.2))=false := by
    rw [rawPath,rawMethod];exact denied
  have rawMissing : ¬RouteSpec.relayPath (RuntimeRequestSpans.path raw head) := by rw [rawPath];exact missing
  have leading := RouteReceivedPath.received_path wire fuel head accepted
  have rawLeading : ∃ ys,RuntimeRequestSpans.path raw head=47#8::ys := by rw [rawPath];exact leading
  obtain ⟨nt,d,after,sent,ready⟩ := RuntimeRouteRefusal.contract live pc result rawDenied rawMissing rawLeading metadata (hs close) (by rw [rawPath];exact hhs close)
  rw [rawPath] at sent
  refine ⟨received,nr+nt,d,after,raw,close,recvBound,exactRead,len,?_,header,payload,live.closeSpec,ready⟩
  simpa only [List.nil_append,List.append_assoc] using receive.trans sent
end E5R.Thermostat.ReceivedRouteRefusalCycle
