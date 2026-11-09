import Projects.thermostat.ReceivedFirstMatch
import Projects.thermostat.RuntimeLiteralWriteTransaction
import Projects.thermostat.RuntimeHeaderLookup
set_option autoImplicit false
namespace E5R.Thermostat.ReceivedLiteralWriteCycle
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board

def reply (kind : RouteLiteralInfo.Kind) (s : Spec.Snapshot) (original body : List (BitVec 8)) (head : Head) :=
  ApiWriteHttpSpec.run s (RouteLiteralInfo.text kind) none original body (RuntimeRequestInputs.entries head)

/-- Accepted Empty literal write request: all auth/body/kernel outcomes and
    exact HTTP bytes, from real receive to reusable next-request boundary. -/
theorem empty {c ram s served} (h : LoopReady.At c ram s served)
    (wire : Nat → BitVec 8) (fuel : Nat) (head : Head) (plan : MainHeaderStreamPlan.Plan)
    (space : fuel≤2048) (valid : MainHeaderStreamPlan.Valid plan wire 0 fuel)
    (accepted : (MainHeaderStreamSpec.consume wire fuel []).result=.done head) (framing : head.framing=.empty)
    (kind : RouteLiteralInfo.Kind) (write : kind≠.state)
    (route : RuntimeRequestSpans.path (MainHeaderStreamSpec.consume wire fuel []).input head=RouteLiteralInfo.text kind)
    (method : RouteSpec.allows (RouteLiteralInfo.route kind) (MainMethodSpec.decode (MainMethodBytes.token (MainHeaderStreamSpec.consume wire fuel []).input head.method.2))=true)
    (hs : Bool → List UartTxLoop.Slot) (bs : List UartTxLoop.Slot)
    (hhs : ∀ close,(hs close).length=(ResponseHeadSpec.bytes
      (reply kind s ((MainHeaderStreamSpec.consume wire fuel []).input.take head.len) [] head).status
      (reply kind s ((MainHeaderStreamSpec.consume wire fuel []).input.take head.len) [] head).mime
      (reply kind s ((MainHeaderStreamSpec.consume wire fuel []).input.take head.len) [] head).payload.length close).length)
    (hbs : bs.length=(reply kind s ((MainHeaderStreamSpec.consume wire fuel []).input.take head.len) [] head).payload.length) :
    let response := reply kind s ((MainHeaderStreamSpec.consume wire fuel []).input.take head.len) [] head
    ∃ n d after close,Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩
      (MainHeaderStreamPlan.logs plan 0 (MainHeaderStreamSpec.consume wire fuel []).received++UartTxLoop.reads (hs close)++UartTxLoop.reads bs)
      (UartTxLoop.events (ResponseHeadSpec.bytes response.status response.mime response.payload.length close)++UartTxLoop.events response.payload) ∧
      close=MainCloseSpec.mustClose head.minor (served+1) ((MainHeaderStreamSpec.consume wire fuel []).input.take head.len) (RuntimeRequestInputs.entries head) ∧
      LoopReady.At d after response.state (if close then 0 else served+1) := by
  obtain ⟨nr,a,mid,lowValue,close,receive,pc,result,captures,metadata,live,csr⟩ := ReceivedFirstMatch.empty h wire fuel head plan space valid accepted framing
  have leading := RouteReceivedPath.received_path wire fuel head accepted
  obtain ⟨nt,d,after,sent,ready⟩ := RuntimeLiteralWriteTransaction.contract kind write live pc result route method leading metadata (hs close) bs (hhs close) hbs
  refine ⟨nr+nt,d,after,close,?_,live.closeSpec,ready⟩
  simpa only [RuntimeLiteralWriteTransaction.reply,reply,RuntimeRequestSpans.raw,RuntimeRequestSpans.body,List.take_zero,List.nil_append,List.append_assoc] using receive.trans sent

/-- Chunked literal writes use the original header for pure auth/Connection
    policy and independently dechunked bytes for command decoding. -/
theorem chunked {c ram s served} (h : LoopReady.At c ram s served)
    (wire : Nat → BitVec 8) (fuel arrivals : Nat) (head : Head)
    (headerPlan : MainHeaderStreamPlan.Plan) (bodyPlan : ChunkReceivePlan.Plan)
    (headSpace : fuel≤2048) (headerValid : MainHeaderStreamPlan.Valid headerPlan wire 0 fuel)
    (accepted : (MainHeaderStreamSpec.consume wire fuel []).result=.done head) (framing : head.framing=.chunked)
    (space : head.len+arrivals≤2048) (bodyValid : ChunkReceivePlan.Valid bodyPlan wire head.len arrivals)
    (done : (ChunkBufferSpec.consume wire arrivals head.len head.len cStart []).stop=.done)
    (kind : RouteLiteralInfo.Kind) (write : kind≠.state)
    (route : RuntimeRequestSpans.path (MainHeaderStreamSpec.consume wire fuel []).input head=RouteLiteralInfo.text kind)
    (method : RouteSpec.allows (RouteLiteralInfo.route kind) (MainMethodSpec.decode (MainMethodBytes.token (MainHeaderStreamSpec.consume wire fuel []).input head.method.2))=true)
    (hs : Bool → List UartTxLoop.Slot) (bs : List UartTxLoop.Slot)
    (hhs : ∀ close,(hs close).length=(ResponseHeadSpec.bytes
      (reply kind s (MainHeaderStreamSpec.consume wire fuel []).input (ChunkBufferSpec.consume wire arrivals head.len head.len cStart []).body head).status
      (reply kind s (MainHeaderStreamSpec.consume wire fuel []).input (ChunkBufferSpec.consume wire arrivals head.len head.len cStart []).body head).mime
      (reply kind s (MainHeaderStreamSpec.consume wire fuel []).input (ChunkBufferSpec.consume wire arrivals head.len head.len cStart []).body head).payload.length close).length)
    (hbs : bs.length=(reply kind s (MainHeaderStreamSpec.consume wire fuel []).input (ChunkBufferSpec.consume wire arrivals head.len head.len cStart []).body head).payload.length) :
    let r := ChunkBufferSpec.consume wire arrivals head.len head.len cStart []
    let response := reply kind s (MainHeaderStreamSpec.consume wire fuel []).input r.body head
    ∃ received n d after raw close,received≤arrivals ∧ head.len+received=r.read ∧ raw.length=r.read ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩
        (MainHeaderStreamPlan.logs headerPlan 0 (MainHeaderStreamSpec.consume wire fuel []).received++ChunkReceivePlan.logs bodyPlan head.len received++UartTxLoop.reads (hs close)++UartTxLoop.reads bs)
        (UartTxLoop.events (ResponseHeadSpec.bytes response.status response.mime response.payload.length close)++UartTxLoop.events response.payload) ∧
      raw.take head.len=(MainHeaderStreamSpec.consume wire fuel []).input ∧ RuntimeRequestSpans.body raw head r.body.length=r.body ∧
      close=MainCloseSpec.mustClose head.minor (served+1) (MainHeaderStreamSpec.consume wire fuel []).input (RuntimeRequestInputs.entries head) ∧
      LoopReady.At d after response.state (if close then 0 else served+1) := by
  obtain ⟨received,nr,a,mid,raw,lowValue,close,recvBound,exactRead,len,receive,header,payload,pc,result,captures,metadata,live,csr⟩ :=
    ReceivedFirstMatch.chunked h wire fuel arrivals head headerPlan bodyPlan headSpace headerValid accepted framing space bodyValid done
  have targetBound : head.target.1≤head.target.2 ∧ head.target.2≤head.len := by
    have := live.stored.bounds.target.2.1;have := live.stored.contained.1;omega
  have rawPath : RuntimeRequestSpans.path raw head=RuntimeRequestSpans.path (MainHeaderStreamSpec.consume wire fuel []).input head := RuntimeHeaderPrefix.path header targetBound
  have rawMethod : MainMethodSpec.decode (MainMethodBytes.token raw head.method.2)=MainMethodSpec.decode (MainMethodBytes.token (MainHeaderStreamSpec.consume wire fuel []).input head.method.2) := by
    rw [RuntimeHeaderPrefix.method header (by have := live.stored.bounds.target;have := live.stored.contained.1;omega)]
  have leading := RouteReceivedPath.received_path wire fuel head accepted
  have rawLeading : ∃ ys,RuntimeRequestSpans.path raw head=47#8::ys := by rw [rawPath];exact leading
  have bounds : ∀ e∈RuntimeRequestInputs.entries head,HeaderSpec.Bounds head.len e := by
    intro e member
    obtain ⟨field,inside,rfl⟩ := List.mem_map.mp member
    obtain ⟨a,b,c,d⟩ := live.stored.contained.2 field inside
    change field.ns≤field.ne ∧ field.ne≤head.len ∧ field.vs≤field.ve ∧ field.ve≤head.len
    exact ⟨by omega,by omega,c,d⟩
  have sameHead : (RuntimeRequestSpans.raw raw (ChunkBufferSpec.consume wire arrivals head.len head.len cStart []).read).take head.len=(MainHeaderStreamSpec.consume wire fuel []).input := by
    unfold RuntimeRequestSpans.raw
    rw [←len,List.take_length];exact header
  have responseEq : RuntimeLiteralWriteTransaction.reply kind s raw head (ChunkBufferSpec.consume wire arrivals head.len head.len cStart []).body.length (ChunkBufferSpec.consume wire arrivals head.len head.len cStart []).read=
      reply kind s (MainHeaderStreamSpec.consume wire fuel []).input (ChunkBufferSpec.consume wire arrivals head.len head.len cStart []).body head := by
    unfold RuntimeLiteralWriteTransaction.reply reply
    rw [payload]
    exact RuntimeHeaderLookup.write sameHead s (RouteLiteralInfo.text kind) _ none _ bounds
  have closeEq := RuntimeHeaderLookup.close sameHead head.minor (served+1) (RuntimeRequestInputs.entries head) bounds
  obtain ⟨nt,d,after,sent,ready⟩ := RuntimeLiteralWriteTransaction.contract kind write live pc result
    (rawPath.trans route) (by rw [rawMethod];exact method) rawLeading metadata (hs close) bs (by rw [responseEq];exact hhs close) (by rw [responseEq];exact hbs)
  rw [responseEq] at sent ready
  refine ⟨received,nr+nt,d,after,raw,close,recvBound,exactRead,len,?_,header,payload,live.closeSpec.trans closeEq,ready⟩
  simpa only [List.nil_append,List.append_assoc] using receive.trans sent
end E5R.Thermostat.ReceivedLiteralWriteCycle
