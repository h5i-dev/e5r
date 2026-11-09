import Projects.thermostat.RuntimeHeaderPrefix
import Projects.thermostat.ReceivedFirstMatch
import Projects.thermostat.RuntimeHeadTransaction
set_option autoImplicit false
namespace E5R.Thermostat.ReceivedHeadCycle
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board

/-- One complete actual Empty HEAD/state request and exact HTTP reply returns
    to the reusable receive boundary. Path/method conditions are pure bytes. -/
theorem empty {c ram s served} (h : LoopReady.At c ram s served)
    (wire : Nat → BitVec 8) (fuel : Nat) (head : Head) (plan : MainHeaderStreamPlan.Plan)
    (space : fuel≤2048) (valid : MainHeaderStreamPlan.Valid plan wire 0 fuel)
    (accepted : (MainHeaderStreamSpec.consume wire fuel []).result=.done head) (kind : head.framing=.empty)
    (route : RuntimeRequestSpans.path (MainHeaderStreamSpec.consume wire fuel []).input head=WireSpec.ascii "/state")
    (method : MainMethodSpec.decode (MainMethodBytes.token (MainHeaderStreamSpec.consume wire fuel []).input head.method.2)=.head)
    (hs : Bool → List UartTxLoop.Slot) (bs : List UartTxLoop.Slot)
    (hhs : ∀ close,(hs close).length=(ResponseHeadSpec.bytes 200 (WireSpec.ascii "application/json") (ReplyJson.snapshot s).length close).length)
    (hbs : bs.length=0) :
    let input := (MainHeaderStreamSpec.consume wire fuel []).input
    ∃ n d after close, Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩
      (MainHeaderStreamPlan.logs plan 0 (MainHeaderStreamSpec.consume wire fuel []).received++UartTxLoop.reads (hs close)++UartTxLoop.reads bs)
      (UartTxLoop.events (ResponseHeadSpec.bytes 200 (WireSpec.ascii "application/json") (ReplyJson.snapshot s).length close)++UartTxLoop.events []) ∧
      close=MainCloseSpec.mustClose head.minor (served+1) (RuntimeRequestSpans.raw input head.len) (RuntimeRequestInputs.entries head) ∧
      LoopReady.At d after s (if close then 0 else served+1) := by
  obtain ⟨nr,a,mid,lowValue,close,received,pc,result,captures,metadata,live,csr⟩ := ReceivedFirstMatch.empty h wire fuel head plan space valid accepted kind
  have matched : a.get 10=1#32 := by simpa only [route,ite_true] using result
  obtain ⟨nt,d,after,sent,ready⟩ := RuntimeHeadTransaction.contract live pc matched captures metadata route method (hs close) bs (hhs close) hbs
  refine ⟨nr+nt,d,after,close,?_,live.closeSpec,ready⟩
  simpa only [List.nil_append,List.append_assoc] using received.trans sent

/-- Complete bounded chunked HEAD/state cycle. The original method/path are
    carried through actual body compaction by exact header-prefix equality. -/
theorem chunked {c ram s served} (h : LoopReady.At c ram s served)
    (wire : Nat → BitVec 8) (fuel arrivals : Nat) (head : Head)
    (headerPlan : MainHeaderStreamPlan.Plan) (bodyPlan : ChunkReceivePlan.Plan)
    (headSpace : fuel≤2048) (headerValid : MainHeaderStreamPlan.Valid headerPlan wire 0 fuel)
    (accepted : (MainHeaderStreamSpec.consume wire fuel []).result=.done head) (kind : head.framing=.chunked)
    (space : head.len+arrivals≤2048) (bodyValid : ChunkReceivePlan.Valid bodyPlan wire head.len arrivals)
    (done : (ChunkBufferSpec.consume wire arrivals head.len head.len cStart []).stop=.done)
    (route : RuntimeRequestSpans.path (MainHeaderStreamSpec.consume wire fuel []).input head=WireSpec.ascii "/state")
    (method : MainMethodSpec.decode (MainMethodBytes.token (MainHeaderStreamSpec.consume wire fuel []).input head.method.2)=.head)
    (hs : Bool → List UartTxLoop.Slot) (bs : List UartTxLoop.Slot)
    (hhs : ∀ close,(hs close).length=(ResponseHeadSpec.bytes 200 (WireSpec.ascii "application/json") (ReplyJson.snapshot s).length close).length)
    (hbs : bs.length=0) :
    let r := ChunkBufferSpec.consume wire arrivals head.len head.len cStart []
    ∃ received n d after raw close, received≤arrivals ∧ head.len+received=r.read ∧ raw.length=r.read ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩
        (MainHeaderStreamPlan.logs headerPlan 0 (MainHeaderStreamSpec.consume wire fuel []).received++ChunkReceivePlan.logs bodyPlan head.len received++
          UartTxLoop.reads (hs close)++UartTxLoop.reads bs)
        (UartTxLoop.events (ResponseHeadSpec.bytes 200 (WireSpec.ascii "application/json") (ReplyJson.snapshot s).length close)++UartTxLoop.events []) ∧
      raw.take head.len=(MainHeaderStreamSpec.consume wire fuel []).input ∧ RuntimeRequestSpans.body raw head r.body.length=r.body ∧
      close=MainCloseSpec.mustClose head.minor (served+1) (RuntimeRequestSpans.raw raw r.read) (RuntimeRequestInputs.entries head) ∧
      LoopReady.At d after s (if close then 0 else served+1) := by
  obtain ⟨received,nr,a,mid,raw,lowValue,close,recvBound,exactRead,len,receive,header,payload,pc,result,captures,metadata,live,csr⟩ :=
    ReceivedFirstMatch.chunked h wire fuel arrivals head headerPlan bodyPlan headSpace headerValid accepted kind space bodyValid done
  have targetBound : head.target.1≤head.target.2 ∧ head.target.2≤head.len := by
    have := live.stored.bounds.target.2.1;have := live.stored.contained.1;omega
  have rawRoute : RuntimeRequestSpans.path raw head=WireSpec.ascii "/state" := (RuntimeHeaderPrefix.path header targetBound).trans route
  have rawMethod : MainMethodSpec.decode (MainMethodBytes.token raw head.method.2)=.head := by
    rw [RuntimeHeaderPrefix.method header (by have := live.stored.bounds.target;have := live.stored.contained.1;omega)]
    exact method
  have matched : a.get 10=1#32 := by simpa only [rawRoute,ite_true] using result
  obtain ⟨nt,d,after,sent,ready⟩ := RuntimeHeadTransaction.contract live pc matched captures metadata rawRoute rawMethod (hs close) bs (hhs close) hbs
  refine ⟨received,nr+nt,d,after,raw,close,recvBound,exactRead,len,?_,header,payload,live.closeSpec,ready⟩
  simpa only [List.nil_append,List.append_assoc] using receive.trans sent
end E5R.Thermostat.ReceivedHeadCycle
