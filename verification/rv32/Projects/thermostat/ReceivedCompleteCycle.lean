import Projects.thermostat.ReceivedFirstMatch
import Projects.thermostat.ReceivedLengthFirstMatch
import Projects.thermostat.RuntimeRouteCorrespondence
import Projects.thermostat.HeadConsumedExtent
set_option autoImplicit false
namespace E5R.Thermostat.ReceivedCompleteCycle
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board

def reply (s : Spec.Snapshot) (original body : List (BitVec 8)) (head : Head) :=
  RouteSpec.reply s (MainMethodSpec.decode (MainMethodBytes.token original head.method.2))
    (RuntimeRequestSpans.path original head) original body (RuntimeRequestInputs.entries head)

def Done (c : Core) (ram : Word → BitVec 8) (s : Spec.Snapshot) (served : Nat)
    (original body : List (BitVec 8)) (head : Head) (rx : List Observed.Read)
    (hs : Bool → List UartTxLoop.Slot) (bs : List UartTxLoop.Slot) : Prop :=
  let response := reply s original body head
  ∃ n d after close, Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩
    (rx++UartTxLoop.reads (hs close)++UartTxLoop.reads bs)
    (UartTxLoop.events (ResponseHeadSpec.bytes response.status response.mime response.payload.length close)++
      UartTxLoop.events (ResponseHeadSpec.body response.status (RuntimeRouteTransaction.isHead original head) response.payload)) ∧
    close=MainCloseSpec.mustClose head.minor (served+1) original (RuntimeRequestInputs.entries head) ∧
    LoopReady.At d after response.state (if close then 0 else served+1)

/-- Original wire header and decoded body determine every route, refusal,
    committed state and response. Caller memory/layout comes from reception. -/
theorem finish {c ram s served original body head rx a mid input amount rawUsed lowValue close used nr}
    (received : Observed.Steps B img nr ⟨c,ram⟩ ⟨a,mid⟩ rx [])
    (h : RuntimeRouteEnvelope.At a mid input s head amount rawUsed (served+1) lowValue close)
    (pc : a.pc=0x800013d2#32)
    (result : a.get 10=(if RuntimeRequestSpans.path input head=WireSpec.ascii "/state" then 1#32 else 0#32))
    (captures : a.get 11=0#32) (metadata : LoopTransactionMemory.At mid used)
    (same : input.take head.len=original) (payload : RuntimeRequestSpans.body input head amount=body)
    (leading : ∃ ys,RuntimeRequestSpans.path original head=47#8::ys)
    (hs : Bool → List UartTxLoop.Slot) (bs : List UartTxLoop.Slot)
    (hhs : ∀ close,(hs close).length=(ResponseHeadSpec.bytes (reply s original body head).status (reply s original body head).mime (reply s original body head).payload.length close).length)
    (hbs : bs.length=(ResponseHeadSpec.body (reply s original body head).status (RuntimeRouteTransaction.isHead original head) (reply s original body head).payload).length) :
    Done c ram s served original body head rx hs bs := by
  have responseEq : RuntimeRouteTransaction.reply s input head amount rawUsed=reply s original body head := RuntimeRouteCorrespondence.reply h same payload
  have headEq := RuntimeRouteCorrespondence.isHead h same
  have pathEq := RuntimeRouteCorrespondence.path h same
  have fullLeading : ∃ ys,RuntimeRequestSpans.path input head=47#8::ys := by rw [pathEq];exact leading
  obtain ⟨nt,d,after,sent,ready⟩ := RuntimeRouteTransaction.contract h pc result captures fullLeading metadata (hs close) bs
    (by simpa only [responseEq] using hhs close) (by simpa only [responseEq,headEq] using hbs)
  refine ⟨nr+nt,d,after,close,?_,RuntimeRouteCorrespondence.close h same,?_⟩
  · simpa only [responseEq,headEq,List.nil_append,List.append_assoc] using received.trans sent
  · simpa only [responseEq] using ready

/-- Every accepted empty-framed request executes the actual full response and
    returns to the reusable receive boundary, with no selected-route premise. -/
theorem empty {c ram s served} (h : LoopReady.At c ram s served)
    (wire : Nat → BitVec 8) (fuel : Nat) (head : Head) (plan : MainHeaderStreamPlan.Plan)
    (space : fuel≤2048) (valid : MainHeaderStreamPlan.Valid plan wire 0 fuel)
    (accepted : (MainHeaderStreamSpec.consume wire fuel []).result=.done head) (kind : head.framing=.empty)
    (hs : Bool → List UartTxLoop.Slot) (bs : List UartTxLoop.Slot)
    (hhs : ∀ close,(hs close).length=(ResponseHeadSpec.bytes (reply s (MainHeaderStreamSpec.consume wire fuel []).input [] head).status (reply s (MainHeaderStreamSpec.consume wire fuel []).input [] head).mime (reply s (MainHeaderStreamSpec.consume wire fuel []).input [] head).payload.length close).length)
    (hbs : bs.length=(ResponseHeadSpec.body (reply s (MainHeaderStreamSpec.consume wire fuel []).input [] head).status (RuntimeRouteTransaction.isHead (MainHeaderStreamSpec.consume wire fuel []).input head) (reply s (MainHeaderStreamSpec.consume wire fuel []).input [] head).payload).length) :
    Done c ram s served (MainHeaderStreamSpec.consume wire fuel []).input [] head
      (MainHeaderStreamPlan.logs plan 0 (MainHeaderStreamSpec.consume wire fuel []).received) hs bs := by
  obtain ⟨nr,a,mid,lowValue,close,received,pc,result,captures,metadata,live,csr⟩ := ReceivedFirstMatch.empty h wire fuel head plan space valid accepted kind
  have same : (MainHeaderStreamSpec.consume wire fuel []).input.take head.len=(MainHeaderStreamSpec.consume wire fuel []).input := by
    rw [←HeadConsumedExtent.receive_exact wire fuel head accepted,List.take_length]
  have payload : RuntimeRequestSpans.body (MainHeaderStreamSpec.consume wire fuel []).input head 0=[] := by
    simp only [RuntimeRequestSpans.body,List.take_zero]
  exact finish received live pc result captures metadata same payload (RouteReceivedPath.received_path wire fuel head accepted) hs bs hhs hbs

/-- Every accepted Content-Length request, including arbitrary decoded bodies,
    routes through actual authentication, control and exact HTTP output. -/
theorem length {c ram s served} (h : LoopReady.At c ram s served)
    (wire : Nat → BitVec 8) (fuel : Nat) (head : Head) (amount : Nat)
    (headerPlan : MainHeaderStreamPlan.Plan) (bodyPlan : MainLengthStreamPlan.Plan)
    (space : fuel≤2048) (headerValid : MainHeaderStreamPlan.Valid headerPlan wire 0 fuel)
    (accepted : (MainHeaderStreamSpec.consume wire fuel []).result=.done head) (framing : head.framing=.length amount)
    (bodyValid : MainLengthStreamPlan.Valid bodyPlan wire head.len amount)
    (hs : Bool → List UartTxLoop.Slot) (bs : List UartTxLoop.Slot)
    (hhs : ∀ close,(hs close).length=(ResponseHeadSpec.bytes (reply s (MainHeaderStreamSpec.consume wire fuel []).input (MainHeaderStreamSpec.arrivals wire head.len amount) head).status (reply s (MainHeaderStreamSpec.consume wire fuel []).input (MainHeaderStreamSpec.arrivals wire head.len amount) head).mime (reply s (MainHeaderStreamSpec.consume wire fuel []).input (MainHeaderStreamSpec.arrivals wire head.len amount) head).payload.length close).length)
    (hbs : bs.length=(ResponseHeadSpec.body (reply s (MainHeaderStreamSpec.consume wire fuel []).input (MainHeaderStreamSpec.arrivals wire head.len amount) head).status (RuntimeRouteTransaction.isHead (MainHeaderStreamSpec.consume wire fuel []).input head) (reply s (MainHeaderStreamSpec.consume wire fuel []).input (MainHeaderStreamSpec.arrivals wire head.len amount) head).payload).length) :
    Done c ram s served (MainHeaderStreamSpec.consume wire fuel []).input (MainHeaderStreamSpec.arrivals wire head.len amount) head
      (MainHeaderStreamPlan.logs headerPlan 0 (MainHeaderStreamSpec.consume wire fuel []).received++MainLengthStreamPlan.logs bodyPlan head.len amount) hs bs := by
  obtain ⟨nr,a,mid,lowValue,close,received,pc,result,captures,live,metadata,same,payload⟩ := ReceivedLengthFirstMatch.contract h wire fuel head amount headerPlan bodyPlan space headerValid accepted framing bodyValid
  exact finish received live pc result captures metadata same payload (RouteReceivedPath.received_path wire fuel head accepted) hs bs hhs hbs

/-- Complete bounded chunked requests retain the original header for auth and
    close policy while the response is specified by the independently dechunked
    body. Encoded input extent is never identified with decoded body length. -/
theorem chunked {c ram s served} (h : LoopReady.At c ram s served)
    (wire : Nat → BitVec 8) (fuel arrivals : Nat) (head : Head)
    (headerPlan : MainHeaderStreamPlan.Plan) (bodyPlan : ChunkReceivePlan.Plan)
    (headSpace : fuel≤2048) (headerValid : MainHeaderStreamPlan.Valid headerPlan wire 0 fuel)
    (accepted : (MainHeaderStreamSpec.consume wire fuel []).result=.done head) (kind : head.framing=.chunked)
    (space : head.len+arrivals≤2048) (bodyValid : ChunkReceivePlan.Valid bodyPlan wire head.len arrivals)
    (done : (ChunkBufferSpec.consume wire arrivals head.len head.len cStart []).stop=.done)
    (hs : Bool → List UartTxLoop.Slot) (bs : List UartTxLoop.Slot)
    (hhs : ∀ close,(hs close).length=(ResponseHeadSpec.bytes (reply s (MainHeaderStreamSpec.consume wire fuel []).input (ChunkBufferSpec.consume wire arrivals head.len head.len cStart []).body head).status (reply s (MainHeaderStreamSpec.consume wire fuel []).input (ChunkBufferSpec.consume wire arrivals head.len head.len cStart []).body head).mime (reply s (MainHeaderStreamSpec.consume wire fuel []).input (ChunkBufferSpec.consume wire arrivals head.len head.len cStart []).body head).payload.length close).length)
    (hbs : bs.length=(ResponseHeadSpec.body (reply s (MainHeaderStreamSpec.consume wire fuel []).input (ChunkBufferSpec.consume wire arrivals head.len head.len cStart []).body head).status (RuntimeRouteTransaction.isHead (MainHeaderStreamSpec.consume wire fuel []).input head) (reply s (MainHeaderStreamSpec.consume wire fuel []).input (ChunkBufferSpec.consume wire arrivals head.len head.len cStart []).body head).payload).length) :
    ∃ received,received≤arrivals ∧ head.len+received=(ChunkBufferSpec.consume wire arrivals head.len head.len cStart []).read ∧
      Done c ram s served (MainHeaderStreamSpec.consume wire fuel []).input (ChunkBufferSpec.consume wire arrivals head.len head.len cStart []).body head
        (MainHeaderStreamPlan.logs headerPlan 0 (MainHeaderStreamSpec.consume wire fuel []).received++ChunkReceivePlan.logs bodyPlan head.len received) hs bs := by
  obtain ⟨received,nr,a,mid,raw,lowValue,close,recvBound,exactRead,len,receive,same,payload,pc,result,captures,metadata,live,csr⟩ :=
    ReceivedFirstMatch.chunked h wire fuel arrivals head headerPlan bodyPlan headSpace headerValid accepted kind space bodyValid done
  exact ⟨received,recvBound,exactRead,finish receive live pc result captures metadata same payload (RouteReceivedPath.received_path wire fuel head accepted) hs bs hhs hbs⟩
end E5R.Thermostat.ReceivedCompleteCycle
