import Projects.thermostat.LoopReadTransaction
import Projects.thermostat.LoopTempTransaction
import Projects.thermostat.LoopSetpointTransaction
import Projects.thermostat.LoopModeTransaction
import Projects.thermostat.LoopRelayTransaction
import Projects.thermostat.LoopSpec
set_option autoImplicit false
namespace E5R.Thermostat.Firmware
open E5R E5R.Thermostat HttpRequestSpec ApiRequestSpec MainHeaderStreamSpec

def nextReads (r : Fixed11) (served : Nat) (headerPlan : MainHeaderStreamPlan.Plan) (bodyPlan : MainLengthStreamPlan.Plan)
    (hs : Bool → List UartTxLoop.Slot) (bs : List UartTxLoop.Slot) :=
  (MainHeaderStreamPlan.logs headerPlan 0 r.headBytes.length++MainLengthStreamPlan.logs bodyPlan r.headBytes.length r.body.length)++
    (UartTxLoop.reads (hs (LoopSpec.close r served))++UartTxLoop.reads bs)

/-- T2 induction step for all five unchanged T1 API pairs. Byte grammar,
    actual counter/layout/router/auth/command facts and the reusable next UART
    boundary are derived along the real ELF execution. -/
theorem next_request (r : Fixed11) {c : Core} {ram : Word → BitVec 8} {s : Spec.Snapshot} {served : Nat}
    (h : LoopReady.At c ram s served) (wire : Nat → BitVec 8)
    (headerPlan : MainHeaderStreamPlan.Plan) (bodyPlan : MainLengthStreamPlan.Plan)
    (delivers : ∀ k (hk : k<r.bytes.length), wire k=r.bytes[k]'hk)
    (headerValid : MainHeaderStreamPlan.Valid headerPlan wire 0 r.headBytes.length)
    (bodyValid : MainLengthStreamPlan.Valid bodyPlan wire r.headBytes.length r.body.length)
    (hs : Bool → List UartTxLoop.Slot) (bs : List UartTxLoop.Slot)
    (hhs : ∀ close, (hs close).length=(ResponseHeadSpec.bytes (r.reply s).status (r.reply s).mime (r.reply s).payload.length close).length)
    (hbs : bs.length=(r.reply s).payload.length) :
    ∃ n d after, Observed.Steps UartPlatform.board img n ⟨c,ram⟩ ⟨d,after⟩
      (nextReads r served headerPlan bodyPlan hs bs)
      (UartTxLoop.events (ResponseHeadSpec.bytes (r.reply s).status (r.reply s).mime (r.reply s).payload.length (LoopSpec.close r served))++
        UartTxLoop.events (r.reply s).payload) ∧
      Observed.input (nextReads r served headerPlan bodyPlan hs bs)=r.bytes ∧
      LoopReady.At d after (r.reply s).state (LoopSpec.nextCount r served) := by
  obtain ⟨first,a,mid,receive,request,capacity,routes,headLimit,bodyLimit⟩ := LoopReceiveRequest.contract r h wire headerPlan bodyPlan delivers headerValid bodyValid
  have metadata := LoopTransactionMemory.request request capacity routes headLimit bodyLimit
  have path := ApiRouting.path r
  have method := ApiRouting.method_case r
  have run : ∃ n d after close,
      Observed.Steps UartPlatform.board img n ⟨a,mid⟩ ⟨d,after⟩ (UartTxLoop.reads (hs close)++UartTxLoop.reads bs)
        (UartTxLoop.events (ResponseHeadSpec.bytes (r.reply s).status (r.reply s).mime (r.reply s).payload.length close)++UartTxLoop.events (r.reply s).payload) ∧
      close=LoopSpec.close r served ∧ LoopReady.At d after (r.reply s).state (if close then 0 else served+1) := by
    cases routeEq : r.route with
    | state =>
      have expected : r.reply s=⟨s,200,WireSpec.ascii "application/json",ReplyJson.snapshot s⟩ := by unfold Fixed11.reply;rw [routeEq]
      obtain ⟨n,d,after,close,steps,closure,ready⟩ := LoopReadTransaction.contract request metadata
        (by simpa only [routeEq,Route.path] using path) (by simpa only [routeEq,ApiRouting.method] using method)
        hs bs (by simpa only [expected] using hhs) (by simpa only [expected] using hbs)
      simp only [ApiRouting.raw,ApiRouting.entries] at closure
      refine ⟨n,d,after,close,?_,closure,?_⟩
      · simpa only [expected] using steps
      · simpa only [expected] using ready
    | temp =>
      have expected : ApiWriteHttpSpec.run s (WireSpec.ascii "/temp") (none)
          (MainRequestSpans.raw r.bytes r.head r.body.length) (MainRequestSpans.body r.bytes r.head r.body.length) (MainRequestInputs.entries r.head)=r.reply s := by
        rw [ApiRouting.raw,ApiRouting.body,ApiRouting.entries]
        simp only [Fixed11.reply,routeEq,Route.path,Route.capture,MainRelayCaptured.path]
      obtain ⟨n,d,after,close,steps,closure,ready⟩ := LoopTempTransaction.contract request metadata
        (by simpa only [routeEq,Route.path,MainRelayCaptured.path] using path) (by simpa only [routeEq,ApiRouting.method] using method)
        hs bs (by simpa only [expected] using hhs) (by simpa only [expected] using hbs)
      rw [expected] at steps ready
      simp only [ApiRouting.raw,ApiRouting.entries] at closure
      exact ⟨n,d,after,close,steps,closure,ready⟩
    | setpoint =>
      have expected : ApiWriteHttpSpec.run s (WireSpec.ascii "/setpoint") (none)
          (MainRequestSpans.raw r.bytes r.head r.body.length) (MainRequestSpans.body r.bytes r.head r.body.length) (MainRequestInputs.entries r.head)=r.reply s := by
        rw [ApiRouting.raw,ApiRouting.body,ApiRouting.entries]
        simp only [Fixed11.reply,routeEq,Route.path,Route.capture,MainRelayCaptured.path]
      obtain ⟨n,d,after,close,steps,closure,ready⟩ := LoopSetpointTransaction.contract request metadata
        (by simpa only [routeEq,Route.path,MainRelayCaptured.path] using path) (by simpa only [routeEq,ApiRouting.method] using method)
        hs bs (by simpa only [expected] using hhs) (by simpa only [expected] using hbs)
      rw [expected] at steps ready
      simp only [ApiRouting.raw,ApiRouting.entries] at closure
      exact ⟨n,d,after,close,steps,closure,ready⟩
    | mode =>
      have expected : ApiWriteHttpSpec.run s (WireSpec.ascii "/mode") (none)
          (MainRequestSpans.raw r.bytes r.head r.body.length) (MainRequestSpans.body r.bytes r.head r.body.length) (MainRequestInputs.entries r.head)=r.reply s := by
        rw [ApiRouting.raw,ApiRouting.body,ApiRouting.entries]
        simp only [Fixed11.reply,routeEq,Route.path,Route.capture,MainRelayCaptured.path]
      obtain ⟨n,d,after,close,steps,closure,ready⟩ := LoopModeTransaction.contract request metadata
        (by simpa only [routeEq,Route.path,MainRelayCaptured.path] using path) (by simpa only [routeEq,ApiRouting.method] using method)
        hs bs (by simpa only [expected] using hhs) (by simpa only [expected] using hbs)
      rw [expected] at steps ready
      simp only [ApiRouting.raw,ApiRouting.entries] at closure
      exact ⟨n,d,after,close,steps,closure,ready⟩
    | relay segment =>
      have expected : ApiWriteHttpSpec.run s (MainRelayCaptured.path segment) (some segment)
          (MainRequestSpans.raw r.bytes r.head r.body.length) (MainRequestSpans.body r.bytes r.head r.body.length) (MainRequestInputs.entries r.head)=r.reply s := by
        rw [ApiRouting.raw,ApiRouting.body,ApiRouting.entries]
        simp only [Fixed11.reply,routeEq,Route.path,Route.capture,MainRelayCaptured.path]
      have valid : segment≠[] ∧ ∀ b∈segment, HttpRequestSpec.isTargetByte b.toNat=true ∧ b≠47#8 ∧ b≠63#8 := by
        simpa only [routeEq,Route.Valid] using r.routeValid
      obtain ⟨n,d,after,close,steps,closure,ready⟩ := LoopRelayTransaction.contract segment valid.1
        (fun b hb => (valid.2 b hb).2.1) request metadata
        (by simpa only [routeEq,Route.path,MainRelayCaptured.path] using path) (by simpa only [routeEq,ApiRouting.method] using method)
        hs bs (by simpa only [expected] using hhs) (by simpa only [expected] using hbs)
      rw [expected] at steps ready
      simp only [ApiRouting.raw,ApiRouting.entries] at closure
      exact ⟨n,d,after,close,steps,closure,ready⟩
  obtain ⟨last,d,after,close,sent,closure,ready⟩ := run
  subst close
  have headLogs := MainHeaderStreamPlan.logs_wire headerPlan wire 0 r.headBytes.length r.headBytes.length headerValid (Nat.le_refl _)
  have bodyLogs := MainLengthStreamPlan.logs_wire bodyPlan wire r.headBytes.length r.body.length r.body.length bodyValid (Nat.le_refl _)
  have headerBytes := ApiConsume.arrivals_piece wire r.headBytes 0 r.headBytes.length (by omega) (ApiConsume.head_agree r wire delivers)
  simp only [List.drop_zero,List.take_length] at headerBytes
  have bodyBytes := ApiConsume.arrivals_piece wire r.bytes r.headBytes.length r.body.length
    (by change r.headBytes.length+r.body.length≤(r.headBytes++r.body).length;rw [List.length_append];exact Nat.le_refl _) delivers
  simp only [Fixed11.bytes,List.drop_left,List.take_length] at bodyBytes
  refine ⟨first+last,d,after,?_,?_,ready⟩
  · simpa only [nextReads,List.nil_append] using receive.trans sent
  · simp only [nextReads,Observed.input_append,UartTxLoop.no_input,List.append_nil,headLogs,bodyLogs,headerBytes,bodyBytes]
    rfl
end E5R.Thermostat.Firmware
