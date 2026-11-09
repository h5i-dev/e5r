import Projects.thermostat.CompleteRequestSpec
import Projects.thermostat.ReceivedCompleteCycle
set_option autoImplicit false
namespace E5R.Thermostat.CompleteRequestSchedules
open E5R E5R.Thermostat HttpRequestSpec CompleteRequestSpec

structure One (r : Request) (s : Spec.Snapshot) where
  headerPlan : MainHeaderStreamPlan.Plan
  headerValid : MainHeaderStreamPlan.Valid headerPlan r.wire 0 r.fuel
  lengthPlan : MainLengthStreamPlan.Plan
  chunkPlan : ChunkReceivePlan.Plan
  bodyValid : match r.framed with
    | .empty _ => True
    | .length amount _ => MainLengthStreamPlan.Valid lengthPlan r.wire r.head.len amount
    | .chunked budget _ _ _ => ChunkReceivePlan.Valid chunkPlan r.wire r.head.len budget
  hs : Bool → List UartTxLoop.Slot
  bs : List UartTxLoop.Slot
  headerLengths : ∀ close,(hs close).length=(ResponseHeadSpec.bytes (r.reply s).status (r.reply s).mime (r.reply s).payload.length close).length
  bodyLength : bs.length=(ResponseHeadSpec.body (r.reply s).status r.isHead (r.reply s).payload).length

def bodyReads (r : Request) (lp : MainLengthStreamPlan.Plan) (cp : ChunkReceivePlan.Plan) : List Observed.Read := match r.framed with
  | .empty _ => []
  | .length amount _ => MainLengthStreamPlan.logs lp r.head.len amount
  | .chunked budget _ _ _ => ChunkReceivePlan.logs cp r.head.len ((ChunkBufferSpec.consume r.wire budget r.head.len r.head.len cStart []).read-r.head.len)

def rx {r s} (one : One r s) :=
  MainHeaderStreamPlan.logs one.headerPlan 0 (MainHeaderStreamSpec.consume r.wire r.fuel []).received++bodyReads r one.lengthPlan one.chunkPlan

def reads {r s} (served : Nat) (one : One r s) :=
  rx one++UartTxLoop.reads (one.hs (r.close served))++UartTxLoop.reads one.bs

/-- The actual completed-request contract uniformly selects every route/method
    and all control/refusal outcomes from the pure input bytes. -/
theorem execute {r : Request} {s served c ram} (one : One r s) (h : LoopReady.At c ram s served) :
    ∃ n d after,Observed.Steps UartPlatform.board img n ⟨c,ram⟩ ⟨d,after⟩ (reads served one)
      (UartTxLoop.events (r.output s served)) ∧ LoopReady.At d after (r.reply s).state (r.nextCount served) := by
  have headEq : RuntimeRouteTransaction.isHead r.original r.head=r.isHead := rfl
  have entryEq : RuntimeRequestInputs.entry=MainRequestInputs.entry := rfl
  have run : ReceivedCompleteCycle.Done c ram s served r.original r.body r.head (rx one) one.hs one.bs := by
    cases frameEq : r.framed with
    | empty kind =>
      have t := ReceivedCompleteCycle.empty h r.wire r.fuel r.head one.headerPlan r.space one.headerValid r.accepted kind one.hs one.bs
        (by simpa +instances only [ReceivedCompleteCycle.reply,Request.reply,RuntimeRequestSpans.path,MainRequestSpans.path,RuntimeRequestInputs.entries,MainRequestInputs.entries,entryEq,Request.body,frameEq,Request.original] using one.headerLengths)
        (by simpa +instances only [ReceivedCompleteCycle.reply,Request.reply,RuntimeRequestSpans.path,MainRequestSpans.path,RuntimeRequestInputs.entries,MainRequestInputs.entries,entryEq,Request.body,frameEq,←headEq,Request.original] using one.bodyLength)
      simpa +instances only [rx,bodyReads,frameEq,List.append_nil,Request.original,Request.body] using t
    | length amount kind =>
      have valid : MainLengthStreamPlan.Valid one.lengthPlan r.wire r.head.len amount := by simpa +instances only [frameEq] using one.bodyValid
      have t := ReceivedCompleteCycle.length h r.wire r.fuel r.head amount one.headerPlan one.lengthPlan r.space one.headerValid r.accepted kind valid one.hs one.bs
        (by simpa +instances only [ReceivedCompleteCycle.reply,Request.reply,RuntimeRequestSpans.path,MainRequestSpans.path,RuntimeRequestInputs.entries,MainRequestInputs.entries,entryEq,Request.body,frameEq,Request.original] using one.headerLengths)
        (by simpa +instances only [ReceivedCompleteCycle.reply,Request.reply,RuntimeRequestSpans.path,MainRequestSpans.path,RuntimeRequestInputs.entries,MainRequestInputs.entries,entryEq,Request.body,frameEq,←headEq,Request.original] using one.bodyLength)
      simpa +instances only [rx,bodyReads,frameEq,Request.original,Request.body] using t
    | chunked budget kind space done =>
      have valid : ChunkReceivePlan.Valid one.chunkPlan r.wire r.head.len budget := by simpa +instances only [frameEq] using one.bodyValid
      obtain ⟨received,bound,used,t⟩ := ReceivedCompleteCycle.chunked h r.wire r.fuel budget r.head one.headerPlan one.chunkPlan r.space one.headerValid r.accepted kind space valid done one.hs one.bs
        (by simpa +instances only [ReceivedCompleteCycle.reply,Request.reply,RuntimeRequestSpans.path,MainRequestSpans.path,RuntimeRequestInputs.entries,MainRequestInputs.entries,entryEq,Request.body,frameEq,Request.original] using one.headerLengths)
        (by simpa +instances only [ReceivedCompleteCycle.reply,Request.reply,RuntimeRequestSpans.path,MainRequestSpans.path,RuntimeRequestInputs.entries,MainRequestInputs.entries,entryEq,Request.body,frameEq,←headEq,Request.original] using one.bodyLength)
      have exactReceived : received=(ChunkBufferSpec.consume r.wire budget r.head.len r.head.len cStart []).read-r.head.len := by omega
      subst received
      simpa +instances only [rx,bodyReads,frameEq,Request.original,Request.body] using t
  obtain ⟨n,d,after,close,trace,closeEq,ready⟩ := run
  change close=r.close served at closeEq
  subst close
  refine ⟨n,d,after,?_,ready⟩
  simpa +instances only [reads,Request.output,UartTxLoop.events,RuntimeRequestSpans.path,MainRequestSpans.path,RuntimeRequestInputs.entries,MainRequestInputs.entries,entryEq,List.map_append,ReceivedCompleteCycle.reply,Request.reply,RuntimeRequestSpans.path,MainRequestSpans.path,RuntimeRequestInputs.entries,MainRequestInputs.entries,entryEq,RuntimeRouteTransaction.isHead,Request.isHead] using trace


/-- Projection contains only actual RBR bytes, never LSR readiness polls or TX. -/
theorem accepted {r s} (one : One r s) (served : Nat) : Observed.input (reads served one)=r.input := by
  have bodyInput : Observed.input (bodyReads r one.lengthPlan one.chunkPlan)=MainHeaderStreamSpec.arrivals r.wire r.head.len r.bodyCount := by
    cases frameEq : r.framed with
    | empty kind => simp only [bodyReads,Request.bodyCount,frameEq,Observed.input,MainHeaderStreamSpec.arrivals,List.filterMap_nil,List.range_zero,List.map_nil]
    | length amount kind =>
      have valid : MainLengthStreamPlan.Valid one.lengthPlan r.wire r.head.len amount := by simpa only [frameEq] using one.bodyValid
      simpa only [bodyReads,Request.bodyCount,frameEq] using MainLengthStreamPlan.logs_wire one.lengthPlan r.wire r.head.len amount amount valid (Nat.le_refl _)
    | chunked budget kind space done =>
      have valid : ChunkReceivePlan.Valid one.chunkPlan r.wire r.head.len budget := by simpa only [frameEq] using one.bodyValid
      simp only [bodyReads,Request.bodyCount,frameEq,ChunkReceivePlan.logs_input,MainHeaderStreamSpec.arrivals]
      apply List.map_congr_left
      intro i member
      have index := List.mem_range.mp member
      have positions := ChunkBufferSpec.positions r.wire budget r.head.len r.head.len cStart []
      exact (valid (r.head.len+i) (by omega) (by omega)).2.2
  have headerInput := MainHeaderStreamPlan.logs_wire one.headerPlan r.wire 0 _ r.fuel one.headerValid (MainHeaderStreamSpec.received_le r.wire r.fuel [])
  have headerBytes := MainHeaderStreamSpec.input_bytes r.wire r.fuel []
  simp only [List.length_nil,List.nil_append] at headerBytes
  simp only [reads,rx,Observed.input_append,UartTxLoop.no_input,List.append_nil,headerInput,bodyInput,Request.input,Request.original,headerBytes]
end E5R.Thermostat.CompleteRequestSchedules
