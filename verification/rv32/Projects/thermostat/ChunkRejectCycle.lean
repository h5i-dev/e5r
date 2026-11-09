import Projects.thermostat.ChunkRejectBody
import Projects.thermostat.LoopReceiveRequest
set_option autoImplicit false
set_option maxRecDepth 5000
namespace E5R.Thermostat.ChunkRejectCycle
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec
abbrev B := UartPlatform.board
abbrev sp := 0x80ffeb90#32

def reads (headerPlan : MainHeaderStreamPlan.Plan) (bodyPlan : ChunkReceivePlan.Plan) (slots : List UartTxLoop.Slot)
    (wire : Nat → BitVec 8) (fuel received : Nat) :=
  MainHeaderStreamPlan.logs headerPlan 0 (consume wire fuel []).received++
    ChunkReceivePlan.logs bodyPlan (consume wire fuel []).input.length received++UartTxLoop.reads slots

theorem body_input (plan : ChunkReceivePlan.Plan) (wire : Nat → BitVec 8) (first count available : Nat)
    (valid : ChunkReceivePlan.Valid plan wire first available) (bound : count≤available) :
    Observed.input (ChunkReceivePlan.logs plan first count)=MainHeaderStreamSpec.arrivals wire first count := by
  rw [ChunkReceivePlan.logs_input]
  apply List.map_congr_left
  intro i hi
  have index := List.mem_range.mp hi
  exact (valid (first+i) (by omega) (by omega)).2.2

/-- Every logical stream whose independent head parser selects Chunked and
    whose independent decoder rejects within the supplied raw-buffer bound
    takes the actual receive/parser/body/error/send/restart path. Only pure
    classification and finite UART delivery/readiness describe the environment. -/
theorem contract {c : Core} {ram : Word → BitVec 8} {s : Spec.Snapshot} {served : Nat}
    (h : LoopReady.At c ram s served) (wire : Nat → BitVec 8) (fuel arrivals status : Nat) (head : Head)
    (headerPlan : MainHeaderStreamPlan.Plan) (bodyPlan : ChunkReceivePlan.Plan)
    (headSpace : fuel≤2048) (headerValid : MainHeaderStreamPlan.Valid headerPlan wire 0 fuel)
    (accepted : (consume wire fuel []).result=.done head) (kind : head.framing=.chunked)
    (space : (consume wire fuel []).input.length+arrivals≤2048)
    (bodyValid : ChunkReceivePlan.Valid bodyPlan wire (consume wire fuel []).input.length arrivals)
    (reject : (ChunkBufferSpec.consume wire ((consume wire fuel []).input.length-head.len+arrivals) head.len head.len cStart []).stop=.reject status)
    (slots : List UartTxLoop.Slot) (length : slots.length=(ResponseHeadSpec.bytes status [] 0 true).length) :
    ∃ received d n after, received≤arrivals ∧
      ((consume wire fuel []).input.length≤head.len+1 → received=
        (ChunkBufferSpec.consume wire ((consume wire fuel []).input.length-head.len+arrivals) head.len head.len cStart []).read-(consume wire fuel []).input.length) ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (reads headerPlan bodyPlan slots wire fuel received)
        (UartTxLoop.events (ResponseHeadSpec.bytes status [] 0 true)) ∧
      Observed.input (reads headerPlan bodyPlan slots wire fuel received)=
        MainHeaderStreamSpec.arrivals wire 0 (consume wire fuel []).received++MainHeaderStreamSpec.arrivals wire (consume wire fuel []).input.length received ∧
      LoopReady.At d after s 0 ∧ AppState.At after s ∧ ramRead after 0x80ffebbc#32 .w=0#32 := by
  obtain ⟨hn,a,ra,_,header,boundary,_,bankA,serveA,lowA⟩ := MainHeaderStreamRegs.contract_routes wire headerPlan fuel
    h.receive (by simpa only [List.length_nil,Nat.zero_add] using headSpace) headerValid
  rw [accepted] at boundary
  have parsed : HttpRequestBytes.parse (consume wire fuel []).input 1024 1024=.done head := by
    rw [←MainHeaderStreamSpec.exact_result wire fuel [] (by decide +kernel)]
    exact accepted
  obtain ⟨bn,b,_,_,copy,bodyReady,_,bankB,serveB⟩ := MainHeaderToBodyRegs.contract boundary parsed
  let rb := MainBodyHeadMemory.memory ra sp head
  have lowFrame : ViewFrame.Region ram rb sp 132 := HeadRegionFrame.trans lowA
    (MainBodyHeadMemory.frame ra sp head 0 132 (by decide) (Or.inl (by decide)) (Or.inl (by decide)))
  have static : InitRoutes.Layout rb := by
    apply InitRoutes.layout_preserve ram rb ⟨h.routes,h.capacity⟩
    · simpa only [ViewFrame.Region,show sp+72#32=0x80ffebd8#32 by decide +kernel] using HeadRegionFrame.sub lowFrame 72 60 (by decide)
    · simpa only [ViewFrame.Region,show sp+16#32=0x80ffeba0#32 by decide +kernel] using HeadRegionFrame.sub lowFrame 16 4 (by decide)
  have inputWire : ∀ k (hk : k<(consume wire fuel []).input.length), head.len≤k →
      (consume wire fuel []).input[k]'hk=wire k := by
    intro k hk _
    have bytes := MainHeaderStreamSpec.input_bytes wire fuel []
    simp only [List.length_nil,List.nil_append] at bytes
    simp only [bytes,MainHeaderStreamSpec.arrivals,List.getElem_map,List.getElem_range,Nat.zero_add]
  obtain ⟨received,d,n,after,receivedBound,_,exactReceived,_,response,ready⟩ := ChunkRejectBody.contract bodyReady kind served
    (MainGprBank.preserve (MainGprBank.trans bankA bankB) h.bank)
    (MainServeLayout.preserve (MainServeLayout.trans serveA serveB) h.serve) static.2 static.1 wire arrivals status bodyPlan space bodyValid inputWire reject slots length
  refine ⟨received,d,hn+bn+n,after,receivedBound,exactReceived,?_,?_,ready,ready.receive.stable.app,ready.receive.stable.app.available⟩
  · simpa only [reads,List.length_nil,List.nil_append,List.append_nil,List.append_assoc] using (header.trans copy.observed).trans response
  · rw [reads,Observed.input_append,Observed.input_append,MainHeaderStreamPlan.logs_wire headerPlan wire 0 _ fuel headerValid (received_le wire fuel []),
      body_input bodyPlan wire _ received arrivals bodyValid receivedBound,UartTxLoop.no_input,List.append_nil]
end E5R.Thermostat.ChunkRejectCycle
