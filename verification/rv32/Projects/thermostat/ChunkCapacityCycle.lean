import Projects.thermostat.ChunkCapacityBody
import Projects.thermostat.ChunkRejectCycle
set_option autoImplicit false
set_option maxRecDepth 5000
namespace E5R.Thermostat.ChunkCapacityCycle
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec ChunkRejectCycle
abbrev B := UartPlatform.board
abbrev sp := 0x80ffeb90#32

/-- Real receive boundary through accepted chunked head, arbitrary valid but
    incomplete raw input filling RX2048, actual413 response and nextRX/count0.
    All body caller preconditions are discharged from upstream execution. -/
theorem contract {c : Core} {ram : Word → BitVec 8} {s : Spec.Snapshot} {served : Nat}
    (h : LoopReady.At c ram s served) (wire : Nat → BitVec 8) (fuel arrivals : Nat) (head : Head)
    (headerPlan : MainHeaderStreamPlan.Plan) (bodyPlan : ChunkReceivePlan.Plan)
    (headSpace : fuel≤2048) (headerValid : MainHeaderStreamPlan.Valid headerPlan wire 0 fuel)
    (accepted : (consume wire fuel []).result=.done head) (kind : head.framing=.chunked)
    (full : (consume wire fuel []).input.length+arrivals=2048)
    (bodyValid : ChunkReceivePlan.Valid bodyPlan wire (consume wire fuel []).input.length arrivals)
    (incomplete : (ChunkBufferSpec.consume wire ((consume wire fuel []).input.length-head.len+arrivals) head.len head.len cStart []).stop=.needInput)
    (slots : List UartTxLoop.Slot) (length : slots.length=(ResponseHeadSpec.bytes 413 [] 0 true).length) :
    ∃ d n after,
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (reads headerPlan bodyPlan slots wire fuel arrivals)
        (UartTxLoop.events (ResponseHeadSpec.bytes 413 [] 0 true)) ∧
      Observed.input (reads headerPlan bodyPlan slots wire fuel arrivals)=
        MainHeaderStreamSpec.arrivals wire 0 (consume wire fuel []).received++MainHeaderStreamSpec.arrivals wire (consume wire fuel []).input.length arrivals ∧
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
  obtain ⟨d,n,after,_,response,ready⟩ := ChunkCapacityBody.contract bodyReady kind served
    (MainGprBank.preserve (MainGprBank.trans bankA bankB) h.bank)
    (MainServeLayout.preserve (MainServeLayout.trans serveA serveB) h.serve) static.2 static.1 wire arrivals bodyPlan full bodyValid inputWire incomplete slots length
  refine ⟨d,hn+bn+n,after,?_,?_,ready,ready.receive.stable.app,ready.receive.stable.app.available⟩
  · simpa only [reads,List.length_nil,List.nil_append,List.append_nil,List.append_assoc] using (header.trans copy.observed).trans response
  · rw [reads,Observed.input_append,Observed.input_append,MainHeaderStreamPlan.logs_wire headerPlan wire 0 _ fuel headerValid (received_le wire fuel []),
      body_input bodyPlan wire _ arrivals arrivals bodyValid (Nat.le_refl _),UartTxLoop.no_input,List.append_nil]
end E5R.Thermostat.ChunkCapacityCycle
