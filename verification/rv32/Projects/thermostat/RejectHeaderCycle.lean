import Projects.thermostat.RejectStatus
import Projects.thermostat.RejectTransaction
import Projects.thermostat.MainRouterBankHeaderFrames
set_option autoImplicit false
namespace E5R.Thermostat.RejectHeaderCycle
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

/-- Arbitrary malformed request-head stream: actual receive/parser rejection,
    exact status-only close response and reusable next-request boundary.
    Parser acceptance, result layout and response fields are not premises. -/
theorem contract {c : Core} {ram : Word → BitVec 8} {s : Spec.Snapshot} {served : Nat}
    (h : LoopReady.At c ram s served) (wire : Nat → BitVec 8) (fuel status : Nat)
    (plan : MainHeaderStreamPlan.Plan) (space : fuel≤2048)
    (valid : MainHeaderStreamPlan.Valid plan wire 0 fuel)
    (reject : (MainHeaderStreamSpec.consume wire fuel []).result=.reject status)
    (slots : List UartTxLoop.Slot) (length : slots.length=(ResponseHeadSpec.bytes status [] 0 true).length) :
    ∃ d n after, n≤MainHeaderStreamPlan.cost plan 0 fuel+3318+UartWriteAll.time (ResponseHeadSpec.bytes status [] 0 true) slots ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩
        (MainHeaderStreamPlan.logs plan 0 (MainHeaderStreamSpec.consume wire fuel []).received++UartTxLoop.reads slots)
        (UartTxLoop.events (ResponseHeadSpec.bytes status [] 0 true)) ∧ LoopReady.At d after s 0 := by
  obtain ⟨first,a,mid,firstBound,receive,boundary,_,bankFrame,serveFrame,low⟩ := MainHeaderStreamRegs.contract_routes wire plan fuel
    h.receive (by simpa only [List.length_nil,Nat.zero_add] using space) (by simpa only [List.length_nil] using valid)
  simp only [List.length_nil] at firstBound
  rw [reject] at boundary
  obtain ⟨cut,stable,_⟩ := boundary
  have parse : HttpRequestBytes.parse (MainHeaderStreamSpec.consume wire fuel []).input 1024 1024=.reject status := by
    rw [←MainHeaderStreamSpec.exact_result wire fuel [] (by decide +kernel)]
    exact reject
  obtain ⟨lo,hi⟩ := RejectStatus.bounds (RejectStatus.parse _ 1024 1024 status parse)
  have cap : ramRead mid 0x80ffeba0#32 .w=2048#32 := by
    have word := ViewFrame.word low 16 (by decide)
    have eq : ramRead mid 0x80ffeba0#32 .w=ramRead ram 0x80ffeba0#32 .w := by
      simpa only [show 0x80ffeb90#32+16#32=0x80ffeba0#32 by decide +kernel] using word
    exact eq.trans h.capacity
  have routes : MainRouterTable.At mid := by
    apply MainRouterTable.preserve h.routes
    have sub := HeadRegionFrame.sub low 72 60 (by decide)
    simpa only [show 0x80ffeb90#32+72#32=0x80ffebd8#32 by decide +kernel] using sub
  obtain ⟨d,rest,after,restBound,response,ready⟩ := RejectTransaction.contract a mid s served status _ cut stable
    (MainGprBank.preserve bankFrame h.bank) (MainServeLayout.preserve serveFrame h.serve) cap routes lo hi slots length
  exact ⟨d,first+rest,after,by omega,by simpa only [List.length_nil,List.nil_append] using receive.trans response,ready⟩
end E5R.Thermostat.RejectHeaderCycle
