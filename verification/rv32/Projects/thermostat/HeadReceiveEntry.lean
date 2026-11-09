import Projects.thermostat.HeadConsumedExtent
import Projects.thermostat.LoopReceiveRequest
set_option autoImplicit false
set_option maxRecDepth 4000
namespace E5R.Thermostat.HeadReceiveEntry
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec
abbrev B := UartPlatform.board
abbrev sp := 0x80ffeb90#32

/-- Any pure successful head, including Empty/Chunked, reaches its real body
    dispatch with both actual Head copies, exact extent, caller bank and static
    routing/capacity words. No framing-specific body result is assumed. -/
theorem contract {c : Core} {ram : Word → BitVec 8} {s : Spec.Snapshot} {served : Nat}
    (h : LoopReady.At c ram s served) (wire : Nat → BitVec 8) (fuel : Nat) (head : Head)
    (plan : MainHeaderStreamPlan.Plan) (space : fuel≤2048)
    (valid : MainHeaderStreamPlan.Valid plan wire 0 fuel)
    (accepted : (consume wire fuel []).result=.done head) :
    ∃ n d after, Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (MainHeaderStreamPlan.logs plan 0 (consume wire fuel []).received) [] ∧
      MainHeaderToBody.Ready d after (consume wire fuel []).input s head ∧
      (consume wire fuel []).input.length=head.len ∧ MainGprBank.At d ∧ MainServeLayout.At after served ∧
      InitRoutes.Layout after ∧ HeadCompletedView.At after 0x80fffd38#32 head ∧
      MainHeadAcceptedBounds.At head.len 1024 head ∧ d.sameCsr c := by
  obtain ⟨hn,a,ra,_,header,boundary,csrA,bankA,serveA,lowA⟩ := MainHeaderStreamRegs.contract_routes wire plan fuel
    h.receive (by simpa only [List.length_nil,Nat.zero_add] using space) valid
  rw [accepted] at boundary
  have parsed : HttpRequestBytes.parse (consume wire fuel []).input 1024 1024=.done head := by
    rw [←MainHeaderStreamSpec.exact_result wire fuel [] (by decide +kernel)]
    exact accepted
  obtain ⟨bn,b,_,_,copy,bodyReady,csrB,bankB,serveB⟩ := MainHeaderToBodyRegs.contract boundary parsed
  let rb := MainBodyHeadMemory.memory ra sp head
  have lowFrame : ViewFrame.Region ram rb sp 132 := HeadRegionFrame.trans lowA
    (MainBodyHeadMemory.frame ra sp head 0 132 (by decide) (Or.inl (by decide)) (Or.inl (by decide)))
  have static : InitRoutes.Layout rb := by
    apply InitRoutes.layout_preserve ram rb ⟨h.routes,h.capacity⟩
    · simpa only [ViewFrame.Region,show sp+72#32=0x80ffebd8#32 by decide +kernel] using HeadRegionFrame.sub lowFrame 72 60 (by decide)
    · simpa only [ViewFrame.Region,show sp+16#32=0x80ffeba0#32 by decide +kernel] using HeadRegionFrame.sub lowFrame 16 4 (by decide)
  have original : HeadCompletedView.At ra 0x80fffd38#32 head := boundary.2.2.1
  have originalFrame : ViewFrame.Region ra rb 0x80fffd38#32 304 := by
    simpa only [sp,show 0x80ffeb90#32+4520#32=0x80fffd38#32 by decide +kernel] using
      MainBodyHeadMemory.frame ra sp head 4520 304 (by decide) (Or.inr (by decide)) (Or.inr (by decide))
  have originalAfter := MainCopyView.head originalFrame head original
  have exactLength := HeadConsumedExtent.receive_exact wire fuel head accepted
  have bounds := bodyReady.bounds
  have headLimit : head.len≤1024 := by have := bounds.length.2;have := Nat.min_le_right (consume wire fuel []).input.length 1024;omega
  rw [exactLength,Nat.min_eq_left headLimit] at bounds
  exact ⟨hn+bn,b,rb,by simpa only [List.length_nil,List.append_nil] using header.trans copy.observed,bodyReady,exactLength,
    MainGprBank.preserve (MainGprBank.trans bankA bankB) h.bank,MainServeLayout.preserve (MainServeLayout.trans serveA serveB) h.serve,
    static,originalAfter,bounds,csrB.trans csrA⟩
end E5R.Thermostat.HeadReceiveEntry
