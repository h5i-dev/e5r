import Projects.thermostat.EmptyPhase
import Projects.thermostat.StackEnvelope
import Projects.thermostat.StackEmptyNextReady
import Projects.thermostat.StackHeaderToBodyRegs
import Projects.thermostat.StackRequestPhase
import Projects.thermostat.StackRuntimeRequestBuild
set_option autoImplicit false
namespace E5R.Thermostat.StackEmptyPhase
open E5R E5R.Thermostat HttpRequestSpec EmptyPhase
abbrev B := StackBoard.board
abbrev Envelope (I : Machine → ProtocolStreamSpec.State → Prop) (m : Machine) (g : ProtocolStreamSpec.State) := StackEnvelope.Envelope (fun cut => I cut g) m
theorem from_header {c ram s served original head}
    (boundary : MainHeaderLoopTwo.Boundary c ram original s (.done head))
    (parsed : HttpRequestBytes.parse original 1024 1024=.done head)
    (earlier : ∀ k,k<original.length → HttpRequestBytes.parse (original.take k) 1024 1024=.incomplete)
    (caller : HeaderPhase.Caller c ram served) (kind : head.framing=.empty) :
    Envelope (fun m g => RequestPhase.At m.core m.ram g) ⟨c,ram⟩ (HeaderPhase.classify s served original) := by
  have exactHead := (HeaderPhase.accepted_extent original head earlier parsed).symm
  obtain ⟨hn,a,lo,hi,copy,bodyReady,csrA,bankA,serveA⟩ := StackHeaderToBodyRegs.contract boundary parsed
  let ra := MainBodyHeadMemory.memory ram sp head
  have copyLow := MainBodyHeadMemory.frame ram sp head 0 132 (by decide) (Or.inl (by decide)) (Or.inl (by decide))
  have liveCaller := HeaderPhase.preserve_caller caller bankA serveA (by simpa only [BitVec.add_zero] using copyLow)
  have originalFrame : ViewFrame.Region ram ra 0x80fffd38#32 304 := by
    simpa only [show sp+4520#32=0x80fffd38#32 by decide +kernel] using MainBodyHeadMemory.frame ram sp head 4520 304
      (by decide) (Or.inr (by decide)) (Or.inr (by decide))
  have originalView : HeadCompletedView.At ra 0x80fffd38#32 head := MainCopyView.head originalFrame head boundary.2.2.1
  have headBounds := bodyReady.bounds
  have headLimit : head.len≤1024 := Nat.le_trans headBounds.length.2 (Nat.min_le_right _ _)
  rw [exactHead,Nat.min_eq_left headLimit] at headBounds
  have bounds : MainHeadAcceptedBounds.At 1024 1024 head := MainLengthState.widen headBounds headLimit
  obtain ⟨e,next,entry,csrE,routeFrame,capacityFrame,nextFuture⟩ := StackEmptyNextReady.contract bodyReady originalView exactHead
    liveCaller.bank liveCaller.serve kind liveCaller.room bounds ⟨headBounds.target.2.2,headBounds.fields⟩
  obtain ⟨rn,d,after,bound,request,ready,csrD,requestFrame,requestFuture⟩ := StackRuntimeRequestBuild.contract entry
  have staticNext := InitRoutes.layout_preserve ra (EmptyNextReady.memory ra head) liveCaller.layout
    (by simpa only [ViewFrame.Region,show sp+72#32=0x80ffebd8#32 by decide +kernel] using routeFrame)
    (by simpa only [ViewFrame.Region,show sp+16#32=0x80ffeba0#32 by decide +kernel] using capacityFrame)
  have staticFinal : InitRoutes.Layout after := InitRoutes.layout_preserve _ after staticNext
    (by simpa only [ViewFrame.Region,show sp+72#32=0x80ffebd8#32 by decide +kernel] using HeadRegionFrame.sub requestFrame 72 60 (by decide))
    (by simpa only [ViewFrame.Region,show sp+16#32=0x80ffeba0#32 by decide +kernel] using HeadRegionFrame.sub requestFrame 16 4 (by decide))
  have limitsFrame := HeadRegionFrame.trans nextFuture requestFuture
  have metadata : LoopTransactionMemory.At after (BitVec.ofNat 32 head.len) := by
    refine ⟨(ViewFrame.word limitsFrame 76 (by decide)).trans bodyReady.stable.layout.head.headLimit,
      (ViewFrame.word limitsFrame 80 (by decide)).trans bodyReady.stable.layout.head.bodyLimit,?_,ready.usedWord,?_,staticFinal.2,staticFinal.1⟩
    · simpa only [exactHead] using ready.stable.filled
    · rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := ready.stable.bound;rw [exactHead] at this;omega)]
      have bound := ready.stable.bound
      rw [exactHead] at bound
      exact bound
  have header : original.take head.len=original := by rw [←exactHead,List.take_length]
  have payload : RuntimeRequestSpans.body original head 0=[] := by simp only [RuntimeRequestSpans.body,List.take_zero]
  obtain ⟨nr,last,final,route,post⟩ := StackRequestPhase.enter ready metadata header payload parsed
  refine ⟨boundary.2.1.masked,hn+409+rn+nr,⟨last,final⟩,((copy.trans next).trans request).trans route,?_⟩
  have same : HeaderPhase.classify s served original=ProtocolStreamSpec.dispatch ⟨s,served,.head original⟩ original [] head := by
    unfold HeaderPhase.classify
    rw [parsed]
    dsimp only
    rw [kind]
  rw [same]
  exact post
end E5R.Thermostat.StackEmptyPhase
