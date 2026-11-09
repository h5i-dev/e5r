import Projects.thermostat.RuntimeLiteralWriteInput
import Projects.thermostat.StackBoard
import Projects.thermostat.StackRuntimeApiWriteCaller
import Projects.thermostat.StackRuntimeFourthMatch
import Projects.thermostat.StackRuntimeModeWriteInput
import Projects.thermostat.StackRuntimeSecondMatch
import Projects.thermostat.StackRuntimeSetpointWriteInput
import Projects.thermostat.StackRuntimeTempWriteInput
import Projects.thermostat.StackRuntimeThirdMatch
set_option autoImplicit false
set_option maxRecDepth 6000
namespace E5R.Thermostat.StackRuntimeLiteralWriteInput
open E5R E5R.Thermostat HttpRequestSpec RuntimeLiteralWriteInput
abbrev B := StackBoard.board
theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head}
    {amount rawUsed served : Nat} {lowValue : Word} {close : Bool} {used : Word}
    (kind : RouteLiteralInfo.Kind) (write : kind≠.state)
    (h : RuntimeRouteEnvelope.At c ram input s head amount rawUsed served lowValue close)
    (pc : c.pc=0x800013d2#32)
    (result : c.get 10=(if RuntimeRequestSpans.path input head=WireSpec.ascii "/state" then 1#32 else 0#32))
    (route : RuntimeRequestSpans.path input head=RouteLiteralInfo.text kind)
    (method : RouteSpec.allows (RouteLiteralInfo.route kind) (MainMethodSpec.decode (MainMethodBytes.token input head.method.2))=true)
    (leading : ∃ ys,RuntimeRequestSpans.path input head=47#8::ys) (metadata : LoopTransactionMemory.At ram used) :
    ∃ n d after,Quiet.Steps StackBoard.board img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      StackRuntimeApiWriteCaller.Ready (handler kind) (future kind) (RouteLiteralInfo.text kind) none d after input s head amount rawUsed served close ∧
      LoopTransactionMemory.At after used ∧ d.get 19=0x10000000#32 ∧ d.get 23=0x80fff9f0#32 ∧ d.get 26=3#32 ∧ d.mie_=false := by
  have notState : RuntimeRequestSpans.path input head≠WireSpec.ascii "/state" := by
    rw [route]
    cases kind with
    | state => exact False.elim (write rfl)
    | setpoint | temp | mode => decide +kernel
  obtain ⟨na,a,ra,ba,ta,pa,a10,a11,a9,liveA,metaA,ca⟩ := StackRuntimeSecondMatch.contract h pc result (Or.inl notState) leading metadata
  cases kind with
  | state => exact False.elim (write rfl)
  | setpoint =>
    have matched : a.get 10=1#32 := by
      have path : RuntimeRequestSpans.path input head=WireSpec.ascii "/setpoint" := route
      simpa only [path,ite_true] using a10
    have put : MainMethodSpec.decode (MainMethodBytes.token input head.method.2)=.put := by
      cases token : MainMethodSpec.decode (MainMethodBytes.token input head.method.2) <;> simp_all [RouteSpec.allows,RouteLiteralInfo.route]
    obtain ⟨d,td,ready,cd,frame,d23,d26,d19⟩ := StackRuntimeSetpointWriteInput.contract liveA pa matched a11 route put
    exact ⟨na+28,d,_,ta.trans td,ready,LoopTransactionMemory.caller metaA frame,d19.trans liveA.stable.uart,
      d23.trans liveA.future,d26.trans liveA.three,(congrArg Prod.fst cd).trans liveA.stable.masked⟩
  | temp =>
    have noSetpoint : RuntimeRequestSpans.path input head≠WireSpec.ascii "/setpoint" := by rw [route];decide +kernel
    obtain ⟨nb,b,rb,bb,tb,pb,b10,b11,b9,liveB,metaB,cb⟩ := StackRuntimeThirdMatch.contract liveA pa a10 (Or.inl noSetpoint) leading metaA
    have matched : b.get 10=1#32 := by
      have path : RuntimeRequestSpans.path input head=WireSpec.ascii "/temp" := route
      simpa only [path,ite_true] using b10
    have post : MainMethodSpec.decode (MainMethodBytes.token input head.method.2)=.post := by
      cases token : MainMethodSpec.decode (MainMethodBytes.token input head.method.2) <;> simp_all [RouteSpec.allows,RouteLiteralInfo.route]
    obtain ⟨d,td,ready,cd,frame,d23,d26,d19⟩ := StackRuntimeTempWriteInput.contract liveB pb matched b11 route post
    exact ⟨na+nb+28,d,_,(ta.trans tb).trans td,ready,LoopTransactionMemory.caller metaB frame,d19.trans liveB.stable.uart,
      d23.trans liveB.future,d26.trans liveB.three,(congrArg Prod.fst cd).trans liveB.stable.masked⟩
  | mode =>
    have noSetpoint : RuntimeRequestSpans.path input head≠WireSpec.ascii "/setpoint" := by rw [route];decide +kernel
    obtain ⟨nb,b,rb,bb,tb,pb,b10,b11,b9,liveB,metaB,cb⟩ := StackRuntimeThirdMatch.contract liveA pa a10 (Or.inl noSetpoint) leading metaA
    have noTemp : RuntimeRequestSpans.path input head≠WireSpec.ascii "/temp" := by rw [route];decide +kernel
    obtain ⟨ne,e,re,be,te,pe,e10,e11,e9,liveE,metaE,ce⟩ := StackRuntimeFourthMatch.contract liveB pb b10 (Or.inl noTemp) leading metaB
    have matched : e.get 10=1#32 := by
      have path : RuntimeRequestSpans.path input head=WireSpec.ascii "/mode" := route
      simpa only [path,ite_true] using e10
    have put : MainMethodSpec.decode (MainMethodBytes.token input head.method.2)=.put := by
      cases token : MainMethodSpec.decode (MainMethodBytes.token input head.method.2) <;> simp_all [RouteSpec.allows,RouteLiteralInfo.route]
    have pointer : e.get 25=0x80fffa58#32 := liveE.secondSlot
    obtain ⟨d,td,ready,cd,frame,d23,d26,d19⟩ := StackRuntimeModeWriteInput.contract liveE pe matched e11 route put pointer
    exact ⟨na+nb+ne+27,d,_,((ta.trans tb).trans te).trans td,ready,LoopTransactionMemory.caller metaE frame,d19.trans liveE.stable.uart,
      d23.trans liveE.future,d26.trans liveE.three,(congrArg Prod.fst cd).trans liveE.stable.masked⟩
end E5R.Thermostat.StackRuntimeLiteralWriteInput
