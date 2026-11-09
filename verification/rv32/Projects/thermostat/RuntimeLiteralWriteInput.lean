import Projects.thermostat.RouteSpec
import Projects.thermostat.RuntimeSecondMatch
import Projects.thermostat.RuntimeThirdMatch
import Projects.thermostat.RuntimeFourthMatch
import Projects.thermostat.RuntimeSetpointWriteInput
import Projects.thermostat.RuntimeTempWriteInput
import Projects.thermostat.RuntimeModeWriteInput
set_option autoImplicit false
namespace E5R.Thermostat.RuntimeLiteralWriteInput
open E5R E5R.Thermostat HttpRequestSpec

def handler : RouteLiteralInfo.Kind → Fin 4
  | .state | .setpoint => 0 | .temp => 1 | .mode => 2

def future : RouteLiteralInfo.Kind → Word
  | .state | .setpoint => 0x80fffab0#32 | .temp => 0x80fffa84#32 | .mode => 0x80fffa58#32

/-- Actual route search and handler setup for each literal write route. The
    caller's full auth/body/header precondition derives from received RAM. -/
theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head}
    {amount rawUsed served : Nat} {lowValue : Word} {close : Bool} {used : Word}
    (kind : RouteLiteralInfo.Kind) (write : kind≠.state)
    (h : RuntimeRouteEnvelope.At c ram input s head amount rawUsed served lowValue close)
    (pc : c.pc=0x800013d2#32)
    (result : c.get 10=(if RuntimeRequestSpans.path input head=WireSpec.ascii "/state" then 1#32 else 0#32))
    (route : RuntimeRequestSpans.path input head=RouteLiteralInfo.text kind)
    (method : RouteSpec.allows (RouteLiteralInfo.route kind) (MainMethodSpec.decode (MainMethodBytes.token input head.method.2))=true)
    (leading : ∃ ys,RuntimeRequestSpans.path input head=47#8::ys) (metadata : LoopTransactionMemory.At ram used) :
    ∃ n d after,Quiet.Steps UartPlatform.board img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      RuntimeApiWriteCaller.Ready (handler kind) (future kind) (RouteLiteralInfo.text kind) none d after input s head amount rawUsed served close ∧
      LoopTransactionMemory.At after used ∧ d.get 19=0x10000000#32 ∧ d.get 23=0x80fff9f0#32 ∧ d.get 26=3#32 ∧ d.mie_=false := by
  have notState : RuntimeRequestSpans.path input head≠WireSpec.ascii "/state" := by
    rw [route]
    cases kind with
    | state => exact False.elim (write rfl)
    | setpoint | temp | mode => decide +kernel
  obtain ⟨na,a,ra,ba,ta,pa,a10,a11,a9,liveA,metaA,ca⟩ := RuntimeSecondMatch.contract h pc result (Or.inl notState) leading metadata
  cases kind with
  | state => exact False.elim (write rfl)
  | setpoint =>
    have matched : a.get 10=1#32 := by
      have path : RuntimeRequestSpans.path input head=WireSpec.ascii "/setpoint" := route
      simpa only [path,ite_true] using a10
    have put : MainMethodSpec.decode (MainMethodBytes.token input head.method.2)=.put := by
      cases token : MainMethodSpec.decode (MainMethodBytes.token input head.method.2) <;> simp_all [RouteSpec.allows,RouteLiteralInfo.route]
    obtain ⟨d,td,ready,cd,frame,d23,d26,d19⟩ := RuntimeSetpointWriteInput.contract liveA pa matched a11 route put
    exact ⟨na+28,d,_,ta.trans td,ready,LoopTransactionMemory.caller metaA frame,d19.trans liveA.stable.uart,
      d23.trans liveA.future,d26.trans liveA.three,(congrArg Prod.fst cd).trans liveA.stable.masked⟩
  | temp =>
    have noSetpoint : RuntimeRequestSpans.path input head≠WireSpec.ascii "/setpoint" := by rw [route];decide +kernel
    obtain ⟨nb,b,rb,bb,tb,pb,b10,b11,b9,liveB,metaB,cb⟩ := RuntimeThirdMatch.contract liveA pa a10 (Or.inl noSetpoint) leading metaA
    have matched : b.get 10=1#32 := by
      have path : RuntimeRequestSpans.path input head=WireSpec.ascii "/temp" := route
      simpa only [path,ite_true] using b10
    have post : MainMethodSpec.decode (MainMethodBytes.token input head.method.2)=.post := by
      cases token : MainMethodSpec.decode (MainMethodBytes.token input head.method.2) <;> simp_all [RouteSpec.allows,RouteLiteralInfo.route]
    obtain ⟨d,td,ready,cd,frame,d23,d26,d19⟩ := RuntimeTempWriteInput.contract liveB pb matched b11 route post
    exact ⟨na+nb+28,d,_,(ta.trans tb).trans td,ready,LoopTransactionMemory.caller metaB frame,d19.trans liveB.stable.uart,
      d23.trans liveB.future,d26.trans liveB.three,(congrArg Prod.fst cd).trans liveB.stable.masked⟩
  | mode =>
    have noSetpoint : RuntimeRequestSpans.path input head≠WireSpec.ascii "/setpoint" := by rw [route];decide +kernel
    obtain ⟨nb,b,rb,bb,tb,pb,b10,b11,b9,liveB,metaB,cb⟩ := RuntimeThirdMatch.contract liveA pa a10 (Or.inl noSetpoint) leading metaA
    have noTemp : RuntimeRequestSpans.path input head≠WireSpec.ascii "/temp" := by rw [route];decide +kernel
    obtain ⟨ne,e,re,be,te,pe,e10,e11,e9,liveE,metaE,ce⟩ := RuntimeFourthMatch.contract liveB pb b10 (Or.inl noTemp) leading metaB
    have matched : e.get 10=1#32 := by
      have path : RuntimeRequestSpans.path input head=WireSpec.ascii "/mode" := route
      simpa only [path,ite_true] using e10
    have put : MainMethodSpec.decode (MainMethodBytes.token input head.method.2)=.put := by
      cases token : MainMethodSpec.decode (MainMethodBytes.token input head.method.2) <;> simp_all [RouteSpec.allows,RouteLiteralInfo.route]
    have pointer : e.get 25=0x80fffa58#32 := liveE.secondSlot
    obtain ⟨d,td,ready,cd,frame,d23,d26,d19⟩ := RuntimeModeWriteInput.contract liveE pe matched e11 route put pointer
    exact ⟨na+nb+ne+27,d,_,((ta.trans tb).trans te).trans td,ready,LoopTransactionMemory.caller metaE frame,d19.trans liveE.stable.uart,
      d23.trans liveE.future,d26.trans liveE.three,(congrArg Prod.fst cd).trans liveE.stable.masked⟩
end E5R.Thermostat.RuntimeLiteralWriteInput
