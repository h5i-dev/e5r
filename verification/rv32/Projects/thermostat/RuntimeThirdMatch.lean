import Projects.thermostat.RuntimeThirdCandidate
import Projects.thermostat.RuntimeLiteralMatch
import Projects.thermostat.LoopTransactionMemory
set_option autoImplicit false
namespace E5R.Thermostat.RuntimeThirdMatch
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board
abbrev sp := RuntimeRouteEnvelope.sp
abbrev rx := RuntimeRouteEnvelope.rx

/-- Actual first rejection through second candidate comparison. The precise
    state/setpoint byte predicates determine both comparisons and404/405 flag. -/
theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head}
    {amount rawUsed served : Nat} {lowValue : Word} {close : Bool} {used : Word}
    (h : RuntimeRouteEnvelope.At c ram input s head amount rawUsed served lowValue close)
    (pc : c.pc=0x80001422#32)
    (result : c.get 10=(if RuntimeRequestSpans.path input head=WireSpec.ascii "/setpoint" then 1#32 else 0#32))
    (eligible : RuntimeRequestSpans.path input head≠WireSpec.ascii "/setpoint" ∨
      MainMethodSpec.decode (MainMethodBytes.token input head.method.2)≠.put)
    (leading : ∃ ys,RuntimeRequestSpans.path input head=47#8::ys)
    (metadata : LoopTransactionMemory.At ram used) :
    ∃ n d after, n≤10*(RuntimeRequestSpans.path input head).length+224 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      d.pc=0x8000146c#32 ∧ d.get 10=(if RuntimeRequestSpans.path input head=WireSpec.ascii "/temp" then 1#32 else 0#32) ∧
      d.get 11=0#32 ∧ d.get 9=(if RuntimeRequestSpans.path input head=WireSpec.ascii "/setpoint" then 2#32 else c.get 9) ∧
      RuntimeRouteEnvelope.At d after input s head amount rawUsed served lowValue close ∧ LoopTransactionMemory.At after used ∧ d.sameCsr c := by
  obtain ⟨na,a,ba,ta,entry,a9,ac,frameA⟩ := RuntimeThirdCandidate.advance h pc result eligible
  obtain ⟨nb,d,bb,tb,pd,d10,d11,abi,dc,frameB,live⟩ := RuntimeLiteralMatch.contract .temp 0x8000146c#32 entry (by decide) (by decide) leading
  have frame : ViewFrame.Region ram (MainPathStateSave.memory (RouteThirdCore.memory ram (rx+BitVec.ofNat 32 head.target.1)) a) sp 3304 := by
    have short := HeadRegionFrame.sub frameB 0 3304 (by decide)
    simp only [BitVec.add_zero] at short
    exact HeadRegionFrame.trans frameA short
  refine ⟨na+nb,d,_,by omega,ta.trans tb,pd,d10,d11,(abi 9 (by decide)).trans a9,live,LoopTransactionMemory.caller metadata frame,dc.trans ac⟩
end E5R.Thermostat.RuntimeThirdMatch
