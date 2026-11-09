import Projects.thermostat.RuntimeSecondMatch
import Projects.thermostat.StackBoard
import Projects.thermostat.StackRuntimeApiWriteCaller
import Projects.thermostat.StackRuntimeLiteralMatch
import Projects.thermostat.StackRuntimeSecondCandidate
set_option autoImplicit false
set_option maxRecDepth 6000
namespace E5R.Thermostat.StackRuntimeSecondMatch
open E5R E5R.Thermostat HttpRequestSpec RuntimeSecondMatch
abbrev B := StackBoard.board
theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head}
    {amount rawUsed served : Nat} {lowValue : Word} {close : Bool} {used : Word}
    (h : RuntimeRouteEnvelope.At c ram input s head amount rawUsed served lowValue close)
    (pc : c.pc=0x800013d2#32)
    (result : c.get 10=(if RuntimeRequestSpans.path input head=WireSpec.ascii "/state" then 1#32 else 0#32))
    (eligible : RuntimeRequestSpans.path input head≠WireSpec.ascii "/state" ∨
      (MainMethodSpec.decode (MainMethodBytes.token input head.method.2)≠.get ∧ MainMethodSpec.decode (MainMethodBytes.token input head.method.2)≠.head))
    (leading : ∃ ys,RuntimeRequestSpans.path input head=47#8::ys)
    (metadata : LoopTransactionMemory.At ram used) :
    ∃ n d after, n≤10*(RuntimeRequestSpans.path input head).length+225 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      d.pc=0x80001422#32 ∧ d.get 10=(if RuntimeRequestSpans.path input head=WireSpec.ascii "/setpoint" then 1#32 else 0#32) ∧
      d.get 11=0#32 ∧ d.get 9=(if RuntimeRequestSpans.path input head=WireSpec.ascii "/state" then 2#32 else 3#32) ∧
      RuntimeRouteEnvelope.At d after input s head amount rawUsed served lowValue close ∧ LoopTransactionMemory.At after used ∧ d.sameCsr c := by
  obtain ⟨na,a,ba,ta,entry,a9,ac,frameA⟩ := StackRuntimeSecondCandidate.advance h pc result eligible
  obtain ⟨nb,d,bb,tb,pd,d10,d11,abi,dc,frameB,live⟩ := StackRuntimeLiteralMatch.contract .setpoint 0x80001422#32 entry (by decide) (by decide) leading
  have frame : ViewFrame.Region ram (MainPathStateSave.memory (RouteSecondCore.memory ram (rx+BitVec.ofNat 32 head.target.1)) a) sp 3304 := by
    have short := HeadRegionFrame.sub frameB 0 3304 (by decide)
    simp only [BitVec.add_zero] at short
    exact HeadRegionFrame.trans frameA short
  refine ⟨na+nb,d,_,by omega,ta.trans tb,pd,d10,d11,(abi 9 (by decide)).trans a9,live,LoopTransactionMemory.caller metadata frame,dc.trans ac⟩
end E5R.Thermostat.StackRuntimeSecondMatch
