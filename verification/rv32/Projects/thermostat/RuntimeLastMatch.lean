import Projects.thermostat.RuntimeRelayEntry
import Projects.thermostat.RuntimeRelayMatch
set_option autoImplicit false
namespace E5R.Thermostat.RuntimeLastMatch
open E5R E5R.Thermostat HttpRequestSpec

/-- Actual remaining route search from first candidate return to last return.
    All literal denial and relay matching decisions derive from pure policy. -/
theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head}
    {amount rawUsed served : Nat} {lowValue : Word} {close : Bool} {used : Word}
    (h : RuntimeRouteEnvelope.At c ram input s head amount rawUsed served lowValue close)
    (pc : c.pc=0x800013d2#32)
    (result : c.get 10=(if RuntimeRequestSpans.path input head=WireSpec.ascii "/state" then 1#32 else 0#32))
    (denied : ∀ kind : RouteLiteralInfo.Kind,RuntimeRequestSpans.path input head=RouteLiteralInfo.text kind →
      RouteSpec.allows (RouteLiteralInfo.route kind) (MainMethodSpec.decode (MainMethodBytes.token input head.method.2))=false)
    (leading : ∃ ys,RuntimeRequestSpans.path input head=47#8::ys) (metadata : LoopTransactionMemory.At ram used) :
    ∃ n d after,n≤45*(RuntimeRequestSpans.path input head).length+934 ∧ Quiet.Steps UartPlatform.board img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      d.pc=0x80001856#32 ∧ d.get 10=(if RouteSpec.relayPath (RuntimeRequestSpans.path input head) then 1#32 else 0#32) ∧
      d.get 11=RouteRelayBody.count (RuntimeRequestSpans.path input head) ∧
      d.get 9=(if RuntimeRelayEntry.known (RuntimeRequestSpans.path input head) then 2#32 else 3#32) ∧
      MainTransactionStable.At d after input s ∧ LoopTransactionMemory.At after used ∧ d.sameCsr c := by
  obtain ⟨na,a,mid,ba,ta,entry,flag,metadataA,ca⟩ := RuntimeRelayEntry.contract h pc result denied leading metadata
  obtain ⟨nb,d,bb,tb,pd,d10,d11,abi,cb,low,high,stable⟩ := RuntimeRelayMatch.contract entry leading
  have lowSmall : ViewFrame.Region mid (RuntimeRelayMatch.memory mid a input head) RuntimeRouteEnvelope.sp 3304 := by
    intro i;exact low ⟨i.val,by have := i.isLt;omega⟩
  exact ⟨na+nb,d,_,by omega,ta.trans tb,pd,d10,d11,(abi 9 (by decide)).trans flag,stable,
    LoopTransactionMemory.caller metadataA lowSmall,cb.trans ca⟩
end E5R.Thermostat.RuntimeLastMatch
