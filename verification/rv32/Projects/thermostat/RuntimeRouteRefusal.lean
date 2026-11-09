import Projects.thermostat.RuntimeRelayEntry
import Projects.thermostat.RuntimeRelayRefusal
import Projects.thermostat.RouteRefusalSpec
set_option autoImplicit false
namespace E5R.Thermostat.RuntimeRouteRefusal
open E5R E5R.Thermostat HttpRequestSpec

theorem status_eq (path : List (BitVec 8)) : RuntimeRefusalNext.status (decide (RuntimeRelayEntry.known path))=RouteRefusalSpec.status path := by
  by_cases yes : RuntimeRelayEntry.known path
  · have yes' : RouteRefusalSpec.known path := yes
    simp only [RuntimeRefusalNext.status,RouteRefusalSpec.status,yes,yes',decide_true,ite_true]
  · have no' : ¬RouteRefusalSpec.known path := yes
    simp only [RuntimeRefusalNext.status,RouteRefusalSpec.status,yes,no',decide_false,Bool.false_eq_true,ite_false]

/-- Pure routing denial through all real remaining candidates, exact empty
    refusal reply, and reusable next-request boundary. -/
theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head}
    {amount rawUsed served : Nat} {lowValue : Word} {close : Bool} {used : Word}
    (h : RuntimeRouteEnvelope.At c ram input s head amount rawUsed served lowValue close)
    (pc : c.pc=0x800013d2#32)
    (result : c.get 10=(if RuntimeRequestSpans.path input head=WireSpec.ascii "/state" then 1#32 else 0#32))
    (denied : ∀ kind : RouteLiteralInfo.Kind,RuntimeRequestSpans.path input head=RouteLiteralInfo.text kind →
      RouteSpec.allows (RouteLiteralInfo.route kind) (MainMethodSpec.decode (MainMethodBytes.token input head.method.2))=false)
    (missing : ¬RouteSpec.relayPath (RuntimeRequestSpans.path input head))
    (leading : ∃ ys,RuntimeRequestSpans.path input head=47#8::ys) (metadata : LoopTransactionMemory.At ram used)
    (slots : List UartTxLoop.Slot)
    (length : slots.length=(ResponseHeadSpec.bytes (RouteRefusalSpec.status (RuntimeRequestSpans.path input head)) [] 0 close).length) :
    ∃ n d after,Observed.Steps UartPlatform.board img n ⟨c,ram⟩ ⟨d,after⟩ (UartTxLoop.reads slots)
      (UartTxLoop.events (ResponseHeadSpec.bytes (RouteRefusalSpec.status (RuntimeRequestSpans.path input head)) [] 0 close)) ∧
      LoopReady.At d after s (if close then 0 else served) := by
  obtain ⟨na,a,mid,_,ta,entry,flag,metadataA,_⟩ := RuntimeRelayEntry.contract h pc result denied leading metadata
  have flagWord : a.get 9=(if decide (RuntimeRelayEntry.known (RuntimeRequestSpans.path input head)) then 2#32 else 3#32) := by
    by_cases yes : RuntimeRelayEntry.known (RuntimeRequestSpans.path input head) <;> simpa only [yes,decide_true,decide_false,ite_true,Bool.false_eq_true,ite_false] using flag
  obtain ⟨nb,d,after,tb,ready⟩ := RuntimeRelayRefusal.contract (decide (RuntimeRelayEntry.known (RuntimeRequestSpans.path input head))) entry flagWord leading missing metadataA slots (by rw [status_eq];exact length)
  exact ⟨na+nb,d,after,by simpa only [status_eq,List.nil_append] using ta.observed.trans tb,ready⟩
end E5R.Thermostat.RuntimeRouteRefusal
