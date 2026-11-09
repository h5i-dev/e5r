import Projects.thermostat.RuntimeRelayEntry
import Projects.thermostat.RuntimeRelayWrongMethod
set_option autoImplicit false
namespace E5R.Thermostat.RuntimeRouteRelayWrongMethod
open E5R E5R.Thermostat HttpRequestSpec

theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head}
    {amount rawUsed served : Nat} {lowValue : Word} {close : Bool} {used : Word}
    (h : RuntimeRouteEnvelope.At c ram input s head amount rawUsed served lowValue close)
    (pc : c.pc=0x800013d2#32)
    (result : c.get 10=(if RuntimeRequestSpans.path input head=WireSpec.ascii "/state" then 1#32 else 0#32))
    (route : RouteSpec.relayPath (RuntimeRequestSpans.path input head))
    (method : MainMethodSpec.decode (MainMethodBytes.token input head.method.2)≠.put)
    (leading : ∃ ys,RuntimeRequestSpans.path input head=47#8::ys) (metadata : LoopTransactionMemory.At ram used)
    (slots : List UartTxLoop.Slot) (length : slots.length=(ResponseHeadSpec.bytes 405 [] 0 close).length) :
    ∃ n d after,Observed.Steps UartPlatform.board img n ⟨c,ram⟩ ⟨d,after⟩ (UartTxLoop.reads slots)
      (UartTxLoop.events (ResponseHeadSpec.bytes 405 [] 0 close)) ∧ LoopReady.At d after s (if close then 0 else served) := by
  have denied (kind : RouteLiteralInfo.Kind) (selected : RuntimeRequestSpans.path input head=RouteLiteralInfo.text kind) :
      RouteSpec.allows (RouteLiteralInfo.route kind) (MainMethodSpec.decode (MainMethodBytes.token input head.method.2))=false := by
    have headPrefix := route.1
    rw [selected] at headPrefix
    have different : (RouteLiteralInfo.text kind).take 7≠WireSpec.ascii "/relay/" := by cases kind <;> decide +kernel
    exact False.elim (different headPrefix)
  obtain ⟨na,a,mid,_,ta,entry,_,metadataA,_⟩ := RuntimeRelayEntry.contract h pc result denied leading metadata
  obtain ⟨nb,d,after,tb,done⟩ := RuntimeRelayWrongMethod.contract entry leading route method metadataA slots length
  exact ⟨na+nb,d,after,by simpa only [List.nil_append] using ta.observed.trans tb,done⟩
end E5R.Thermostat.RuntimeRouteRelayWrongMethod
