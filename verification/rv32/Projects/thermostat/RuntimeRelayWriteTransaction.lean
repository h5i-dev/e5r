import Projects.thermostat.RuntimeRelayEntry
import Projects.thermostat.RuntimeRelaySuccess
import Projects.thermostat.RuntimeRelayWriteInput
import Projects.thermostat.RuntimeApiWriteNext
set_option autoImplicit false
namespace E5R.Thermostat.RuntimeRelayWriteTransaction
open E5R E5R.Thermostat HttpRequestSpec

def reply (s : Spec.Snapshot) (input : List (BitVec 8)) (head : Head) (amount rawUsed : Nat) :=
  ApiWriteHttpSpec.run s (RuntimeRequestSpans.path input head) (some ((RuntimeRequestSpans.path input head).drop 7))
    (RuntimeRequestSpans.raw input rawUsed) (RuntimeRequestSpans.body input head amount) (RuntimeRequestInputs.entries head)

theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head}
    {amount rawUsed served : Nat} {lowValue : Word} {close : Bool} {used : Word}
    (h : RuntimeRouteEnvelope.At c ram input s head amount rawUsed served lowValue close)
    (pc : c.pc=0x800013d2#32)
    (result : c.get 10=(if RuntimeRequestSpans.path input head=WireSpec.ascii "/state" then 1#32 else 0#32))
    (route : RouteSpec.relayPath (RuntimeRequestSpans.path input head))
    (method : MainMethodSpec.decode (MainMethodBytes.token input head.method.2)=.put)
    (leading : ∃ ys,RuntimeRequestSpans.path input head=47#8::ys) (metadata : LoopTransactionMemory.At ram used)
    (hs bs : List UartTxLoop.Slot)
    (hhs : hs.length=(ResponseHeadSpec.bytes (reply s input head amount rawUsed).status (reply s input head amount rawUsed).mime (reply s input head amount rawUsed).payload.length close).length)
    (hbs : bs.length=(reply s input head amount rawUsed).payload.length) :
    ∃ n d after,Observed.Steps UartPlatform.board img n ⟨c,ram⟩ ⟨d,after⟩ (UartTxLoop.reads hs++UartTxLoop.reads bs)
      (UartTxLoop.events (ResponseHeadSpec.bytes (reply s input head amount rawUsed).status (reply s input head amount rawUsed).mime (reply s input head amount rawUsed).payload.length close)++
        UartTxLoop.events (reply s input head amount rawUsed).payload) ∧
      LoopReady.At d after (reply s input head amount rawUsed).state (if close then 0 else served) := by
  have denied (kind : RouteLiteralInfo.Kind) (selected : RuntimeRequestSpans.path input head=RouteLiteralInfo.text kind) :
      RouteSpec.allows (RouteLiteralInfo.route kind) (MainMethodSpec.decode (MainMethodBytes.token input head.method.2))=false := by
    have headPrefix := route.1
    rw [selected] at headPrefix
    have different : (RouteLiteralInfo.text kind).take 7≠WireSpec.ascii "/relay/" := by cases kind <;> decide +kernel
    exact False.elim (different headPrefix)
  obtain ⟨na,a,mid,_,ta,entry,_,metadataA,_⟩ := RuntimeRelayEntry.contract h pc result denied leading metadata
  obtain ⟨nb,b,mem,tb,captured,frameB⟩ := RuntimeRelaySuccess.contract entry route
  have metadataB := LoopTransactionMemory.caller metadataA frameB
  obtain ⟨d,td,ready,masked,frameD,d19,d23,d26⟩ := RuntimeRelayWriteInput.contract captured method
  have metadataD := LoopTransactionMemory.caller metadataB frameD
  have pathEq : RuntimeRelayCaptured.path ((RuntimeRequestSpans.path input head).drop 7)=RuntimeRequestSpans.path input head := RelaySuccessMemory.path _ route
  have headersEq : RuntimeRequestInputs.entries head=MainRequestInputs.entries head := rfl
  have headerSlots : hs.length=(ResponseHeadSpec.bytes
      (ApiWriteHttpSpec.run s (RuntimeRelayCaptured.path ((RuntimeRequestSpans.path input head).drop 7)) (some ((RuntimeRequestSpans.path input head).drop 7)) (RuntimeRequestSpans.raw input rawUsed) (MainRequestSpans.body input head amount) (MainRequestInputs.entries head)).status
      (ApiWriteHttpSpec.run s (RuntimeRelayCaptured.path ((RuntimeRequestSpans.path input head).drop 7)) (some ((RuntimeRequestSpans.path input head).drop 7)) (RuntimeRequestSpans.raw input rawUsed) (MainRequestSpans.body input head amount) (MainRequestInputs.entries head)).mime
      (ApiWriteHttpSpec.run s (RuntimeRelayCaptured.path ((RuntimeRequestSpans.path input head).drop 7)) (some ((RuntimeRequestSpans.path input head).drop 7)) (RuntimeRequestSpans.raw input rawUsed) (MainRequestSpans.body input head amount) (MainRequestInputs.entries head)).payload.length close).length := by
    rw [pathEq];exact hhs
  have payloadSlots : bs.length=(ApiWriteHttpSpec.run s (RuntimeRelayCaptured.path ((RuntimeRequestSpans.path input head).drop 7)) (some ((RuntimeRequestSpans.path input head).drop 7)) (RuntimeRequestSpans.raw input rawUsed) (MainRequestSpans.body input head amount) (MainRequestInputs.entries head)).payload.length := by rw [pathEq];exact hbs
  obtain ⟨ne,e,final,te,done⟩ := RuntimeApiWriteCaller.next ready metadataD
    (d19.trans ((captured.regs 19 (by decide)).trans entry.live.stable.uart))
    (d23.trans ((captured.regs 23 (by decide)).trans entry.live.future)) (d26.trans ((captured.regs 26 (by decide)).trans entry.live.three)) masked hs bs headerSlots payloadSlots
  refine ⟨na+nb+26+ne,e,final,?_,?_⟩
  · simpa only [reply,pathEq,RuntimeRequestSpans.body,MainRequestSpans.body,headersEq,List.nil_append] using (((ta.observed.trans tb.observed).trans td.observed).trans te)
  · simpa only [reply,pathEq,RuntimeRequestSpans.body,MainRequestSpans.body,headersEq] using done
end E5R.Thermostat.RuntimeRelayWriteTransaction
