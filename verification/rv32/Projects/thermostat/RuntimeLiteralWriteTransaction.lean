import Projects.thermostat.RuntimeLiteralWriteInput
import Projects.thermostat.RuntimeApiWriteNext
set_option autoImplicit false
namespace E5R.Thermostat.RuntimeLiteralWriteTransaction
open E5R E5R.Thermostat HttpRequestSpec

def reply (kind : RouteLiteralInfo.Kind) (s : Spec.Snapshot) (input : List (BitVec 8)) (head : Head) (amount rawUsed : Nat) :=
  ApiWriteHttpSpec.run s (RouteLiteralInfo.text kind) none (RuntimeRequestSpans.raw input rawUsed) (RuntimeRequestSpans.body input head amount) (RuntimeRequestInputs.entries head)

/-- All literal HTTP write routes: actual routing/setup/auth/decoding/engine/
    serialization and exact UART bytes return to the reusable receive boundary. -/
theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head}
    {amount rawUsed served : Nat} {lowValue : Word} {close : Bool} {used : Word}
    (kind : RouteLiteralInfo.Kind) (write : kind≠.state)
    (h : RuntimeRouteEnvelope.At c ram input s head amount rawUsed served lowValue close)
    (pc : c.pc=0x800013d2#32)
    (result : c.get 10=(if RuntimeRequestSpans.path input head=WireSpec.ascii "/state" then 1#32 else 0#32))
    (route : RuntimeRequestSpans.path input head=RouteLiteralInfo.text kind)
    (method : RouteSpec.allows (RouteLiteralInfo.route kind) (MainMethodSpec.decode (MainMethodBytes.token input head.method.2))=true)
    (leading : ∃ ys,RuntimeRequestSpans.path input head=47#8::ys) (metadata : LoopTransactionMemory.At ram used)
    (hs bs : List UartTxLoop.Slot)
    (hhs : hs.length=(ResponseHeadSpec.bytes (reply kind s input head amount rawUsed).status (reply kind s input head amount rawUsed).mime (reply kind s input head amount rawUsed).payload.length close).length)
    (hbs : bs.length=(reply kind s input head amount rawUsed).payload.length) :
    ∃ n d after,Observed.Steps UartPlatform.board img n ⟨c,ram⟩ ⟨d,after⟩ (UartTxLoop.reads hs++UartTxLoop.reads bs)
      (UartTxLoop.events (ResponseHeadSpec.bytes (reply kind s input head amount rawUsed).status (reply kind s input head amount rawUsed).mime (reply kind s input head amount rawUsed).payload.length close)++
        UartTxLoop.events (reply kind s input head amount rawUsed).payload) ∧
      LoopReady.At d after (reply kind s input head amount rawUsed).state (if close then 0 else served) := by
  obtain ⟨na,a,mid,ta,ready,metadataA,uart,future,three,masked⟩ := RuntimeLiteralWriteInput.contract kind write h pc result route method leading metadata
  obtain ⟨nb,d,after,tb,final⟩ := RuntimeApiWriteCaller.next ready metadataA uart future three masked hs bs hhs hbs
  refine ⟨na+nb,d,after,?_,final⟩
  simpa only [reply,RuntimeRequestSpans.body,MainRequestSpans.body,show RuntimeRequestInputs.entries head=MainRequestInputs.entries head by rfl,List.nil_append] using ta.observed.trans tb
end E5R.Thermostat.RuntimeLiteralWriteTransaction
