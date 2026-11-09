import Projects.thermostat.WriteHandlerPrepare
import Projects.thermostat.RuntimeLiteralWriteTransaction
import Projects.thermostat.RuntimeRelayWriteTransaction
set_option autoImplicit false
namespace E5R.Thermostat.WriteRoutePrepare
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board
theorem literal {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head}
    {amount rawUsed served : Nat} {lowValue : Word} {close : Bool} {used : Word}
    (kind : RouteLiteralInfo.Kind) (write : kind≠.state)
    (h : RuntimeRouteEnvelope.At c ram input s head amount rawUsed served lowValue close)
    (pc : c.pc=0x800013d2#32)
    (result : c.get 10=(if RuntimeRequestSpans.path input head=WireSpec.ascii "/state" then 1#32 else 0#32))
    (route : RuntimeRequestSpans.path input head=RouteLiteralInfo.text kind)
    (method : RouteSpec.allows (RouteLiteralInfo.route kind) (MainMethodSpec.decode (MainMethodBytes.token input head.method.2))=true)
    (leading : ∃ ys,RuntimeRequestSpans.path input head=47#8::ys) (metadata : LoopTransactionMemory.At ram used)
    : ∃ n d after json,Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      NormalSendPhase.Ready d after (RuntimeLiteralWriteTransaction.reply kind s input head amount rawUsed) served used json close false := by
  obtain ⟨na,a,mid,ta,ready,metadataA,uart,future,three,masked⟩ := RuntimeLiteralWriteInput.contract kind write h pc result route method leading metadata
  obtain ⟨nb,d,after,json,prepare,final⟩ := WriteHandlerPrepare.prepare ready metadataA uart future three masked
  refine ⟨na+nb,d,after,json,ta.trans prepare,?_⟩
  simpa only [RuntimeLiteralWriteTransaction.reply,RuntimeRequestSpans.body,MainRequestSpans.body,
    show RuntimeRequestInputs.entries head=MainRequestInputs.entries head by rfl] using final

theorem relay {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head}
    {amount rawUsed served : Nat} {lowValue : Word} {close : Bool} {used : Word}
    (h : RuntimeRouteEnvelope.At c ram input s head amount rawUsed served lowValue close)
    (pc : c.pc=0x800013d2#32)
    (result : c.get 10=(if RuntimeRequestSpans.path input head=WireSpec.ascii "/state" then 1#32 else 0#32))
    (route : RouteSpec.relayPath (RuntimeRequestSpans.path input head))
    (method : MainMethodSpec.decode (MainMethodBytes.token input head.method.2)=.put)
    (leading : ∃ ys,RuntimeRequestSpans.path input head=47#8::ys) (metadata : LoopTransactionMemory.At ram used)
    : ∃ n d after json,Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      NormalSendPhase.Ready d after (RuntimeRelayWriteTransaction.reply s input head amount rawUsed) served used json close false := by
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
  obtain ⟨ne,e,after,json,prepare,final⟩ := WriteHandlerPrepare.prepare ready metadataD
    (d19.trans ((captured.regs 19 (by decide)).trans entry.live.stable.uart))
    (d23.trans ((captured.regs 23 (by decide)).trans entry.live.future))
    (d26.trans ((captured.regs 26 (by decide)).trans entry.live.three)) masked
  refine ⟨na+nb+26+ne,e,after,json,((ta.trans tb).trans td).trans prepare,?_⟩
  simpa only [RuntimeRelayWriteTransaction.reply,pathEq,RuntimeRequestSpans.body,MainRequestSpans.body,headersEq] using final

end E5R.Thermostat.WriteRoutePrepare
