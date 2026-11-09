import Projects.thermostat.RuntimeSetpointWriteInput
import Projects.thermostat.RuntimeApiWriteNext
set_option autoImplicit false
namespace E5R.Thermostat.RuntimeSetpointTransaction
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board

theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head}
    {amount rawUsed served : Nat} {lowValue : Word} {close : Bool} {used : Word}
    (h : RuntimeRouteEnvelope.At c ram input s head amount rawUsed served lowValue close)
    (pc : c.pc=0x80001422#32) (matched : c.get 10=1#32) (captures : c.get 11=0#32)
    (route : RuntimeRequestSpans.path input head=WireSpec.ascii "/setpoint")
    (method : MainMethodSpec.decode (MainMethodBytes.token input head.method.2)=.put)
    (metadata : LoopTransactionMemory.At ram used) (hs bs : List UartTxLoop.Slot)
    (hhs : hs.length=(ResponseHeadSpec.bytes
      (ApiWriteHttpSpec.run s (WireSpec.ascii "/setpoint") none (RuntimeRequestSpans.raw input rawUsed) (RuntimeRequestSpans.body input head amount) (RuntimeRequestInputs.entries head)).status
      (ApiWriteHttpSpec.run s (WireSpec.ascii "/setpoint") none (RuntimeRequestSpans.raw input rawUsed) (RuntimeRequestSpans.body input head amount) (RuntimeRequestInputs.entries head)).mime
      (ApiWriteHttpSpec.run s (WireSpec.ascii "/setpoint") none (RuntimeRequestSpans.raw input rawUsed) (RuntimeRequestSpans.body input head amount) (RuntimeRequestInputs.entries head)).payload.length close).length)
    (hbs : bs.length=(ApiWriteHttpSpec.run s (WireSpec.ascii "/setpoint") none (RuntimeRequestSpans.raw input rawUsed) (RuntimeRequestSpans.body input head amount) (RuntimeRequestInputs.entries head)).payload.length) :
    let reply := ApiWriteHttpSpec.run s (WireSpec.ascii "/setpoint") none (RuntimeRequestSpans.raw input rawUsed) (RuntimeRequestSpans.body input head amount) (RuntimeRequestInputs.entries head)
    ∃ n d after,Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (UartTxLoop.reads hs++UartTxLoop.reads bs)
      (UartTxLoop.events (ResponseHeadSpec.bytes reply.status reply.mime reply.payload.length close)++UartTxLoop.events reply.payload) ∧
      LoopReady.At d after reply.state (if close then 0 else served) := by
  obtain ⟨a,ta,ready,csr,frame,a23,a26,a19⟩ := RuntimeSetpointWriteInput.contract h pc matched captures route method
  have metadataA := LoopTransactionMemory.caller metadata frame
  obtain ⟨nb,d,after,tb,final⟩ := RuntimeApiWriteCaller.next ready metadataA (a19.trans h.stable.uart)
    (a23.trans h.future) (a26.trans h.three) ((congrArg Prod.fst csr).trans h.stable.masked) hs bs hhs hbs
  exact ⟨28+nb,d,after,by simpa only [RuntimeRequestSpans.body,MainRequestSpans.body,show RuntimeRequestInputs.entries head=MainRequestInputs.entries head by rfl,List.nil_append] using ta.observed.trans tb,final⟩
end E5R.Thermostat.RuntimeSetpointTransaction
