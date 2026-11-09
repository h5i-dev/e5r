import Projects.thermostat.RuntimeHeadInput
import Projects.thermostat.RuntimeMethodDecoded
import Projects.thermostat.RuntimeReadNext
import Projects.thermostat.LoopReadDecoded
import Projects.thermostat.LoopReadNext
set_option autoImplicit false
namespace E5R.Thermostat.RuntimeHeadTransaction
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board

/-- Generic framing/raw extents join the already audited actual Read/JSON/HTTP
    path and real next-request loop. The read command comes from Wire decoding. -/
theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head}
    {amount rawUsed served : Nat} {lowValue : Word} {close : Bool} {used : Word}
    (h : RuntimeRouteEnvelope.At c ram input s head amount rawUsed served lowValue close)
    (pc : c.pc=0x800013d2#32) (matched : c.get 10=1#32) (captures : c.get 11=0#32)
    (metadata : LoopTransactionMemory.At ram used)
    (route : RuntimeRequestSpans.path input head=WireSpec.ascii "/state")
    (method : MainMethodSpec.decode (MainMethodBytes.token input head.method.2)=.head)
    (hs bs : List UartTxLoop.Slot)
    (hhs : hs.length=(ResponseHeadSpec.bytes 200 (WireSpec.ascii "application/json") (ReplyJson.snapshot s).length close).length)
    (hbs : bs.length=0) :
    ∃ n d after, Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (UartTxLoop.reads hs++UartTxLoop.reads bs)
      (UartTxLoop.events (ResponseHeadSpec.bytes 200 (WireSpec.ascii "application/json") (ReplyJson.snapshot s).length close)++
        UartTxLoop.events []) ∧ LoopReady.At d after s (if close then 0 else served) := by
  obtain ⟨a,setup,routeReady,_,setupFrame,a23,a26⟩ := RuntimeHeadInput.contract h pc matched captures route method h.replyCapacity
  have metadataA := LoopTransactionMemory.caller metadata setupFrame
  obtain ⟨b,nb,mid,_,decoded,readReady,_,decodeFrame,b23,b26⟩ := RuntimeMethodDecoded.contract routeReady
  have metadataB := LoopTransactionMemory.caller metadataA decodeFrame
  have room : close=false → served<100 := by
    intro kept
    by_cases reached : 100≤served
    · have forced := MainCloseSpec.limit head.minor served reached (RuntimeRequestSpans.raw input rawUsed) (RuntimeRequestInputs.entries head)
      have contradiction := h.closeSpec.trans forced
      rw [kept] at contradiction;cases contradiction
    · omega
  obtain ⟨last,d,after,sent,ready⟩ := RuntimeReadNext.contract readReady metadataB
    (b23.trans (a23.trans h.future)) (b26.trans (a26.trans h.three)) room hs bs hhs hbs
  refine ⟨32+nb+last,d,after,?_,ready⟩
  simpa [ResponseHeadSpec.body] using (setup.trans decoded).observed.trans sent
end E5R.Thermostat.RuntimeHeadTransaction
