import Projects.thermostat.ReadRoutePrepare
import Projects.thermostat.StackRuntimeReadInput
import Projects.thermostat.StackRuntimeHeadInput
import Projects.thermostat.StackRuntimeMethodDecoded
import Projects.thermostat.StackReadHandlerPrepare
set_option autoImplicit false
namespace E5R.Thermostat.StackReadRoutePrepare
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := StackBoard.board
theorem get {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head}
    {amount rawUsed served : Nat} {lowValue : Word} {close : Bool} {used : Word}
    (h : RuntimeRouteEnvelope.At c ram input s head amount rawUsed served lowValue close)
    (pc : c.pc=0x800013d2#32) (matched : c.get 10=1#32) (captures : c.get 11=0#32)
    (metadata : LoopTransactionMemory.At ram used)
    (route : RuntimeRequestSpans.path input head=WireSpec.ascii "/state")
    (method : MainMethodSpec.decode (MainMethodBytes.token input head.method.2)=.get)
    : ∃ n d after,Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      NormalSendPhase.Ready d after (ReadHandlerPrepare.reply s) served used true close false := by
  obtain ⟨a,setup,routeReady,_,setupFrame,a23,a26⟩ := StackRuntimeReadInput.contract h pc matched captures route method h.replyCapacity
  have metadataA := LoopTransactionMemory.caller metadata setupFrame
  obtain ⟨b,nb,mid,_,decoded,readReady,_,decodeFrame,b23,b26⟩ := StackRuntimeMethodDecoded.contract routeReady
  have metadataB := LoopTransactionMemory.caller metadataA decodeFrame
  have room : close=false → served<100 := by
    intro kept
    by_cases reached : 100≤served
    · have forced := MainCloseSpec.limit head.minor served reached (RuntimeRequestSpans.raw input rawUsed) (RuntimeRequestInputs.entries head)
      have contradiction := h.closeSpec.trans forced
      rw [kept] at contradiction;cases contradiction
    · omega
  have read : StackRuntimeReadViews.DecodedReady b mid input s served close false :=
    ⟨readReady.acquiredInput,readReady.stable,readReady.serve,readReady.closeByte,readReady.capacity,
      readReady.payload,readReady.replyCapacity,readReady.method⟩
  obtain ⟨last,d,after,bound,prepare,ready⟩ := StackReadHandlerPrepare.contract read metadataB
    (b23.trans (a23.trans h.future)) (b26.trans (a26.trans h.three)) room
  exact ⟨28+nb+last,d,after,(setup.trans decoded).trans prepare,ready⟩

theorem head {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head}
    {amount rawUsed served : Nat} {lowValue : Word} {close : Bool} {used : Word}
    (h : RuntimeRouteEnvelope.At c ram input s head amount rawUsed served lowValue close)
    (pc : c.pc=0x800013d2#32) (matched : c.get 10=1#32) (captures : c.get 11=0#32)
    (metadata : LoopTransactionMemory.At ram used)
    (route : RuntimeRequestSpans.path input head=WireSpec.ascii "/state")
    (method : MainMethodSpec.decode (MainMethodBytes.token input head.method.2)=.head)
    : ∃ n d after,Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      NormalSendPhase.Ready d after (ReadHandlerPrepare.reply s) served used true close true := by
  obtain ⟨a,setup,routeReady,_,setupFrame,a23,a26⟩ := StackRuntimeHeadInput.contract h pc matched captures route method h.replyCapacity
  have metadataA := LoopTransactionMemory.caller metadata setupFrame
  obtain ⟨b,nb,mid,_,decoded,readReady,_,decodeFrame,b23,b26⟩ := StackRuntimeMethodDecoded.contract routeReady
  have metadataB := LoopTransactionMemory.caller metadataA decodeFrame
  have room : close=false → served<100 := by
    intro kept
    by_cases reached : 100≤served
    · have forced := MainCloseSpec.limit head.minor served reached (RuntimeRequestSpans.raw input rawUsed) (RuntimeRequestInputs.entries head)
      have contradiction := h.closeSpec.trans forced
      rw [kept] at contradiction;cases contradiction
    · omega
  let read := readReady
  obtain ⟨last,d,after,bound,prepare,ready⟩ := StackReadHandlerPrepare.contract read metadataB
    (b23.trans (a23.trans h.future)) (b26.trans (a26.trans h.three)) room
  exact ⟨32+nb+last,d,after,(setup.trans decoded).trans prepare,ready⟩

end E5R.Thermostat.StackReadRoutePrepare
