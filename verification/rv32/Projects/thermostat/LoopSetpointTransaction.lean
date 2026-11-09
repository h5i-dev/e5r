import Projects.thermostat.LoopCloseRequest
import Projects.thermostat.LoopRouteFrames
import Projects.thermostat.LoopSetpointChain
import Projects.thermostat.LoopSetpointWriteInput
import Projects.thermostat.LoopApiWriteNext
import Projects.thermostat.MainReadReset
import Projects.thermostat.MainModeCaller
set_option autoImplicit false
namespace E5R.Thermostat.LoopSetpointTransaction
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board
/-- Actual Request, route attempts, caller, all write outcomes and next request. -/
theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot}
    {head : Head} {amount served : Nat} {used : Word}
    (h : MainRequestBuild.Ready c ram input s head amount served) (metadata : LoopTransactionMemory.At ram used)
    (route : MainRequestSpans.path input head=WireSpec.ascii "/setpoint")
    (method : MainMethodSpec.decode (MainMethodBytes.token input head.method.2)=.put)
    (hs : Bool → List UartTxLoop.Slot) (bs : List UartTxLoop.Slot)
    (hhs : ∀ close, (hs close).length=(ResponseHeadSpec.bytes
      (ApiWriteHttpSpec.run s (WireSpec.ascii "/setpoint") none (MainRequestSpans.raw input head amount) (MainRequestSpans.body input head amount) (MainRequestInputs.entries head)).status
      (ApiWriteHttpSpec.run s (WireSpec.ascii "/setpoint") none (MainRequestSpans.raw input head amount) (MainRequestSpans.body input head amount) (MainRequestInputs.entries head)).mime
      (ApiWriteHttpSpec.run s (WireSpec.ascii "/setpoint") none (MainRequestSpans.raw input head amount) (MainRequestSpans.body input head amount) (MainRequestInputs.entries head)).payload.length close).length)
    (hbs : bs.length=(ApiWriteHttpSpec.run s (WireSpec.ascii "/setpoint") none (MainRequestSpans.raw input head amount) (MainRequestSpans.body input head amount) (MainRequestInputs.entries head)).payload.length) :
    let reply := ApiWriteHttpSpec.run s (WireSpec.ascii "/setpoint") none (MainRequestSpans.raw input head amount) (MainRequestSpans.body input head amount) (MainRequestInputs.entries head)
    ∃ n d after close, Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (UartTxLoop.reads (hs close)++UartTxLoop.reads bs)
      (UartTxLoop.events (ResponseHeadSpec.bytes reply.status reply.mime reply.payload.length close)++UartTxLoop.events reply.payload) ∧
      close=MainCloseSpec.mustClose head.minor served (MainRequestSpans.raw input head amount) (MainRequestInputs.entries head) ∧
      LoopReady.At d after reply.state (if close then 0 else served) := by
  dsimp only
  obtain ⟨cn,a,ra,close,closed,closeReady,metadataA⟩ := LoopCloseRequest.contract h metadata
  obtain ⟨b,router,routerReady,metadataB⟩ := LoopRouteFrames.router closeReady metadataA
  obtain ⟨e,first,firstReady,epc,failed,_,_,firstFrame,e23,e26⟩ := LoopSetpointChain.first routerReady
    (MainRouterFutures.initialized ra) (MainReadReset.reply_capacity ra) route
  have metadataE := LoopTransactionMemory.caller metadataB firstFrame
  obtain ⟨f,fn,rf,_,second,secondReady,fpc,matched,captures,_,frameF,f23,f26⟩ := LoopSetpointChain.second firstReady epc failed route
  have metadataF := LoopTransactionMemory.caller metadataE frameF
  obtain ⟨j,setup,ready,_,setupFrame,j19,j23,j26⟩ := LoopSetpointWriteInput.contract secondReady fpc matched captures route method
  have metadataJ := LoopTransactionMemory.caller metadataF setupFrame
  obtain ⟨last,d,after,sent,loop⟩ := LoopApiWriteCaller.next (MainApiWriteCaller.of_setpoint ready) metadataJ
    (j19.trans secondReady.stable.uart) (j23.trans (f23.trans (e23.trans routerReady.future)))
    (j26.trans (f26.trans (e26.trans routerReady.three))) ready.masked (hs close) bs (hhs close) hbs
  refine ⟨cn+83+158+fn+28+last,d,after,close,?_,closeReady.spec,loop⟩
  have run := ((((closed.trans router).trans first).trans second).trans setup).observed.trans sent
  simpa only [List.nil_append,Nat.add_assoc] using run
end E5R.Thermostat.LoopSetpointTransaction
