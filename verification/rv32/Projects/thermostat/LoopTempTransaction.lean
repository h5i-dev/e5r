import Projects.thermostat.LoopCloseRequest
import Projects.thermostat.LoopRouteFrames
import Projects.thermostat.LoopTempChain
import Projects.thermostat.LoopTempWriteInput
import Projects.thermostat.LoopApiWriteNext
import Projects.thermostat.MainReadReset
import Projects.thermostat.MainModeCaller
set_option autoImplicit false
namespace E5R.Thermostat.LoopTempTransaction
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board
/-- Actual Request, route attempts, caller, all write outcomes and next request. -/
theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot}
    {head : Head} {amount served : Nat} {used : Word}
    (h : MainRequestBuild.Ready c ram input s head amount served) (metadata : LoopTransactionMemory.At ram used)
    (route : MainRequestSpans.path input head=WireSpec.ascii "/temp")
    (method : MainMethodSpec.decode (MainMethodBytes.token input head.method.2)=.post)
    (hs : Bool → List UartTxLoop.Slot) (bs : List UartTxLoop.Slot)
    (hhs : ∀ close, (hs close).length=(ResponseHeadSpec.bytes
      (ApiWriteHttpSpec.run s (WireSpec.ascii "/temp") none (MainRequestSpans.raw input head amount) (MainRequestSpans.body input head amount) (MainRequestInputs.entries head)).status
      (ApiWriteHttpSpec.run s (WireSpec.ascii "/temp") none (MainRequestSpans.raw input head amount) (MainRequestSpans.body input head amount) (MainRequestInputs.entries head)).mime
      (ApiWriteHttpSpec.run s (WireSpec.ascii "/temp") none (MainRequestSpans.raw input head amount) (MainRequestSpans.body input head amount) (MainRequestInputs.entries head)).payload.length close).length)
    (hbs : bs.length=(ApiWriteHttpSpec.run s (WireSpec.ascii "/temp") none (MainRequestSpans.raw input head amount) (MainRequestSpans.body input head amount) (MainRequestInputs.entries head)).payload.length) :
    let reply := ApiWriteHttpSpec.run s (WireSpec.ascii "/temp") none (MainRequestSpans.raw input head amount) (MainRequestSpans.body input head amount) (MainRequestInputs.entries head)
    ∃ n d after close, Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (UartTxLoop.reads (hs close)++UartTxLoop.reads bs)
      (UartTxLoop.events (ResponseHeadSpec.bytes reply.status reply.mime reply.payload.length close)++UartTxLoop.events reply.payload) ∧
      close=MainCloseSpec.mustClose head.minor served (MainRequestSpans.raw input head amount) (MainRequestInputs.entries head) ∧
      LoopReady.At d after reply.state (if close then 0 else served) := by
  dsimp only
  obtain ⟨cn,a,ra,close,closed,closeReady,metadataA⟩ := LoopCloseRequest.contract h metadata
  obtain ⟨b,router,routerReady,metadataB⟩ := LoopRouteFrames.router closeReady metadataA
  obtain ⟨e,first,firstReady,_⟩ := MainTempFirst.contract routerReady (MainRouterFutures.initialized ra) route (MainReadReset.reply_capacity ra)
  have metadataE := LoopTransactionMemory.caller metadataB (LoopRouteFrames.saved _ b)
  obtain ⟨f,fn,rf,_,second,secondReady,fpc,failed,_,_,frameF,f23,f26⟩ := LoopTempChain.next true
    (MainRouteEnvelope.fromFirst firstReady) firstReady.pc firstReady.result route
  have metadataF := LoopTransactionMemory.caller metadataE frameF
  obtain ⟨g,gn,rg,_,third,thirdReady,gpc,matched,captures,_,frameG,g23,g26⟩ := LoopTempChain.next false secondReady fpc failed route
  have metadataG := LoopTransactionMemory.caller metadataF frameG
  obtain ⟨j,setup,ready,_,setupFrame,j19,j23,j26⟩ := LoopTempWriteInput.contract thirdReady gpc matched captures route method
  have metadataJ := LoopTransactionMemory.caller metadataG setupFrame
  obtain ⟨last,d,after,sent,loop⟩ := LoopApiWriteCaller.next (MainApiWriteCaller.of_temp ready) metadataJ
    (j19.trans thirdReady.stable.uart) (j23.trans (g23.trans (f23.trans firstReady.future)))
    (j26.trans (g26.trans (f26.trans firstReady.three))) ready.masked (hs close) bs (hhs close) hbs
  refine ⟨cn+83+138+fn+gn+28+last,d,after,close,?_,closeReady.spec,loop⟩
  have run := (((((closed.trans router).trans first).trans second).trans third).trans setup).observed.trans sent
  simpa only [List.nil_append,Nat.add_assoc] using run
end E5R.Thermostat.LoopTempTransaction
