import Projects.thermostat.LoopCloseRequest
import Projects.thermostat.LoopRouteFrames
import Projects.thermostat.LoopModeChain
import Projects.thermostat.LoopModeWriteInput
import Projects.thermostat.LoopApiWriteNext
import Projects.thermostat.MainReadReset
import Projects.thermostat.MainModeCaller
set_option autoImplicit false
namespace E5R.Thermostat.LoopModeTransaction
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board
/-- Actual Request, route attempts, caller, all write outcomes and next request. -/
theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot}
    {head : Head} {amount served : Nat} {used : Word}
    (h : MainRequestBuild.Ready c ram input s head amount served) (metadata : LoopTransactionMemory.At ram used)
    (route : MainRequestSpans.path input head=WireSpec.ascii "/mode")
    (method : MainMethodSpec.decode (MainMethodBytes.token input head.method.2)=.put)
    (hs : Bool → List UartTxLoop.Slot) (bs : List UartTxLoop.Slot)
    (hhs : ∀ close, (hs close).length=(ResponseHeadSpec.bytes
      (ApiWriteHttpSpec.run s (WireSpec.ascii "/mode") none (MainRequestSpans.raw input head amount) (MainRequestSpans.body input head amount) (MainRequestInputs.entries head)).status
      (ApiWriteHttpSpec.run s (WireSpec.ascii "/mode") none (MainRequestSpans.raw input head amount) (MainRequestSpans.body input head amount) (MainRequestInputs.entries head)).mime
      (ApiWriteHttpSpec.run s (WireSpec.ascii "/mode") none (MainRequestSpans.raw input head amount) (MainRequestSpans.body input head amount) (MainRequestInputs.entries head)).payload.length close).length)
    (hbs : bs.length=(ApiWriteHttpSpec.run s (WireSpec.ascii "/mode") none (MainRequestSpans.raw input head amount) (MainRequestSpans.body input head amount) (MainRequestInputs.entries head)).payload.length) :
    let reply := ApiWriteHttpSpec.run s (WireSpec.ascii "/mode") none (MainRequestSpans.raw input head amount) (MainRequestSpans.body input head amount) (MainRequestInputs.entries head)
    ∃ n d after close, Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (UartTxLoop.reads (hs close)++UartTxLoop.reads bs)
      (UartTxLoop.events (ResponseHeadSpec.bytes reply.status reply.mime reply.payload.length close)++UartTxLoop.events reply.payload) ∧
      close=MainCloseSpec.mustClose head.minor served (MainRequestSpans.raw input head amount) (MainRequestInputs.entries head) ∧
      LoopReady.At d after reply.state (if close then 0 else served) := by
  dsimp only
  obtain ⟨cn,a,ra,close,closed,closeReady,metadataA⟩ := LoopCloseRequest.contract h metadata
  obtain ⟨b,router,routerReady,metadataB⟩ := LoopRouteFrames.router closeReady metadataA
  obtain ⟨e,first,firstReady,epc,failed,_,e25,_,firstFrame,e23,e26⟩ := LoopModeChain.first routerReady
    (MainRouterFutures.initialized ra) (MainReadReset.reply_capacity ra) route
  have metadataE := LoopTransactionMemory.caller metadataB firstFrame
  obtain ⟨f,fn,rf,_,second,secondReady,fpc,failedF,_,f25,_,frameF,f23,f26⟩ := LoopModeChain.next true firstReady epc failed route
  have metadataF := LoopTransactionMemory.caller metadataE frameF
  obtain ⟨g,gn,rg,_,third,thirdReady,gpc,failedG,_,g25,_,frameG,g23,g26⟩ := LoopModeChain.next false secondReady fpc failedF route
  have metadataG := LoopTransactionMemory.caller metadataF frameG
  obtain ⟨k,kn,rk,_,fourth,fourthReady,kpc,matched,captures,k25,_,frameK,k23,k26⟩ := LoopModeChain.fourth thirdReady gpc failedG route
  have metadataK := LoopTransactionMemory.caller metadataG frameK
  have pointer : k.get 25=0x80fffa58#32 := k25.trans (g25.trans (f25.trans (e25.trans routerReady.secondSlot)))
  obtain ⟨j,setup,ready,_,setupFrame,j19,j23,j26⟩ := LoopModeWriteInput.contract fourthReady kpc matched captures route method pointer
  have metadataJ := LoopTransactionMemory.caller metadataK setupFrame
  obtain ⟨last,d,after,sent,loop⟩ := LoopApiWriteCaller.next (MainApiWriteCaller.of_mode ready) metadataJ
    (j19.trans fourthReady.stable.uart) (j23.trans (k23.trans (g23.trans (f23.trans (e23.trans routerReady.future)))))
    (j26.trans (k26.trans (g26.trans (f26.trans (e26.trans routerReady.three))))) ready.masked (hs close) bs (hhs close) hbs
  refine ⟨cn+83+138+fn+gn+kn+27+last,d,after,close,?_,closeReady.spec,loop⟩
  have run := ((((((closed.trans router).trans first).trans second).trans third).trans fourth).trans setup).observed.trans sent
  simpa only [List.nil_append,Nat.add_assoc] using run
end E5R.Thermostat.LoopModeTransaction
