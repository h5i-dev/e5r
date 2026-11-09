import Projects.thermostat.LoopCloseRequest
import Projects.thermostat.LoopRouteFrames
import Projects.thermostat.LoopRelayChain
import Projects.thermostat.LoopRelayWriteInput
import Projects.thermostat.LoopApiWriteNext
import Projects.thermostat.MainReadReset
import Projects.thermostat.MainModeCaller
set_option autoImplicit false
namespace E5R.Thermostat.LoopRelayTransaction
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board
/-- Actual Request, route attempts, caller, all write outcomes and next request. -/
theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot}
    {head : Head} {amount served : Nat} {used : Word} (param : List (BitVec 8)) (nonempty : param≠[]) (noSlash : ∀ b∈param, b≠47#8)
    (h : MainRequestBuild.Ready c ram input s head amount served) (metadata : LoopTransactionMemory.At ram used)
    (route : MainRequestSpans.path input head=MainRelayCaptured.path param)
    (method : MainMethodSpec.decode (MainMethodBytes.token input head.method.2)=.put)
    (hs : Bool → List UartTxLoop.Slot) (bs : List UartTxLoop.Slot)
    (hhs : ∀ close, (hs close).length=(ResponseHeadSpec.bytes
      (ApiWriteHttpSpec.run s (MainRelayCaptured.path param) (some param) (MainRequestSpans.raw input head amount) (MainRequestSpans.body input head amount) (MainRequestInputs.entries head)).status
      (ApiWriteHttpSpec.run s (MainRelayCaptured.path param) (some param) (MainRequestSpans.raw input head amount) (MainRequestSpans.body input head amount) (MainRequestInputs.entries head)).mime
      (ApiWriteHttpSpec.run s (MainRelayCaptured.path param) (some param) (MainRequestSpans.raw input head amount) (MainRequestSpans.body input head amount) (MainRequestInputs.entries head)).payload.length close).length)
    (hbs : bs.length=(ApiWriteHttpSpec.run s (MainRelayCaptured.path param) (some param) (MainRequestSpans.raw input head amount) (MainRequestSpans.body input head amount) (MainRequestInputs.entries head)).payload.length) :
    let reply := ApiWriteHttpSpec.run s (MainRelayCaptured.path param) (some param) (MainRequestSpans.raw input head amount) (MainRequestSpans.body input head amount) (MainRequestInputs.entries head)
    ∃ n d after close, Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (UartTxLoop.reads (hs close)++UartTxLoop.reads bs)
      (UartTxLoop.events (ResponseHeadSpec.bytes reply.status reply.mime reply.payload.length close)++UartTxLoop.events reply.payload) ∧
      close=MainCloseSpec.mustClose head.minor served (MainRequestSpans.raw input head amount) (MainRequestInputs.entries head) ∧
      LoopReady.At d after reply.state (if close then 0 else served) := by
  dsimp only
  obtain ⟨cn,a,ra,close,closed,closeReady,metadataA⟩ := LoopCloseRequest.contract h metadata
  obtain ⟨b,router,routerReady,metadataB⟩ := LoopRouteFrames.router closeReady metadataA
  obtain ⟨e,first,firstReady,epc,failed,_,e24,_,firstFrame,e23,e26⟩ := LoopRelayChain.first routerReady
    (MainRouterFutures.initialized ra) (MainReadReset.reply_capacity ra) param nonempty route
  have metadataE := LoopTransactionMemory.caller metadataB firstFrame
  obtain ⟨f,fn,rf,_,second,secondReady,fpc,failedF,_,f24,_,frameF,f23,f26⟩ := LoopRelayChain.step1 firstReady epc failed param nonempty route
  have metadataF := LoopTransactionMemory.caller metadataE frameF
  obtain ⟨g,gn,rg,_,third,thirdReady,gpc,failedG,_,g24,_,frameG,g23,g26⟩ := LoopRelayChain.step2 secondReady fpc failedF param nonempty route
  have metadataG := LoopTransactionMemory.caller metadataF frameG
  obtain ⟨k,kn,rk,_,fourth,fourthReady,kpc,failedK,_,k24,_,frameK,k23,k26⟩ := LoopRelayChain.step3 thirdReady gpc failedG param nonempty route
  have metadataK := LoopTransactionMemory.caller metadataG frameK
  have pointer : k.get 24=0x80fffa2c#32 := k24.trans (g24.trans (f24.trans (e24.trans routerReady.firstSlot)))
  obtain ⟨origin,before,m,rm,mn,_,fifth,captured,frameM,m23,m26⟩ := LoopRelayChain.enter fourthReady kpc failedK param nonempty noSlash route pointer
  have metadataM := LoopTransactionMemory.caller metadataK frameM
  obtain ⟨j,setup,ready,masked,setupFrame,j19,j23,j26⟩ := LoopRelayWriteInput.contract captured method
  have metadataJ := LoopTransactionMemory.caller metadataM setupFrame
  obtain ⟨last,d,after,sent,loop⟩ := LoopApiWriteCaller.next ready metadataJ
    (j19.trans ((captured.regs 19 (by decide)).trans captured.live.stable.uart))
    (j23.trans (m23.trans (k23.trans (g23.trans (f23.trans (e23.trans routerReady.future))))))
    (j26.trans (m26.trans (k26.trans (g26.trans (f26.trans (e26.trans routerReady.three)))))) masked (hs close) bs (hhs close) hbs
  refine ⟨cn+83+156+fn+gn+kn+mn+26+last,d,after,close,?_,closeReady.spec,loop⟩
  have run := (((((((closed.trans router).trans first).trans second).trans third).trans fourth).trans fifth).trans setup).observed.trans sent
  simpa only [List.nil_append,Nat.add_assoc] using run
end E5R.Thermostat.LoopRelayTransaction
