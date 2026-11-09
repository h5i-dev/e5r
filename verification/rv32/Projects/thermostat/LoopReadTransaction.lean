import Projects.thermostat.LoopCloseRequest
import Projects.thermostat.LoopRouteFrames
import Projects.thermostat.LoopReadRouteInput
import Projects.thermostat.LoopReadDecoded
import Projects.thermostat.LoopReadNext
import Projects.thermostat.MainReadReset
set_option autoImplicit false
namespace E5R.Thermostat.LoopReadTransaction
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board
/-- Actual Request through general close scan, real state matcher, separate
    Read decoding/acquisition, exact reply and reusable next UART boundary. -/
theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot}
    {head : Head} {amount served : Nat} {used : Word}
    (h : MainRequestBuild.Ready c ram input s head amount served) (metadata : LoopTransactionMemory.At ram used)
    (route : MainRequestSpans.path input head=WireSpec.ascii "/state")
    (method : MainMethodSpec.decode (MainMethodBytes.token input head.method.2)=.get)
    (hs : Bool → List UartTxLoop.Slot) (bs : List UartTxLoop.Slot)
    (hhs : ∀ close, (hs close).length=(ResponseHeadSpec.bytes 200 (WireSpec.ascii "application/json") (ReplyJson.snapshot s).length close).length)
    (hbs : bs.length=(ReplyJson.snapshot s).length) :
    ∃ n d after close, Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (UartTxLoop.reads (hs close)++UartTxLoop.reads bs)
      (UartTxLoop.events (ResponseHeadSpec.bytes 200 (WireSpec.ascii "application/json") (ReplyJson.snapshot s).length close)++
        UartTxLoop.events (ReplyJson.snapshot s)) ∧
      close=MainCloseSpec.mustClose head.minor served (MainRequestSpans.raw input head amount) (MainRequestInputs.entries head) ∧
      LoopReady.At d after s (if close then 0 else served) := by
  obtain ⟨cn,a,ra,close,closed,closeReady,metadataA⟩ := LoopCloseRequest.contract h metadata
  obtain ⟨b,router,routerReady,metadataB⟩ := LoopRouteFrames.router closeReady metadataA
  obtain ⟨e,matched,matchReady,_⟩ := MainStateMatch.contract routerReady route
  have metadataE := LoopTransactionMemory.caller metadataB (LoopRouteFrames.saved _ b)
  have replyCapacity : ramRead (MainPathStateSave.memory (MainRouterSetup.memory ra) b) 0x80fff9fc#32 .w=832#32 := by
    have region : ViewFrame.Region (MainRouterSetup.memory ra) (MainPathStateSave.memory (MainRouterSetup.memory ra) b) 0x80fff9fc#32 4 := by
      intro i
      rw [MainPathStateSave.memory_eq]
      exact OuterSave.frame _ 0x80ffeb30#32 b _ (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)) i)
    have word := ViewFrame.word region 0 (by decide)
    simp only [BitVec.add_zero] at word
    exact word.trans (MainReadReset.reply_capacity ra)
  obtain ⟨f,setup,routeReady,_,setupFrame,f23,f26⟩ := LoopReadRouteInput.contract matchReady route method replyCapacity
  have metadataF := LoopTransactionMemory.caller metadataE setupFrame
  obtain ⟨g,gn,rg,_,decoded,readReady,_,decodeFrame,g23,g26⟩ := LoopReadDecoded.contract routeReady
  have metadataG := LoopTransactionMemory.caller metadataF decodeFrame
  have room : close=false → served<100 := by
    intro kept
    by_cases reached : 100≤served
    · have forced := MainCloseSpec.limit head.minor served reached (MainRequestSpans.raw input head amount) (MainRequestInputs.entries head)
      have contradiction := closeReady.spec.trans forced
      rw [kept] at contradiction
      cases contradiction
    · omega
  obtain ⟨last,d,after,sent,ready⟩ := LoopReadNext.contract readReady metadataG
    (g23.trans (f23.trans matchReady.future)) (g26.trans (f26.trans matchReady.three)) room (hs close) bs (hhs close) hbs
  refine ⟨cn+83+187+28+gn+last,d,after,close,?_,closeReady.spec,ready⟩
  have run := ((((closed.trans router).trans matched).trans setup).trans decoded).observed.trans sent
  simpa only [List.nil_append,Nat.add_assoc] using run
end E5R.Thermostat.LoopReadTransaction
