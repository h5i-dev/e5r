import Projects.thermostat.RuntimeMethod
import Projects.thermostat.RequestPayloadReady
set_option autoImplicit false
namespace E5R.Thermostat.RuntimeRequestBuild
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board

/-- All common successful Next, counter, target/query/method and Request
    instructions. Empty/Chunked keep their original Head framing and distinct
    raw-consumed versus decoded-body extents throughout this composition. -/
theorem contract {c ram input s head amount rawUsed served lowValue}
    (h : RuntimeNext.Entry c ram input s head amount rawUsed served lowValue) :
    ∃ n d after, n≤755+17+(5*(head.target.2-head.target.1)+12)+34+460 ∧
      Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      RuntimeRequest.Ready d after input s head amount rawUsed (served+1) ∧ d.sameCsr c ∧ ViewFrame.Region ram after RuntimeNext.sp 132 ∧ ViewFrame.Region ram after (RuntimeNext.sp+3204#32) 84 := by
  obtain ⟨a,stage,staged,ca⟩ := RuntimeNext.contract h
  obtain ⟨b,target,targetReady,cb⟩ := RuntimeTarget.contract staged
  obtain ⟨qn,e,qBound,query,queryReady,ce⟩ := RuntimeQuery.contract targetReady
  obtain ⟨mn,f,mBound,method,ready,cf⟩ := RuntimeMethod.contract queryReady
  have entry : RequestPayloadReady.Entry f (MainRequestCounter.memory (RejectNextCore.memory ram RuntimeNext.sp) RuntimeNext.sp (BitVec.ofNat 32 served) (BitVec.ofNat 32 rawUsed)) input s head amount rawUsed (served+1) lowValue := by
    exact ⟨ready.pc,ready.stable,ready.future,ready.three,ready.serve,ready.countBound,ready.positive,ready.countReg,
      ready.method,ready.targetPtr,ready.pathLength,ready.queryPtr,ready.queryLength,ready.tag,ready.zeroHigh,ready.low,
      ready.start,ready.endReg,ready.used,ready.rxReg,ready.methodStartReg,ready.methodEndReg,ready.targetStartReg,
      ready.targetEndReg,ready.minor,ready.usedWord,ready.array,ready.bounds,ready.bodyBound,⟨ready.usedBound,ready.available⟩,
      ready.kind,ready.contained⟩
  obtain ⟨d,build,request,cd⟩ := RequestPayloadReady.contract entry
  refine ⟨755+17+qn+mn+460,d,_,by omega,(((stage.trans target).trans query).trans method).trans build,
    request,(((cd.trans cf).trans ce).trans cb).trans ca,?_,?_⟩
  · let mid := MainRequestCounter.memory (RejectNextCore.memory ram RuntimeNext.sp) RuntimeNext.sp (BitVec.ofNat 32 served) (BitVec.ofNat 32 rawUsed)
    have firstFrame : ViewFrame.Region ram (RejectNextCore.memory ram RuntimeNext.sp) RuntimeNext.sp 132 := by
      simpa only [BitVec.add_zero] using NextFramingMemory.frame ram RuntimeNext.sp 0 132 (by decide)
    have middleFrame : ViewFrame.Region (RejectNextCore.memory ram RuntimeNext.sp) mid RuntimeNext.sp 132 := by
      simpa only [BitVec.add_zero] using MainRequestCounterMemory.frame _ RuntimeNext.sp (BitVec.ofNat 32 served) (BitVec.ofNat 32 rawUsed) 0 132 (by decide) (Or.inl (by decide))
    apply HeadRegionFrame.trans (HeadRegionFrame.trans firstFrame middleFrame)
    simpa only [RequestPayloadFields.memory,RuntimeRequest.sp,RuntimeRequest.rx,BitVec.add_zero] using RequestPayloadMemory.frame mid RuntimeNext.sp RuntimeRequest.rx head.len (head.len+amount) rawUsed
      (MainRequestBuild.method input head) (RuntimeRequest.rx+BitVec.ofNat 32 head.target.1) (MainRequestBuild.pathLength input head)
      (MainRequestBuild.queryPtr input head) (MainRequestBuild.queryLength input head) (HeadCompletedView.framingTag head.framing) 0#32 lowValue
      (BitVec.ofNat 32 head.method.1) (BitVec.ofNat 32 head.method.2) (BitVec.ofNat 32 head.target.1) (BitVec.ofNat 32 head.target.2)
      (BitVec.ofNat 32 head.minor) 0 132 (by decide) (Or.inl (by decide))
  · let mid := MainRequestCounter.memory (RejectNextCore.memory ram RuntimeNext.sp) RuntimeNext.sp (BitVec.ofNat 32 served) (BitVec.ofNat 32 rawUsed)
    have firstFrame : ViewFrame.Region ram (RejectNextCore.memory ram RuntimeNext.sp) (RuntimeNext.sp+3204#32) 84 := by
      simpa only [BitVec.add_zero] using NextFramingMemory.frame ram RuntimeNext.sp 3204 84 (by decide)
    have middleFrame : ViewFrame.Region (RejectNextCore.memory ram RuntimeNext.sp) mid (RuntimeNext.sp+3204#32) 84 := by
      simpa only [BitVec.add_zero] using MainRequestCounterMemory.frame _ RuntimeNext.sp (BitVec.ofNat 32 served) (BitVec.ofNat 32 rawUsed) 3204 84 (by decide) (Or.inl (by decide))
    apply HeadRegionFrame.trans (HeadRegionFrame.trans firstFrame middleFrame)
    simpa only [RequestPayloadFields.memory,RuntimeRequest.sp,RuntimeRequest.rx,BitVec.add_zero] using RequestPayloadMemory.frame mid RuntimeNext.sp RuntimeRequest.rx head.len (head.len+amount) rawUsed
      (MainRequestBuild.method input head) (RuntimeRequest.rx+BitVec.ofNat 32 head.target.1) (MainRequestBuild.pathLength input head)
      (MainRequestBuild.queryPtr input head) (MainRequestBuild.queryLength input head) (HeadCompletedView.framingTag head.framing) 0#32 lowValue
      (BitVec.ofNat 32 head.method.1) (BitVec.ofNat 32 head.method.2) (BitVec.ofNat 32 head.target.1) (BitVec.ofNat 32 head.target.2)
      (BitVec.ofNat 32 head.minor) 3204 84 (by decide) (Or.inl (by decide))
end E5R.Thermostat.RuntimeRequestBuild
