import Projects.thermostat.ChunkPhase
import Projects.thermostat.RequestPhase
import Projects.thermostat.ChunkReceivedRequest
set_option autoImplicit false
namespace E5R.Thermostat.ChunkCompletePhase
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board
abbrev sp := 0x80ffeb90#32
abbrev fp := 0x80fff814#32

/-- Completed reactive decoding supplies the actual successful Next caller.
    The compacted buffer is a RAM representation; original head and decoded
    body correspondence are retained separately. -/
theorem next {c ram s served original head r}
    (context : ChunkPhase.Context c ram s served original head)
    (terminal : MainChunkBuffered.Terminal ram sp head.len r c) (done : r.stop=.done)
    (body : ChunkBufferView.Body ram sp head.len r.body) (writeEq : r.written=head.len+r.body.length)
    (bodyBound : r.body.length≤1024) (extent : head.len+r.body.length≤r.read) (readBound : r.read≤2048)
    (cursor : c.get 24=BitVec.ofNat 32 r.read) (filled : ramRead ram (sp+3288#32) .w=BitVec.ofNat 32 r.read) :
    ReactiveEnvelope.Envelope (fun m ghost => RequestPhase.At m.core m.ram ghost) ⟨c,ram⟩
      (ChunkPhase.classify s served original head r) := by
  obtain ⟨pc,obj,inv,readWord,writeWord,layout,stackPtr,masked,tag⟩ := terminal
  have stable : MainTransactionStable.At c ram (ChunkSuccessBody.buffer ram r.read) s := by
    refine ⟨stackPtr,context.frame,context.uart,context.one,?_,?_,?_,context.app,context.invariant,context.stack,masked⟩
    · simpa only [ChunkSuccessBody.buffer,List.length_ofFn] using readBound
    · simpa only [ChunkSuccessBody.buffer,List.length_ofFn,show sp+3288#32=fp+84#32 by decide +kernel] using filled
    · intro i
      change ram (ChunkSuccessBody.rx+BitVec.ofNat 32 i.val)=(List.ofFn (fun j : Fin r.read => ram (ChunkSuccessBody.rx+BitVec.ofNat 32 j.val)))[i.val]' (by simpa only [ChunkSuccessBody.buffer,List.length_ofFn] using i.isLt)
      rw [List.getElem_ofFn]
  have success : ChunkSuccessBody.Ready c ram original s head r served :=
    ⟨pc,stable,context.caller.bank,context.caller.serve,context.two,
      by simpa only [done] using tag,context.view,context.consumed,cursor,readWord,writeWord,body,context.header,
      writeEq,bodyBound,extent,readBound⟩
  have bounds := MainHeadAcceptedBounds.bytes original head context.parsed
  have headLimit : head.len≤1024 := Nat.le_trans bounds.length.2 (Nat.min_le_right _ _)
  have wide := MainLengthState.widen bounds (Nat.min_le_right _ _)
  have contained := MainHeadContained.bytes original head context.parsed
  obtain ⟨e,next,entry,csrE,routeFrame,capacityFrame,nextFuture⟩ := ChunkNextReady.contract success context.kind context.caller.room wide ⟨contained.1,contained.2⟩
  obtain ⟨rn,d,after,bound,request,ready,csrD,requestFrame,requestFuture⟩ := RuntimeRequestBuild.contract entry
  have staticNext := InitRoutes.layout_preserve ram (ChunkNextReady.memory ram head r.written) context.caller.layout
    (by simpa only [ViewFrame.Region,show sp+72#32=0x80ffebd8#32 by decide +kernel] using routeFrame)
    (by simpa only [ViewFrame.Region,show sp+16#32=0x80ffeba0#32 by decide +kernel] using capacityFrame)
  have staticFinal : InitRoutes.Layout after := InitRoutes.layout_preserve _ after staticNext
    (by simpa only [ViewFrame.Region,show sp+72#32=0x80ffebd8#32 by decide +kernel] using HeadRegionFrame.sub requestFrame 72 60 (by decide))
    (by simpa only [ViewFrame.Region,show sp+16#32=0x80ffeba0#32 by decide +kernel] using HeadRegionFrame.sub requestFrame 16 4 (by decide))
  have limits := HeadRegionFrame.trans nextFuture requestFuture
  have rawLength : (ChunkSuccessBody.buffer ram r.read).length=r.read := List.length_ofFn
  have metadata : LoopTransactionMemory.At after (BitVec.ofNat 32 r.read) := by
    refine ⟨(ViewFrame.word limits 76 (by decide)).trans context.headLimit,
      (ViewFrame.word limits 80 (by decide)).trans context.bodyLimit,?_,ready.usedWord,?_,staticFinal.2,staticFinal.1⟩
    · simpa only [rawLength] using ready.stable.filled
    · rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
      exact readBound
  obtain ⟨nr,last,final,route,post⟩ := RequestPhase.enter ready metadata
    (ChunkReceivedRequest.header_bytes success context.length) (ChunkReceivedRequest.body_bytes success) context.parsed
  refine ⟨masked,408+rn+nr,⟨last,final⟩,(next.trans request).trans route,?_⟩
  simpa only [ChunkPhase.classify,done,ChunkPhase.response] using post
end E5R.Thermostat.ChunkCompletePhase
