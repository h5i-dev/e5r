import Projects.thermostat.HeadReceiveEntry
import Projects.thermostat.ChunkNextReady
import Projects.thermostat.RuntimeRequestBuild
import Projects.thermostat.RuntimeRequestSpans
import Projects.thermostat.LoopTransactionMemory
set_option autoImplicit false
set_option maxRecDepth 4000
namespace E5R.Thermostat.ChunkReceivedRequest
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board
abbrev sp := 0x80ffeb90#32
abbrev rx := 0x80ffec14#32

theorem header_bytes {c ram input s head result served}
    (h : ChunkSuccessBody.Ready c ram input s head result served) (exactHead : input.length=head.len) :
    (ChunkSuccessBody.buffer ram result.read).take head.len=input := by
  apply List.ext_getElem
  · simp only [List.length_take,ChunkSuccessBody.buffer,List.length_ofFn]
    have := h.extent.1
    omega
  · intro i hi hj
    rw [List.getElem_take]
    have inside : i<result.read := by have := h.extent.1;omega
    change (List.ofFn (fun j : Fin result.read => ram (rx+BitVec.ofNat 32 j.val)))[i]' (by simpa only [List.length_ofFn] using inside)=input[i]
    rw [List.getElem_ofFn]
    exact h.header ⟨i,hj⟩

theorem body_bytes {c ram input s head result served}
    (h : ChunkSuccessBody.Ready c ram input s head result served) :
    RuntimeRequestSpans.body (ChunkSuccessBody.buffer ram result.read) head result.body.length=result.body := by
  apply List.ext_getElem
  · simp only [RuntimeRequestSpans.body,List.length_take,List.length_drop,ChunkSuccessBody.buffer,List.length_ofFn]
    have := h.extent.1
    omega
  · intro i hi hj
    dsimp only [RuntimeRequestSpans.body] at hi ⊢
    rw [List.getElem_take,List.getElem_drop]
    have inside : head.len+i<result.read := by have := h.extent.1;omega
    change (List.ofFn (fun j : Fin result.read => ram (rx+BitVec.ofNat 32 j.val)))[head.len+i]' (by simpa only [List.length_ofFn] using inside)=result.body[i]
    rw [List.getElem_ofFn]
    have byte := h.body ⟨i,hj⟩
    change ram ((rx+BitVec.ofNat 32 head.len)+BitVec.ofNat 32 i)=result.body[i] at byte
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add,Nat.add_assoc] using byte

/-- Real receive boundary through accepted chunked head, complete dechunking,
    both Next/Request construction stages, URI/method decoding and count store.
    Header/body correspondence is independent of the compacted-buffer ghost.
    Routing/response and arbitrary-prefix safety are subsequent obligations. -/
theorem contract {c ram s served} (h : LoopReady.At c ram s served)
    (wire : Nat → BitVec 8) (fuel arrivals : Nat) (head : Head)
    (headerPlan : MainHeaderStreamPlan.Plan) (bodyPlan : ChunkReceivePlan.Plan)
    (headSpace : fuel≤2048) (headerValid : MainHeaderStreamPlan.Valid headerPlan wire 0 fuel)
    (accepted : (MainHeaderStreamSpec.consume wire fuel []).result=.done head) (kind : head.framing=.chunked)
    (space : head.len+arrivals≤2048) (bodyValid : ChunkReceivePlan.Valid bodyPlan wire head.len arrivals)
    (done : (ChunkBufferSpec.consume wire arrivals head.len head.len cStart []).stop=.done) :
    let r := ChunkBufferSpec.consume wire arrivals head.len head.len cStart []
    ∃ received n d after raw, received≤arrivals ∧ head.len+received=r.read ∧ raw.length=r.read ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩
        (MainHeaderStreamPlan.logs headerPlan 0 (MainHeaderStreamSpec.consume wire fuel []).received++
          ChunkReceivePlan.logs bodyPlan head.len received) [] ∧
      RuntimeRequest.Ready d after raw s head r.body.length r.read (served+1) ∧
      raw.take head.len=(MainHeaderStreamSpec.consume wire fuel []).input ∧
      RuntimeRequestSpans.body raw head r.body.length=r.body ∧ d.sameCsr c ∧ InitRoutes.Layout after ∧ LoopTransactionMemory.At after (BitVec.ofNat 32 r.read) := by
  obtain ⟨hn,a,ra,receive,bodyReady,exactHead,bank,serve,static,_,headBounds,ca⟩ :=
    HeadReceiveEntry.contract h wire fuel head headerPlan headSpace headerValid accepted
  have bounds : MainHeadAcceptedBounds.At 1024 1024 head := by
    have small := Nat.min_le_right (MainHeaderStreamSpec.consume wire fuel []).input.length 1024
    refine ⟨bodyReady.bounds.method,?_,bodyReady.bounds.version,?_,?_,bodyReady.bounds.content⟩
    · have target := bodyReady.bounds.target
      exact ⟨target.1,target.2.1,by omega⟩
    · intro entry member
      have field := bodyReady.bounds.fields entry member
      exact ⟨field.1,field.2.1,field.2.2.1,by have := field.2.2.2;omega⟩
    · have length := bodyReady.bounds.length
      exact ⟨length.1,by omega⟩
  obtain ⟨received,bn,b,rb,recvBound,actualRead,time,chunk,success,cb,bodyFrame,bodyFuture⟩ := ChunkSuccessBody.contract bodyReady kind bank serve exactHead
    wire arrivals bodyPlan (by simpa only [exactHead] using space) (by simpa only [exactHead] using bodyValid) done
  have staticBody : InitRoutes.Layout rb := InitRoutes.layout_preserve ra rb static
    (by simpa only [ViewFrame.Region,show ChunkSuccessBody.sp+72#32=0x80ffebd8#32 by decide +kernel] using HeadRegionFrame.sub bodyFrame 72 60 (by decide))
    (by simpa only [ViewFrame.Region,show ChunkSuccessBody.sp+16#32=0x80ffeba0#32 by decide +kernel] using HeadRegionFrame.sub bodyFrame 16 4 (by decide))
  obtain ⟨e,next,nextReady,ce,routeFrame,capacityFrame,nextFuture⟩ := ChunkNextReady.contract success kind h.room bounds ⟨headBounds.target.2.2,headBounds.fields⟩
  obtain ⟨rn,d,after,_,request,ready,cd,requestFrame,requestFuture⟩ := RuntimeRequestBuild.contract nextReady
  have staticNext := InitRoutes.layout_preserve rb (ChunkNextReady.memory rb head (ChunkBufferSpec.consume wire arrivals head.len head.len cStart []).written) staticBody
    (by simpa only [ViewFrame.Region,show ChunkNextReady.sp+72#32=0x80ffebd8#32 by decide +kernel] using routeFrame)
    (by simpa only [ViewFrame.Region,show ChunkNextReady.sp+16#32=0x80ffeba0#32 by decide +kernel] using capacityFrame)
  have staticFinal : InitRoutes.Layout after := InitRoutes.layout_preserve _ after staticNext
    (by simpa only [ViewFrame.Region,show RuntimeNext.sp+72#32=0x80ffebd8#32 by decide +kernel] using HeadRegionFrame.sub requestFrame 72 60 (by decide))
    (by simpa only [ViewFrame.Region,show RuntimeNext.sp+16#32=0x80ffeba0#32 by decide +kernel] using HeadRegionFrame.sub requestFrame 16 4 (by decide))
  have limitsFrame : ViewFrame.Region ra after (RuntimeNext.sp+3204#32) 84 :=
    HeadRegionFrame.trans (HeadRegionFrame.trans bodyFuture nextFuture) requestFuture
  have rawLength : (ChunkSuccessBody.buffer rb (ChunkBufferSpec.consume wire arrivals head.len head.len cStart []).read).length=(ChunkBufferSpec.consume wire arrivals head.len head.len cStart []).read := List.length_ofFn
  have metadata : LoopTransactionMemory.At after (BitVec.ofNat 32 (ChunkBufferSpec.consume wire arrivals head.len head.len cStart []).read) := by
    refine ⟨(ViewFrame.word limitsFrame 76 (by decide)).trans bodyReady.stable.layout.head.headLimit,
      (ViewFrame.word limitsFrame 80 (by decide)).trans bodyReady.stable.layout.head.bodyLimit,?_,ready.usedWord,?_,staticFinal.2,staticFinal.1⟩
    · simpa only [rawLength] using ready.stable.filled
    · rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := ready.stable.bound;rw [rawLength] at this;omega)]
      have bound := ready.stable.bound
      rw [rawLength] at bound
      exact bound
  refine ⟨received,hn+bn+408+rn,d,after,ChunkSuccessBody.buffer rb _,recvBound,actualRead,?_,?_,ready,
    header_bytes success exactHead,body_bytes success,((cd.trans ce).trans cb).trans ca,staticFinal,metadata⟩
  · exact List.length_ofFn
  · simpa only [exactHead,List.append_nil] using ((receive.trans chunk).trans next.observed).trans request.observed
end E5R.Thermostat.ChunkReceivedRequest
