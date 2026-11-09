import Projects.thermostat.HeadReceiveEntry
import Projects.thermostat.EmptyNextReady
import Projects.thermostat.RuntimeRequestBuild
import Projects.thermostat.RuntimeRequestSpans
import Projects.thermostat.LoopTransactionMemory
set_option autoImplicit false
namespace E5R.Thermostat.EmptyReceivedRequest
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board

/-- Actual one-byte UART reception and Empty framing through both Next
    stages, counter, URI/method decode and Request construction. No body,
    framing payload or completed caller layout is an external premise. -/
theorem contract {c ram s served} (h : LoopReady.At c ram s served)
    (wire : Nat → BitVec 8) (fuel : Nat) (head : Head) (plan : MainHeaderStreamPlan.Plan)
    (space : fuel≤2048) (valid : MainHeaderStreamPlan.Valid plan wire 0 fuel)
    (accepted : (MainHeaderStreamSpec.consume wire fuel []).result=.done head) (kind : head.framing=.empty) :
    ∃ n d after, Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩
      (MainHeaderStreamPlan.logs plan 0 (MainHeaderStreamSpec.consume wire fuel []).received) [] ∧
      RuntimeRequest.Ready d after (MainHeaderStreamSpec.consume wire fuel []).input s head 0 head.len (served+1) ∧
      (MainHeaderStreamSpec.consume wire fuel []).input.length=head.len ∧
      RuntimeRequestSpans.body (MainHeaderStreamSpec.consume wire fuel []).input head 0=[] ∧ d.sameCsr c ∧ InitRoutes.Layout after ∧ LoopTransactionMemory.At after (BitVec.ofNat 32 head.len) := by
  obtain ⟨hn,a,ra,receive,bodyReady,exactHead,bank,serve,static,original,headBounds,ca⟩ :=
    HeadReceiveEntry.contract h wire fuel head plan space valid accepted
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
  obtain ⟨e,next,entry,ce,routeFrame,capacityFrame,nextFuture⟩ := EmptyNextReady.contract bodyReady original exactHead bank serve kind h.room bounds
    ⟨headBounds.target.2.2,headBounds.fields⟩
  obtain ⟨rn,d,after,_,request,ready,cd,requestFrame,requestFuture⟩ := RuntimeRequestBuild.contract entry
  have staticNext := InitRoutes.layout_preserve ra (EmptyNextReady.memory ra head) static
    (by simpa only [ViewFrame.Region,show EmptyNextReady.sp+72#32=0x80ffebd8#32 by decide +kernel] using routeFrame)
    (by simpa only [ViewFrame.Region,show EmptyNextReady.sp+16#32=0x80ffeba0#32 by decide +kernel] using capacityFrame)
  have staticFinal : InitRoutes.Layout after := InitRoutes.layout_preserve _ after staticNext
    (by simpa only [ViewFrame.Region,show RuntimeNext.sp+72#32=0x80ffebd8#32 by decide +kernel] using HeadRegionFrame.sub requestFrame 72 60 (by decide))
    (by simpa only [ViewFrame.Region,show RuntimeNext.sp+16#32=0x80ffeba0#32 by decide +kernel] using HeadRegionFrame.sub requestFrame 16 4 (by decide))
  have limitsFrame := HeadRegionFrame.trans nextFuture requestFuture
  have metadata : LoopTransactionMemory.At after (BitVec.ofNat 32 head.len) := by
    refine ⟨(ViewFrame.word limitsFrame 76 (by decide)).trans bodyReady.stable.layout.head.headLimit,
      (ViewFrame.word limitsFrame 80 (by decide)).trans bodyReady.stable.layout.head.bodyLimit,?_,ready.usedWord,?_,staticFinal.2,staticFinal.1⟩
    · simpa only [exactHead] using ready.stable.filled
    · rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := ready.stable.bound;rw [exactHead] at this;omega)]
      have bound := ready.stable.bound
      rw [exactHead] at bound
      exact bound
  exact ⟨hn+409+rn,d,after,by simpa only [List.append_nil] using (receive.trans next.observed).trans request.observed,
    ready,exactHead,by simp only [RuntimeRequestSpans.body,List.take_zero],(cd.trans ce).trans ca,staticFinal,metadata⟩
end E5R.Thermostat.EmptyReceivedRequest
