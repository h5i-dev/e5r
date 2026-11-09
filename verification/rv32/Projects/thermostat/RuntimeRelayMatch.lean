import Projects.thermostat.RuntimeLiteralInput
import Projects.thermostat.RouteRelay
import Projects.thermostat.RomSpan
import Projects.thermostat.FrameOffsets
set_option autoImplicit false
namespace E5R.Thermostat.RuntimeRelayMatch
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board
abbrev sp := RuntimeRouteEnvelope.sp
abbrev rx := RuntimeRouteEnvelope.rx

def memory (ram : Word → BitVec 8) (c : Core) (input : List (BitVec 8)) (head : Head) :=
  RouteRelayBody.memory (MainPathStateSave.memory ram c) 0x80fff9d0#32 (RuntimeRequestSpans.path input head)

/-- Actual last matcher at the received Request layout. Params may be written
    even on failure, so only the proved regions around that slot are exported. -/
theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head}
    {amount rawUsed served : Nat} {lowValue : Word} {close : Bool}
    (h : RuntimeLiteralInput.At c ram input s head amount rawUsed served lowValue close 0x80005b9c#32 10#32 0x80001856#32)
    (leading : ∃ ys,RuntimeRequestSpans.path input head=47#8::ys) :
    ∃ n d,n≤15*(RuntimeRequestSpans.path input head).length+239 ∧
      Quiet.Steps B img n ⟨c,ram⟩ ⟨d,memory ram c input head⟩ ∧ d.pc=0x80001856#32 ∧
      d.get 10=(if RouteSpec.relayPath (RuntimeRequestSpans.path input head) then 1#32 else 0#32) ∧
      d.get 11=RouteRelayBody.count (RuntimeRequestSpans.path input head) ∧
      (∀ r : Reg,r∈[1,2,3,4,5,6,7,8,9,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] → d.get r=c.get r) ∧ d.sameCsr c ∧
      ViewFrame.Region ram (memory ram c input head) sp 3648 ∧
      ViewFrame.Region ram (memory ram c input head) (sp+3656#32) 1576 ∧
      MainTransactionStable.At d (memory ram c input head) input s := by
  obtain ⟨ys,pathEq⟩ := leading
  obtain ⟨pathBytes,length,separate⟩ := RuntimeLiteralInput.literal_view h.live (47#8::ys) pathEq
  have stack : Memory.Block B 0x80ffeb50#32 64 := by
    have block := Memory.sub_block h.live.stable.stack (off := 60240) (m := 64) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60240#32=0x80ffeb50#32 by decide +kernel] using block
  have paramsBlock : Memory.Block B 0x80fff9d0#32 8 := by
    have block := Memory.sub_block h.live.stable.stack (off := 63952) (m := 8) (by decide) (by decide)
    exact block
  have paramsSeparate : WordRegions.Disjoint 0x80fff9d0#32 8 0x80ffeb30#32 96 :=
    WordRegions.symm (WordZero.separated 0x80ffeb30#32 0x80fff9d0#32 96 8 (by decide +kernel) (by decide +kernel))
  have size : c.get 13=BitVec.ofNat 32 (47#8::ys).length := by
    rw [h.pathLength];change BitVec.ofNat 32 (MainQuerySpec.pathLength (MainQuerySpec.bytes input) head.target.1 head.target.2)=_;rw [length]
  have pathBound : (47#8::ys).length≤2048 := by
    have limits := MainQuerySpec.bounds (MainQuerySpec.bytes input) head.target.1 head.target.2 (by have := h.live.stored.bounds.target.2.1;omega)
    have endBound := h.live.stored.bounds.target.2.2
    change MainQuerySpec.position (MainQuerySpec.bytes input) head.target.1 head.target.2-head.target.1=(47#8::ys).length at length
    omega
  have pattern : ReadBytes.Span B img ram 0x80005b9c#32 (WireSpec.ascii "/relay/{i}") := by
    apply ReadBytes.of_data <;> decide +kernel
  obtain ⟨n,d,bound,trace,pc,result,captures,abi,csr⟩ := RouteRelay.contract B c ram (rx+BitVec.ofNat 32 head.target.1) 0x80fff9d0#32 0x80001856#32 ys
    pattern pathBytes pathBound separate paramsSeparate paramsBlock (by decide)
    h.pc h.live.stable.sp h.ret (by decide) (by decide) h.pattern h.patternLength h.path size h.params stack
  let saved := MainPathStateSave.memory ram c
  let after := memory ram c input head
  have captureRegion (off len : Nat) (bounds : off+len≤5232) (apart : off+len≤3648 ∨ 3656≤off) :
      ViewFrame.Region saved after (sp+BitVec.ofNat 32 off) len := by
    have disjoint : WordRegions.Disjoint (sp+BitVec.ofNat 32 off) len 0x80fff9d0#32 8 := by
      intro i j
      have ne := FrameOffsets.ne sp off 3648 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;omega) (by have := i.isLt;have := j.isLt;omega)
      simpa only [show sp+BitVec.ofNat 32 3648=0x80fff9d0#32 by decide +kernel] using ne
    dsimp only [after,memory]
    unfold RouteRelayBody.memory RelayCaptureTail.memory
    split
    · split
      · intro i;rfl
      · exact MainRelayCapture.region saved _ _ _ _ disjoint
    · intro i;rfl
  have saveRegion (off len : Nat) (bounds : off+len≤5232) : ViewFrame.Region ram saved (sp+BitVec.ofNat 32 off) len := by
    intro i
    dsimp only [saved]
    rw [MainPathStateSave.memory_eq]
    apply OuterSave.frame
    intro j
    have ne := FrameOffsets.ne 0x80ffeb30#32 (96+off) 0 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;omega) (by have := j.isLt;omega)
    simpa only [BitVec.ofNat_add,←BitVec.add_assoc,show 0x80ffeb30#32+96#32=sp by decide +kernel,BitVec.add_zero] using ne
  have region (off len : Nat) (bounds : off+len≤5232) (apart : off+len≤3648 ∨ 3656≤off) : ViewFrame.Region ram after (sp+BitVec.ofNat 32 off) len :=
    fun i => (captureRegion off len bounds apart i).trans (saveRegion off len bounds i)
  have future : ViewFrame.Region ram after 0x80fff814#32 96 := by
    simpa only [show sp+3204#32=0x80fff814#32 by decide +kernel] using region 3204 96 (by decide) (Or.inl (by decide))
  have stable : MainTransactionStable.At d after input s := by
    refine ⟨(abi 2 (by decide)).trans h.live.stable.sp,(abi 8 (by decide)).trans h.live.stable.fp,
      (abi 19 (by decide)).trans h.live.stable.uart,(abi 22 (by decide)).trans h.live.stable.one,h.live.stable.bound,
      (ViewFrame.word future 84 (by decide)).trans h.live.stable.filled,?_,?_,h.live.stable.invariant,h.live.stable.stack,?_⟩
    · intro i
      have byte := region 132 2048 (by decide) (Or.inl (by decide)) ⟨i.val,by have := i.isLt;have := h.live.stable.bound;omega⟩
      have atByte : after (rx+BitVec.ofNat 32 i.val)=ram (rx+BitVec.ofNat 32 i.val) := by simpa only [show sp+132#32=rx by decide +kernel] using byte
      exact atByte.trans (h.live.stable.bytes i)
    · apply AppState.preserve ram after s h.live.stable.app
      simpa only [ViewFrame.Region,show sp+44#32=0x80ffebbc#32 by decide +kernel] using region 44 25 (by decide) (Or.inl (by decide))
    · exact (congrArg Prod.fst csr).trans h.live.stable.masked
  refine ⟨n,d,?_,?_,pc,?_,?_,abi,csr,?_,region 3656 1576 (by decide) (Or.inr (by decide)),stable⟩
  · rw [pathEq,List.length_cons];omega
  · simpa only [memory,pathEq] using trace
  · simpa only [pathEq] using result
  · simpa only [pathEq] using captures
  · simpa only [BitVec.add_zero] using region 0 3648 (by decide) (Or.inl (by decide))
end E5R.Thermostat.RuntimeRelayMatch
