import Projects.thermostat.RuntimeFirstMatch
import Projects.thermostat.StackBoard
import Projects.thermostat.StackRuntimePathView
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.StackRuntimeFirstMatch
open E5R E5R.Thermostat HttpRequestSpec RuntimeFirstMatch
abbrev B := StackBoard.board
theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head}
    {amount rawUsed served : Nat} {lowValue : Word} {close : Bool}
    (h : RuntimeRouterEntry.At c ram input s head amount rawUsed served lowValue close)
    (leading : ∃ ys,RuntimeRequestSpans.path input head=47#8::ys) :
    ∃ n d, n≤10*(RuntimeRequestSpans.path input head).length+157 ∧
      Quiet.Steps B img n ⟨c,ram⟩ ⟨d,MainPathStateSave.memory ram c⟩ ∧ d.pc=0x800013d2#32 ∧
      d.get 10=(if RuntimeRequestSpans.path input head=WireSpec.ascii "/state" then 1#32 else 0#32) ∧ d.get 11=0#32 ∧
      (∀ r : Reg,r∈[1, 2, 3, 4, 5, 6, 7, 8, 9, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31] → d.get r=c.get r) ∧ d.sameCsr c ∧
      ViewFrame.Region ram (MainPathStateSave.memory ram c) sp 5232 ∧
      RuntimeRouteEnvelope.At d (MainPathStateSave.memory ram c) input s head amount rawUsed served lowValue close := by
  obtain ⟨ys,pathEq⟩ := leading
  obtain ⟨pathBytes,length,separate⟩ := StackRuntimePathView.literal_view h (47#8::ys) pathEq
  have stack : Memory.Block B 0x80ffeb50#32 64 := by
    have block := Memory.sub_block StackBoard.available (off := 60240) (m := 64) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60240#32=0x80ffeb50#32 by decide +kernel] using block
  have pattern : ReadBytes.Span B img ram 0x80005b83#32 (WireSpec.ascii "/state") :=
    ReadBytes.of_data B ram _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have size : c.get 13=BitVec.ofNat 32 (47#8::ys).length := by rw [h.pathLength];change BitVec.ofNat 32 (MainQuerySpec.pathLength (MainQuerySpec.bytes input) head.target.1 head.target.2)=_;rw [length]
  have pathBound : (47#8::ys).length≤2048 := by
    have limits := MainQuerySpec.bounds (MainQuerySpec.bytes input) head.target.1 head.target.2 (by have := h.stored.bounds.target.2.1;omega)
    have endBound := h.stored.bounds.target.2.2
    change MainQuerySpec.position (MainQuerySpec.bytes input) head.target.1 head.target.2-head.target.1=(47#8::ys).length at length
    omega
  obtain ⟨n,d,bound,trace,pc,result,captures,abi,csr⟩ := RouteLiteral.contract B c ram 0x80005b83#32
    (rx+BitVec.ofNat 32 head.target.1) 0x80fff9d0#32 0x800013d2#32 115#8 (WireSpec.ascii "tate") ys pattern pathBytes
    (by decide) (by decide) (by decide) pathBound (by unfold WordRegions.Disjoint;decide +kernel) separate
    h.pc h.stable.sp h.ret (by decide) (by decide) h.pattern h.patternLength h.path size h.params stack
  have flag : (RuntimeRequestSpans.path input head=WireSpec.ascii "/state") ↔ 115#8::WireSpec.ascii "tate"=ys := by
    rw [pathEq];change (47#8::ys=47#8::115#8::WireSpec.ascii "tate") ↔ _
    simp only [List.cons.injEq,true_and];exact eq_comm
  refine ⟨n,d,?_,trace,pc,?_,captures,abi,csr,?_,?_⟩
  · rw [pathEq,List.length_cons]
    have fixed : (115#8::WireSpec.ascii "tate").length=5 := by decide
    rw [fixed] at bound;omega
  · simpa only [flag] using result
  · intro i
    rw [MainPathStateSave.memory_eq]
    apply OuterSave.frame
    intro j
    have ne := FrameOffsets.ne 0x80ffeb30#32 96 0 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;omega) (by have := j.isLt;omega)
    simpa only [BitVec.ofNat_add,←BitVec.add_assoc,show 0x80ffeb30#32+96#32=sp by decide +kernel,BitVec.add_zero] using ne
  · apply RuntimeRouteEnvelope.saved (RuntimeRouteEnvelope.fromEntry h) c (csr := csr)
    intro r belongs
    apply abi r
    have subset : ∀ r : Reg,r∈[2,8,18,19,22,23,24,25,26,27] → r∈[1,2,3,4,5,6,7,8,9,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] := by decide
    exact subset r belongs
end E5R.Thermostat.StackRuntimeFirstMatch
