import Projects.thermostat.RuntimeReadInput
import Projects.thermostat.StackRuntimeReadViews
set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.StackRuntimeReadInput
open E5R E5R.Thermostat HttpRequestSpec RuntimeReadInput
abbrev B := StackBoard.board
theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount rawUsed served : Nat} {lowValue : Word} {close : Bool}
    (h : RuntimeRouteEnvelope.At c ram input s head amount rawUsed served lowValue close)
    (pc : c.pc=0x800013d2#32) (matched : c.get 10=1#32) (captures : c.get 11=0#32)
    (route : MainRequestSpans.path input head=WireSpec.ascii "/state")
    (method : MainMethodSpec.decode (MainMethodBytes.token input head.method.2)=.get)
    (replyCapacity : ramRead ram 0x80fff9fc#32 .w=832#32) :
    ∃ d, Quiet.Steps B img 28 ⟨c,ram⟩ ⟨d,MainStateRouteSetup.memory ram⟩ ∧
      StackRuntimeReadViews.RouteReady d (MainStateRouteSetup.memory ram) input s head amount served close false ∧ d.sameCsr c ∧
      ViewFrame.Region ram (MainStateRouteSetup.memory ram) sp 3304 ∧ d.get 23=c.get 23 ∧ d.get 26=c.get 26 := by
  have stack : Memory.Block B sp 5232 := by
    have block := Memory.sub_block StackBoard.available (off := 60304) (m := 5232) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60304#32=sp by decide +kernel] using block
  have fields (i : Fin 5) : ramRead ram (fp+BitVec.ofNat 32 (688+4*i.val)) .w=
      (match i.val with | 0 => 0x80ffebf8#32 | 1 => 0x80fff880#32 | 2 => 0x80ffebbc#32 | 3 => 0x80fff4d4#32 | _ => 832#32) := by
    have choices : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 ∨ i.val=4 := by have := i.isLt;omega
    rcases i with ⟨i,small⟩
    rcases choices with h0|h1|h2|h3|h4
    · change i=0 at h0;subst i;exact h.futures ⟨4,by decide⟩ ⟨0,by decide⟩
    · change i=1 at h1;subst i;exact h.futures ⟨4,by decide⟩ ⟨1,by decide⟩
    · change i=2 at h2;subst i;exact h.futures ⟨4,by decide⟩ ⟨2,by decide⟩
    · change i=3 at h3;subst i;exact h.futures ⟨4,by decide⟩ ⟨3,by decide⟩
    · change i=4 at h4;subst i;exact h.futures ⟨4,by decide⟩ ⟨4,by decide⟩
  have methodByte : ram 0x80fff9f4#32=0#8 := by
    have byte := h.stored.methodByte
    rw [method] at byte
    exact byte
  have getRoute : ram 0x80ffec00#32=0#8 := by
    have byte := (h.table ⟨0,by decide⟩).2.2
    exact byte
  obtain ⟨d,steps,pd,d13,d10,d12,d20,d11,d9,d24,d1,keep,csr⟩ := MainStateRouteSetup.contract B c ram
    h.stable.fp matched captures h.stable.one stack (by have value := fields ⟨0,by decide⟩; change ramRead ram (fp+688#32) .w=2164255736#32 at value; simpa only [show fp+688#32=2164259524#32 by decide +kernel] using value) (by have value := fields ⟨1,by decide⟩; change ramRead ram (fp+692#32) .w=2164258944#32 at value; simpa only [show fp+692#32=2164259528#32 by decide +kernel] using value)
    (by have value := fields ⟨2,by decide⟩; change ramRead ram (fp+696#32) .w=2164255676#32 at value; simpa only [show fp+696#32=2164259532#32 by decide +kernel] using value) (by have value := fields ⟨3,by decide⟩; change ramRead ram (fp+700#32) .w=2164258004#32 at value; simpa only [show fp+700#32=2164259536#32 by decide +kernel] using value) (by have value := fields ⟨4,by decide⟩; change ramRead ram (fp+704#32) .w=832#32 at value; simpa only [show fp+704#32=2164259540#32 by decide +kernel] using value) methodByte getRoute pc
  let after := MainStateRouteSetup.memory ram
  have frame := MainStateRouteSetup.frame ram
  have liveFuture : ViewFrame.Region ram after fp 96 := by
    simpa only [show sp+3204#32=fp by decide +kernel] using frame 3204 96 (by decide) (Or.inl (by decide))
  have stable : MainTransactionStable.At d after input s := by
    refine ⟨(keep 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.stable.sp,
      (keep 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.stable.fp,
      (keep 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.stable.uart,
      (keep 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.stable.one,
      h.stable.bound,(ViewFrame.word liveFuture 84 (by decide)).trans h.stable.filled,?_,?_,h.stable.invariant,h.stable.stack,?_⟩
    · intro i
      have byte := frame 132 2048 (by decide) (Or.inl (by decide)) ⟨i.val,by have := i.isLt;have := h.stable.bound;omega⟩
      have atByte : after (rx+BitVec.ofNat 32 i.val)=ram (rx+BitVec.ofNat 32 i.val) := by simpa only [show sp+132#32=rx by decide +kernel] using byte
      exact atByte.trans (h.stable.bytes i)
    · apply AppState.preserve ram after s h.stable.app
      simpa only [ViewFrame.Region,show sp+44#32=0x80ffebbc#32 by decide +kernel] using frame 44 25 (by decide) (Or.inl (by decide))
    · exact (congrArg Prod.fst csr).trans h.stable.masked
  have whole : Bytes.Span B after rx input := by
    have block := Memory.sub_block StackBoard.available (off := 60436) (m := input.length)
      (by have available := Nat.le_trans h.stored.usedBound.1 h.stored.usedBound.2;have := h.stored.bounds.length.1;omega) (by have := stable.bound;omega)
    have rxblock : Memory.Block B rx input.length := by
      simpa only [show 0x80ff0000#32+60436#32=rx by decide +kernel] using block
    exact Bytes.of_block B after rx input rxblock (by have := stable.bound;omega) stable.bytes
  have limits : head.target.1≤MainQuerySpec.position (MainQuerySpec.bytes input) head.target.1 head.target.2 ∧
      MainQuerySpec.position (MainQuerySpec.bytes input) head.target.1 head.target.2≤input.length := by
    have bounds := MainQuerySpec.bounds (MainQuerySpec.bytes input) head.target.1 head.target.2 (by have := h.stored.bounds.target.2.1;omega)
    have := h.stored.contained.1
    have available := Nat.le_trans h.stored.usedBound.1 h.stored.usedBound.2
    omega
  have pathBytes : Bytes.Span B after (rx+BitVec.ofNat 32 head.target.1) (WireSpec.ascii "/state") := by
    have span := Bytes.subspan whole _ _ limits
    change Bytes.Span B after (rx+BitVec.ofNat 32 head.target.1) (MainRequestSpans.path input head) at span
    rw [route] at span
    exact span
  have pathLength : MainQuerySpec.pathLength (MainQuerySpec.bytes input) head.target.1 head.target.2=6 := by
    have size := Bytes.subspan_length input _ _ limits
    change (MainRequestSpans.path input head).length=MainQuerySpec.pathLength (MainQuerySpec.bytes input) head.target.1 head.target.2 at size
    rw [route] at size
    exact size.symm
  have bodyBytes : Bytes.Span B after (rx+BitVec.ofNat 32 head.len) (MainRequestSpans.body input head amount) := by
    have span := Bytes.subspan whole head.len (head.len+amount) ⟨by omega,(Nat.le_trans h.stored.usedBound.1 h.stored.usedBound.2)⟩
    change Bytes.Span B after (rx+BitVec.ofNat 32 head.len) ((input.drop head.len).take amount)
    simpa only [show head.len+amount-head.len=amount by omega] using span
  have bodyLength : (MainRequestSpans.body input head amount).length=amount := by
    simp only [MainRequestSpans.body,List.length_take,List.length_drop]
    exact Nat.min_eq_left (by have available := Nat.le_trans h.stored.usedBound.1 h.stored.usedBound.2;omega)
  have requestBlock (size : Nat) (positive : 0<size) (bound : size≤376) : Memory.Block B req size := by
    have block := Memory.sub_block StackBoard.available (off := 63616) (m := size) positive (by omega)
    simpa only [show 0x80ff0000#32+63616#32=req by decide +kernel] using block
  have word (off : Nat) (bound : off+4≤3680) : ramRead after (sp+BitVec.ofNat 32 off) .w=ramRead ram (sp+BitVec.ofNat 32 off) .w := by
    have kept := ViewFrame.word (frame off 4 (by omega) (Or.inl bound)) 0 (by decide)
    simpa only [BitVec.add_zero] using kept
  have bodyView : DecodeInput.BodyAt B after req (rx+BitVec.ofNat 32 head.len) (MainRequestSpans.body input head amount) := by
    refine ⟨requestBlock 328 (by decide) (by decide),by decide +kernel,?_,?_,bodyBytes⟩
    · have value := (word 3632 (by decide)).trans h.stored.request.body
      change ramRead after (sp+3632#32) .w=rx+BitVec.ofNat 32 head.len
      exact value.trans (BitVec.add_comm _ _)
    · rw [bodyLength]
      exact (word 3636 (by decide)).trans h.stored.request.bodyLength
  have pathView : PathDispatch.PathAt B after req (rx+BitVec.ofNat 32 head.target.1) (WireSpec.ascii "/state") := by
    refine ⟨requestBlock 312 (by decide) (by decide),by decide +kernel,(word 3616 (by decide)).trans h.stored.request.path,?_,pathBytes⟩
    have value := (word 3620 (by decide)).trans h.stored.request.pathLength
    change ramRead after (sp+3620#32) .w=BitVec.ofNat 32 (MainQuerySpec.pathLength (MainQuerySpec.bytes input) head.target.1 head.target.2) at value
    rw [pathLength] at value
    exact value
  have decoderStack : Memory.Block B decodeSp 16 := by
    have block := Memory.sub_block StackBoard.available (off := 60288) (m := 16) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60288#32=decodeSp by decide +kernel] using block
  have separated : ∀ i : Fin 2048, ∀ j : Fin 16, rx+BitVec.ofNat 32 i.val≠decodeSp+BitVec.ofNat 32 j.val :=
    fun i j => Ne.symm (WordZero.separated decodeSp rx 16 2048 (by decide +kernel) (by decide +kernel) j i)
  have bodySeparate : ∀ i : Fin (MainRequestSpans.body input head amount).length, ∀ j : Fin 16,
      (rx+BitVec.ofNat 32 head.len)+BitVec.ofNat 32 i.val≠decodeSp+BitVec.ofNat 32 j.val := by
    intro i j
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    exact separated ⟨head.len+i.val,by have small : i.val<amount := (by simpa only [bodyLength] using i.isLt);have available := Nat.le_trans h.stored.usedBound.1 h.stored.usedBound.2;have := stable.bound;omega⟩ j
  have pathSeparate : ∀ i : Fin (WireSpec.ascii "/state").length, ∀ j : Fin 16,
      (rx+BitVec.ofNat 32 head.target.1)+BitVec.ofNat 32 i.val≠decodeSp+BitVec.ofNat 32 j.val := by
    intro i j
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    exact separated ⟨head.target.1+i.val,by have := i.isLt;change i.val<6 at this;have := limits.2;have := stable.bound;change MainQuerySpec.position (MainQuerySpec.bytes input) head.target.1 head.target.2-head.target.1=6 at pathLength;omega⟩ j
  have params : WireInput.Params B after req (rx+BitVec.ofNat 32 head.target.1) (WireSpec.ascii "/state") none :=
    .missing (requestBlock 372 (by decide) (by decide)) (by decide +kernel) (MainStateRouteSetup.params_count ram)
  have wire : Wire.Pre B d after decodeSp req (rx+BitVec.ofNat 32 head.target.1) (rx+BitVec.ofNat 32 head.len)
      (WireSpec.ascii "/state") (MainRequestSpans.body input head amount) none :=
    ⟨pd,stable.sp,d10,decoderStack,by decide +kernel,bodyView,pathView,params,
      fun i j => Ne.symm (WordZero.separated decodeSp req 16 372 (by decide +kernel) (by decide +kernel) j i),bodySeparate,pathSeparate⟩
  have flag : after (sp+3304#32)=Encoding.boolByte close := by
    have kept := frame 3304 1 (by decide) (Or.inl (by decide)) ⟨0,by decide⟩
    simpa only [BitVec.add_zero] using kept.trans h.closeByte
  have cap : ramRead after 0x80fff9fc#32 .w=832#32 := by
    have kept := ViewFrame.word (frame 3692 4 (by decide) (Or.inr (Or.inl ⟨by decide,by decide⟩))) 0 (by decide)
    simpa only [BitVec.add_zero,show sp+3692#32=0x80fff9fc#32 by decide +kernel] using kept.trans replyCapacity
  have methodAfter : after 0x80fff9f4#32=0#8 := by
    have kept := frame 3684 1 (by decide) (Or.inr (Or.inl ⟨by decide,by decide⟩)) ⟨0,by decide⟩
    simpa only [BitVec.add_zero,show sp+3684#32=0x80fff9f4#32 by decide +kernel] using kept.trans methodByte
  exact ⟨d,steps,⟨wire,stable,MainServeLayout.preserve (MainServeMemoryFrames.whole liveFuture (by decide)) h.serve,flag,d1,d9,d20,d24,cap,methodAfter,MainStateRouteSetup.actor ram⟩,csr,by simpa only [BitVec.add_zero] using frame 0 3304 (by decide) (Or.inl (by decide)),by apply keep;all_goals decide,by apply keep;all_goals decide⟩
end E5R.Thermostat.StackRuntimeReadInput
