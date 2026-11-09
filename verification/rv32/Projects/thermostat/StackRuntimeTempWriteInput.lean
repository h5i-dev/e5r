import Projects.thermostat.RuntimeTempWriteInput
import Projects.thermostat.StackBoard
import Projects.thermostat.StackRuntimeApiWriteCaller
import Projects.thermostat.StackRuntimeLiteralInput
import Projects.thermostat.StackRuntimeRouteInputs
set_option autoImplicit false
set_option maxRecDepth 6000
namespace E5R.Thermostat.StackRuntimeTempWriteInput
open E5R E5R.Thermostat HttpRequestSpec RuntimeTempWriteInput
abbrev B := StackBoard.board
theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount rawUsed served : Nat} {lowValue : Word} {close : Bool}
    (h : RuntimeRouteEnvelope.At c ram input s head amount rawUsed served lowValue close) (hp : c.pc=0x8000146c#32)
    (matched : c.get 10=1#32) (captures : c.get 11=0#32)
    (route : MainRequestSpans.path input head=WireSpec.ascii "/temp")
    (method : MainMethodSpec.decode (MainMethodBytes.token input head.method.2)=.post) :
    ∃ d, Quiet.Steps B img 28 ⟨c,ram⟩ ⟨d,MainTempWriteSetup.memory ram⟩ ∧
      StackRuntimeApiWriteCaller.Ready 1 future (WireSpec.ascii "/temp") none d (MainTempWriteSetup.memory ram) input s head amount rawUsed served close ∧ d.sameCsr c ∧ ViewFrame.Region ram (MainTempWriteSetup.memory ram) sp 3304 ∧ d.get 23=c.get 23 ∧ d.get 26=c.get 26 ∧ d.get 19=c.get 19 := by
  have block (p : Word) (off n : Nat) (positive : 0<n) (address : 0x80ff0000#32+BitVec.ofNat 32 off=p) (bound : off+n≤65536) : Memory.Block B p n := by
    rw [←address]
    exact Memory.sub_block StackBoard.available positive bound
  have stack : Memory.Block B sp 5232 := block _ 60304 5232 (by decide) (by decide +kernel) (by decide)
  have fields (i : Fin 5) := h.futures ⟨2,by decide⟩ i
  have methodByte : ram 0x80fff9f4#32=2#8 := by
    have value := h.stored.methodByte
    rw [method] at value
    exact value
  have postRoute : ram 0x80ffec08#32=2#8 := by
    have value := (h.table ⟨2,by decide⟩).2.2
    exact value
  obtain ⟨d,steps,pd,d13,d10,d12,d11,d14,d9,d1,keep,csr⟩ := MainTempWriteSetup.contract B c ram h.stable.sp h.stable.fp matched captures h.stable.one stack
    (by have v := fields ⟨0,by decide⟩; change ramRead ram (fp+600#32) .w=0x80ffebe8#32 at v; simpa only [show fp+600#32=0x80fffa6c#32 by decide +kernel] using v)
    (by have v := fields ⟨1,by decide⟩; change ramRead ram (fp+604#32) .w=req at v; simpa only [show fp+604#32=0x80fffa70#32 by decide +kernel] using v)
    (by have v := fields ⟨2,by decide⟩; change ramRead ram (fp+608#32) .w=eng at v; simpa only [show fp+608#32=0x80fffa74#32 by decide +kernel] using v)
    (by have v := fields ⟨3,by decide⟩; change ramRead ram (fp+612#32) .w=0x80fff4d4#32 at v; simpa only [show fp+612#32=0x80fffa78#32 by decide +kernel] using v)
    (by have v := fields ⟨4,by decide⟩; change ramRead ram (fp+616#32) .w=832#32 at v; simpa only [show fp+616#32=0x80fffa7c#32 by decide +kernel] using v)
    methodByte postRoute hp
  let after := MainTempWriteSetup.memory ram
  have frame := MainTempWriteSetup.frame ram
  have requestFrame : ViewFrame.Region ram after req 336 := by
    simpa only [show sp+3312#32=req by decide +kernel] using frame 3312 336 (by decide) (Or.inl (by decide))
  have rxFrame (start size : Nat) (bound : start+size≤2048) : ViewFrame.Region ram after (rx+BitVec.ofNat 32 start) size := by
    have region := frame (132+start) size (by omega) (Or.inl (by omega))
    simpa only [BitVec.ofNat_add,←BitVec.add_assoc,show sp+132#32=rx by decide +kernel] using region
  have rawLength := StackRuntimeRouteInputs.raw_length h
  have rawBound : (RuntimeRequestSpans.raw input rawUsed).length≤2048 := by rw [rawLength];have := h.stored.usedBound.2;have := h.stable.bound;omega
  have rawFrame : ViewFrame.Region ram after rx (RuntimeRequestSpans.raw input rawUsed).length := by
    simpa only [BitVec.add_zero] using rxFrame 0 _ (by omega)
  obtain ⟨pathBytes,pathLength,pathSeparate⟩ := StackRuntimeLiteralInput.literal_view h (WireSpec.ascii "/temp") route
  have targetBound : head.target.1+5≤2048 := by
    have hi := pathBytes.nowrap
    have bounds := MainQuerySpec.bounds (MainQuerySpec.bytes input) head.target.1 head.target.2 (by have := h.stored.bounds.target.2.1;omega)
    have := h.stored.contained.1
    have := (Nat.le_trans h.stored.usedBound.1 h.stored.usedBound.2)
    have := h.stable.bound
    change MainQuerySpec.position (MainQuerySpec.bytes input) head.target.1 head.target.2-head.target.1=5 at pathLength
    omega
  have bodyLength : (MainRequestSpans.body input head amount).length=amount := by
    simp only [MainRequestSpans.body,List.length_take,List.length_drop]
    exact Nat.min_eq_left (by have := (Nat.le_trans h.stored.usedBound.1 h.stored.usedBound.2);omega)
  have bodyBytes : Bytes.Span B ram (rx+BitVec.ofNat 32 head.len) (MainRequestSpans.body input head amount) := by
    have span := Bytes.subspan (StackRuntimeRouteInputs.whole h) head.len (head.len+amount) ⟨by omega,(Nat.le_trans h.stored.usedBound.1 h.stored.usedBound.2)⟩
    simpa only [MainRequestSpans.body,show head.len+amount-head.len=amount by omega] using span
  have bodyView : DecodeInput.BodyAt B ram req (rx+BitVec.ofNat 32 head.len) (MainRequestSpans.body input head amount) := by
    refine ⟨StackRuntimeRouteInputs.object h 328 (by decide) (by decide),by decide +kernel,?_,?_,bodyBytes⟩
    · change ramRead ram (sp+3632#32) .w=rx+BitVec.ofNat 32 head.len
      exact h.stored.request.body.trans (BitVec.add_comm _ _)
    · rw [bodyLength]
      exact h.stored.request.bodyLength
  have pathView : PathDispatch.PathAt B ram req (rx+BitVec.ofNat 32 head.target.1) (WireSpec.ascii "/temp") := by
    refine ⟨StackRuntimeRouteInputs.object h 312 (by decide) (by decide),by decide +kernel,h.stored.request.path,?_,pathBytes⟩
    have word := h.stored.request.pathLength
    change ramRead ram (sp+3620#32) .w=BitVec.ofNat 32 (MainQuerySpec.pathLength (MainQuerySpec.bytes input) head.target.1 head.target.2) at word
    rw [pathLength] at word
    exact word
  have pathFrame : ViewFrame.Region ram after (rx+BitVec.ofNat 32 head.target.1) (WireSpec.ascii "/temp").length := rxFrame _ _ targetBound
  have bodyFrame : ViewFrame.Region ram after (rx+BitVec.ofNat 32 head.len) (MainRequestSpans.body input head amount).length := rxFrame _ _ (by rw [bodyLength];have := (Nat.le_trans h.stored.usedBound.1 h.stored.usedBound.2);have := h.stable.bound;omega)
  have app : AppState.At after s := AppState.preserve ram after s h.stable.app (by
    simpa only [ViewFrame.Region,show sp+44#32=eng by decide +kernel] using frame 44 25 (by decide) (Or.inl (by decide)))
  have withinScratch (start len : Nat) (bound : start+len≤2048) : TxnScratch.Separate (rx+BitVec.ofNat 32 start) len arena := by
    intro i j
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    exact Ne.symm (WordZero.separated arena rx 128 2048 (by decide +kernel) (by decide +kernel) j ⟨start+i.val,by have := i.isLt;omega⟩)
  have params : WireInput.Params B after req (rx+BitVec.ofNat 32 head.target.1) (WireSpec.ascii "/temp") none :=
    .missing (StackRuntimeRouteInputs.object h 372 (by decide) (by decide)) (by decide +kernel) (MainTempWriteSetup.params_count ram)
  have layout : WriteInput.Layout B after arena req eng rx (rx+BitVec.ofNat 32 head.target.1) (rx+BitVec.ofNat 32 head.len)
      (RuntimeRequestSpans.raw input rawUsed) (WireSpec.ascii "/temp") (MainRequestSpans.body input head amount) (MainRequestInputs.entries head) none true s := by
    refine ⟨block _ 60128 128 (by decide) (by decide +kernel) (by decide),by decide +kernel,
      block _ 60348 25 (by decide) (by decide +kernel) (by decide),by decide +kernel,
      WordRegions.symm (WordRegions.before arena eng 128 25 (by decide) (by decide)),app.state,app.available,app.principal,app.keyPtr,app.keyLen,
      HeaderFrame.header_fields (StackRuntimeRouteInputs.headers h) requestFrame rawFrame,
      ViewFrame.body bodyView (ViewFrame.shrink requestFrame (by decide)) bodyFrame,
      ViewFrame.path pathView (ViewFrame.shrink requestFrame (by decide)) pathFrame,params,
      WordRegions.symm (WordRegions.before arena req 128 372 (by decide) (by decide)),
      withinScratch _ _ (by rw [bodyLength];have := (Nat.le_trans h.stored.usedBound.1 h.stored.usedBound.2);have := h.stable.bound;omega),withinScratch _ _ targetBound,?_⟩
    simpa only [BitVec.add_zero] using withinScratch 0 _ (by omega)
  have avoidRX (start len : Nat) (bound : start+len≤2048) : WriteInput.Avoid (rx+BitVec.ofNat 32 start) len (arena+80#32) future := by
    constructor
    · intro i j
      rw [BitVec.add_assoc,←BitVec.ofNat_add]
      exact Ne.symm (WordZero.separated (arena+80#32) rx 96 2048 (by decide +kernel) (by decide +kernel) j ⟨start+i.val,by have := i.isLt;omega⟩)
    · intro i j
      rw [BitVec.add_assoc,←BitVec.ofNat_add]
      exact WordZero.separated rx future 2048 41 (by decide +kernel) (by decide +kernel) ⟨start+i.val,by have := i.isLt;omega⟩ j
  have d2 : d.get 2=sp := (keep 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.stable.sp
  have d8 : d.get 8=fp := (keep 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.stable.fp
  have d18 : d.get 18=2#32 := (keep 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.two
  have d22 : d.get 22=1#32 := (keep 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.stable.one
  have pre : WriteInput.Pre B d after arena future out req eng rx (rx+BitVec.ofNat 32 head.target.1) (rx+BitVec.ofNat 32 head.len)
      (RuntimeRequestSpans.raw input rawUsed) (WireSpec.ascii "/temp") (MainRequestSpans.body input head amount) (MainRequestInputs.entries head) none true s := by
    refine ⟨pd,d2,d11,d10,block _ 60208 96 (by decide) (by decide +kernel) (by decide),
      block _ 64132 41 (by decide) (by decide +kernel) (by decide),by decide +kernel,
      WordRegions.symm (WordRegions.before (arena+80#32) future 96 41 (by decide) (by decide)),MainTempWriteSetup.fresh ram,
      MainTempWriteSetup.request ram,MainTempWriteSetup.engine ram,layout,
      ⟨WordRegions.symm (WordRegions.before (arena+80#32) eng 96 25 (by decide) (by decide)),WordRegions.before eng future 25 41 (by decide) (by decide)⟩,
      ⟨WordRegions.symm (WordRegions.before (arena+80#32) req 96 372 (by decide) (by decide)),WordRegions.before req future 372 41 (by decide) (by decide)⟩,?_,avoidRX _ _ targetBound,avoidRX _ _ ?_⟩
    · simpa only [BitVec.add_zero] using avoidRX 0 _ (by omega)
    · rw [bodyLength]
      have := (Nat.le_trans h.stored.usedBound.1 h.stored.usedBound.2)
      have := h.stable.bound
      omega
  have serveFrame : ViewFrame.Region ram after fp 96 := by
    simpa only [show sp+3204#32=fp by decide +kernel] using frame 3204 96 (by decide) (Or.inl (by decide))
  have cap : ramRead after 0x80fff9fc#32 .w=832#32 := by
    have word := ViewFrame.word (frame 3692 4 (by decide) (Or.inr (Or.inl ⟨by decide,by decide⟩))) 0 (by decide)
    simpa only [BitVec.add_zero,show sp+3692#32=0x80fff9fc#32 by decide +kernel] using word.trans h.replyCapacity
  have flag : after 0x80fff878#32=Encoding.boolByte close := by
    have byte := frame 3304 1 (by decide) (Or.inl (by decide)) ⟨0,by decide⟩
    simpa only [BitVec.add_zero,show sp+3304#32=0x80fff878#32 by decide +kernel] using byte.trans h.closeByte
  have methodAfter : after 0x80fff9f4#32=2#8 := by
    have byte := frame 3684 1 (by decide) (Or.inr (Or.inl ⟨by decide,by decide⟩)) ⟨0,by decide⟩
    simpa only [BitVec.add_zero,show sp+3684#32=0x80fff9f4#32 by decide +kernel] using byte.trans methodByte
  refine ⟨d,steps,⟨pre,d1,d2,d8,d18,d22,app,h.stable.invariant,h.stable.stack,
    MainServeLayout.preserve (MainServeMemoryFrames.whole serveFrame (by decide)) h.serve,cap,
    MainTempWriteSetup.pointer ram,MainTempWriteSetup.capacity ram,flag,h.closeSpec,(by change MainMethod.head (after 0x80fff9f4#32)=false;rw [methodAfter];rfl),(by decide +kernel)⟩,csr,?_,?_,?_,?_⟩
  · simpa only [BitVec.add_zero] using frame 0 3304 (by decide) (Or.inl (by decide))
  · exact keep 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact keep 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact keep 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
end E5R.Thermostat.StackRuntimeTempWriteInput
