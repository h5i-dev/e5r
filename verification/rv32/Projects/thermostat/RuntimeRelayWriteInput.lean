import Projects.thermostat.MainRelayWriteInput
import Projects.thermostat.RuntimeRelayCaptured
import Projects.thermostat.MainRelayWriteSetup
import Projects.thermostat.RuntimeRouteInputs
import Projects.thermostat.RuntimeApiWriteCaller
set_option autoImplicit false
set_option maxRecDepth 6000
namespace E5R.Thermostat.RuntimeRelayWriteInput
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board
abbrev sp : Word := 0x80ffeb90#32
abbrev fp : Word := 0x80fff814#32
abbrev rx : Word := 0x80ffec14#32
abbrev req : Word := 0x80fff880#32
abbrev eng : Word := 0x80ffebbc#32
abbrev arena : Word := 0x80ffeae0#32
abbrev future : Word := 0x80fffa2c#32
abbrev out : Word := 0x80fffd38#32

theorem captured_suffix (param : List (BitVec 8)) :
    ParamInput.captured (RuntimeRelayCaptured.path param) 7 (7+param.length)=param := by
  unfold ParamInput.captured RuntimeRelayCaptured.path
  rw [show 7+param.length-7=param.length by omega]
  change param.take param.length=param
  exact List.take_length

/-- Captures have changed RAM: derive the exact retained fields and first
    parameter, then execute the real method/future/call instructions. -/
theorem contract {origin : Core} {before : Word → BitVec 8} {c : Core} {ram : Word → BitVec 8}
    {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount rawUsed served : Nat} {lowValue : Word} {close : Bool} {param : List (BitVec 8)}
    (h : RuntimeRelayCaptured.At origin before c ram input s head amount rawUsed served lowValue close param)
    (method : MainMethodSpec.decode (MainMethodBytes.token input head.method.2)=.put) :
    ∃ d, Quiet.Steps B img 26 ⟨c,ram⟩ ⟨d,MainRelayWriteSetup.memory ram (ramRead ram (sp+20#32) .w)⟩ ∧
      RuntimeApiWriteCaller.Ready 3 future (RuntimeRelayCaptured.path param) (some param) d
        (MainRelayWriteSetup.memory ram (ramRead ram (sp+20#32) .w)) input s head amount rawUsed served close ∧ d.mie_=false ∧ ViewFrame.Region ram (MainRelayWriteSetup.memory ram (ramRead ram (sp+20#32) .w)) sp 3304 ∧
      d.get 19=c.get 19 ∧ d.get 23=c.get 23 ∧ d.get 26=c.get 26 := by
  have block (p : Word) (off n : Nat) (positive : 0<n) (address : 0x80ff0000#32+BitVec.ofNat 32 off=p) (bound : off+n≤65536) : Memory.Block B p n := by
    rw [←address];exact Memory.sub_block h.live.stable.stack positive bound
  have beforeRegion (off length : Nat) (bound : off+length≤5232) (apart : off+length≤3648 ∨ 3656≤off) :
      ViewFrame.Region before ram (sp+BitVec.ofNat 32 off) length := by
    refine RuntimeRelayCaptured.frame h _ _ ?_ ?_
    · intro i j
      have ne := FrameOffsets.ne 0x80ffeb30#32 (96+off) 0 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;omega) (by have := i.isLt;have := j.isLt;omega)
      simpa only [BitVec.ofNat_add,←BitVec.add_assoc,show 0x80ffeb30#32+96#32=sp by decide +kernel,BitVec.add_zero] using ne
    · intro i j
      have ne := FrameOffsets.ne sp off 3648 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;omega) (by have := i.isLt;have := j.isLt;rcases apart with left|right <;>omega)
      simpa only [show sp+3648#32=RuntimeRelayCaptured.params by decide +kernel] using ne
  have fieldsFrame : ViewFrame.Region before ram (fp+512#32) 20 := by
    simpa only [show sp+3716#32=fp+512#32 by decide +kernel] using beforeRegion 3716 20 (by decide) (Or.inr (by decide))
  have fields (i : Fin 5) : ramRead ram (fp+BitVec.ofNat 32 (512+4*i.val)) .w=MainRouterFutures.value 0 i := by
    have word := ViewFrame.word fieldsFrame (4*i.val) (by have := i.isLt;omega)
    rw [BitVec.add_assoc,←BitVec.ofNat_add] at word
    exact word.trans (h.live.futures 0 i)
  have methodBefore : ram 0x80fff9f4#32=3#8 := by
    have byte := beforeRegion 3684 1 (by decide) (Or.inr (by decide)) ⟨0,by decide⟩
    have old := h.live.stored.methodByte
    rw [method] at old
    simpa only [BitVec.add_zero,show sp+3684#32=0x80fff9f4#32 by decide +kernel] using byte.trans (by simpa only [MainMethodSpec.tag,BitVec.add_zero] using old)
  have putRoute : ram 0x80ffec10#32=3#8 := by
    have byte := beforeRegion 128 1 (by decide) (Or.inl (by decide)) ⟨0,by decide⟩
    have old := (h.live.table ⟨4,by decide⟩).2.2
    simpa only [BitVec.add_zero,show sp+128#32=0x80ffec10#32 by decide +kernel] using byte.trans old
  have c2 := (h.regs 2 (by decide)).trans h.live.stable.sp
  have c8 := (h.regs 8 (by decide)).trans h.live.stable.fp
  have c22 := (h.regs 22 (by decide)).trans h.live.stable.one
  obtain ⟨d,steps,pd,d13,d10,d12,d6,d11,d14,d1,keep,csr⟩ := MainRelayWriteSetup.contract B c ram (ramRead ram (sp+20#32) .w)
    c2 c8 h.matched h.captures c22 h.future (block _ 60304 5232 (by decide) (by decide +kernel) (by decide)) rfl
    (by have v := fields ⟨0,by decide⟩;change ramRead ram (fp+512#32) .w=0x80ffebd8#32 at v;simpa only [show fp+512#32=0x80fffa14#32 by decide +kernel] using v)
    (by have v := fields ⟨1,by decide⟩;change ramRead ram (fp+516#32) .w=req at v;simpa only [show fp+516#32=0x80fffa18#32 by decide +kernel] using v)
    (by have v := fields ⟨2,by decide⟩;change ramRead ram (fp+520#32) .w=eng at v;simpa only [show fp+520#32=0x80fffa1c#32 by decide +kernel] using v)
    (by have v := fields ⟨3,by decide⟩;change ramRead ram (fp+524#32) .w=0x80fff4d4#32 at v;simpa only [show fp+524#32=0x80fffa20#32 by decide +kernel] using v)
    (by have v := fields ⟨4,by decide⟩;change ramRead ram (fp+528#32) .w=832#32 at v;simpa only [show fp+528#32=0x80fffa24#32 by decide +kernel] using v)
    methodBefore putRoute h.pc
  let after := MainRelayWriteSetup.memory ram (ramRead ram (sp+20#32) .w)
  have frame := MainRelayWriteSetup.frame ram (ramRead ram (sp+20#32) .w)
  have region (off length : Nat) (bound : off+length≤5232) (pair : off+length≤3648 ∨ 3656≤off)
      (setup : off+length≤3680 ∨ (3684≤off ∧ off+length≤3740) ∨ 3781≤off) : ViewFrame.Region before after (sp+BitVec.ofNat 32 off) length :=
    fun i => (frame off length bound setup i).trans (beforeRegion off length bound pair i)
  have requestFrame : ViewFrame.Region before after req 336 := by
    simpa only [show sp+3312#32=req by decide +kernel] using region 3312 336 (by decide) (Or.inl (by decide)) (Or.inl (by decide))
  have rxFrame (start length : Nat) (bound : start+length≤2048) : ViewFrame.Region before after (rx+BitVec.ofNat 32 start) length := by
    simpa only [BitVec.ofNat_add,←BitVec.add_assoc,show sp+132#32=rx by decide +kernel] using region (132+start) length (by omega) (Or.inl (by omega)) (Or.inl (by omega))
  have rawLength := RuntimeRouteInputs.raw_length h.live
  have rawBound : (RuntimeRequestSpans.raw input rawUsed).length≤2048 := by rw [rawLength];have := h.live.stored.usedBound.2;have := h.live.stable.bound;omega
  have rawFrame : ViewFrame.Region before after rx (RuntimeRequestSpans.raw input rawUsed).length := by simpa only [BitVec.add_zero] using rxFrame 0 _ (by omega)
  obtain ⟨pathBytes,pathLength,lower,pathSeparate⟩ := RuntimeRelayCaptured.path_view h.live param h.route h.nonempty
  have targetBound : head.target.1+(RuntimeRelayCaptured.path param).length≤2048 := by
    have bounds := MainQuerySpec.bounds (MainQuerySpec.bytes input) head.target.1 head.target.2 (by have := h.live.stored.bounds.target.2.1;omega)
    have pureLength := (RuntimeLiteralInput.literal_view h.live _ h.route).2.1
    change MainQuerySpec.position (MainQuerySpec.bytes input) head.target.1 head.target.2-head.target.1=(RuntimeRelayCaptured.path param).length at pureLength
    have := h.live.stored.contained.1
    have := (Nat.le_trans h.live.stored.usedBound.1 h.live.stored.usedBound.2)
    have := h.live.stable.bound
    omega
  have bodyLength : (MainRequestSpans.body input head amount).length=amount := by
    simp only [MainRequestSpans.body,List.length_take,List.length_drop]
    exact Nat.min_eq_left (by have := (Nat.le_trans h.live.stored.usedBound.1 h.live.stored.usedBound.2);omega)
  have bodyBytes : Bytes.Span B before (rx+BitVec.ofNat 32 head.len) (MainRequestSpans.body input head amount) := by
    have span := Bytes.subspan (RuntimeRouteInputs.whole h.live) head.len (head.len+amount) ⟨by omega,(Nat.le_trans h.live.stored.usedBound.1 h.live.stored.usedBound.2)⟩
    simpa only [MainRequestSpans.body,show head.len+amount-head.len=amount by omega] using span
  have bodyView : DecodeInput.BodyAt B before req (rx+BitVec.ofNat 32 head.len) (MainRequestSpans.body input head amount) := by
    refine ⟨RuntimeRouteInputs.object h.live 328 (by decide) (by decide),by decide +kernel,?_,?_,bodyBytes⟩
    · exact h.live.stored.request.body.trans (BitVec.add_comm _ _)
    · rw [bodyLength];exact h.live.stored.request.bodyLength
  have pathView : PathDispatch.PathAt B before req (rx+BitVec.ofNat 32 head.target.1) (RuntimeRelayCaptured.path param) := by
    refine ⟨RuntimeRouteInputs.object h.live 312 (by decide) (by decide),by decide +kernel,h.live.stored.request.path,?_,pathBytes⟩
    have size := (RuntimeLiteralInput.literal_view h.live _ h.route).2.1
    rw [←size];exact h.live.stored.request.pathLength
  have pathFrame := rxFrame head.target.1 (RuntimeRelayCaptured.path param).length targetBound
  have bodyFrame : ViewFrame.Region before after (rx+BitVec.ofNat 32 head.len) (MainRequestSpans.body input head amount).length := rxFrame _ _ (by rw [bodyLength];have := (Nat.le_trans h.live.stored.usedBound.1 h.live.stored.usedBound.2);have := h.live.stable.bound;omega)
  have app : AppState.At after s := AppState.preserve before after s h.live.stable.app (by
    simpa only [ViewFrame.Region,show sp+44#32=eng by decide +kernel] using region 44 25 (by decide) (Or.inl (by decide)) (Or.inl (by decide)))
  have pathAfter := ViewFrame.path pathView (ViewFrame.shrink requestFrame (by decide)) pathFrame
  have pairFrame : ViewFrame.Region ram after RuntimeRelayCaptured.params 8 := by
    simpa only [show sp+3648#32=RuntimeRelayCaptured.params by decide +kernel] using frame 3648 8 (by decide) (Or.inl (by decide))
  have startWord : ramRead after (req+336#32) .w=7#32 := by
    have word := (ViewFrame.word pairFrame 0 (by decide)).trans (RuntimeRelayCaptured.first_word h)
    simpa only [BitVec.add_zero,show req+336#32=RuntimeRelayCaptured.params by decide +kernel] using word
  have endWord : ramRead after (req+340#32) .w=RuntimeRelayCaptured.size param := by
    have word := (ViewFrame.word pairFrame 4 (by decide)).trans (RuntimeRelayCaptured.second_word h)
    simpa only [show req+340#32=RuntimeRelayCaptured.params+4#32 by decide +kernel] using word
  have countWord : ramRead after (req+368#32) .w=1#32 := by
    simpa only [show req+368#32=sp+3680#32 by decide +kernel] using MainRelayWriteSetup.params_count ram (ramRead ram (sp+20#32) .w)
  have capture : ParamInput.Capture B after req (rx+BitVec.ofNat 32 head.target.1) (RuntimeRelayCaptured.path param) 7 (7+param.length) 1 := by
    refine ⟨RuntimeRouteInputs.object h.live 372 (by decide) (by decide),by decide +kernel,countWord,by decide,
      pathAfter.pointer,pathAfter.length,startWord,endWord,by omega,?_,pathAfter.bytes⟩
    change 7+param.length≤(WireSpec.ascii "/relay/"++param).length
    rw [List.length_append];exact Nat.le_refl _
  have paramsView : WireInput.Params B after req (rx+BitVec.ofNat 32 head.target.1) (RuntimeRelayCaptured.path param) (some param) := by
    simpa only [captured_suffix] using WireInput.Params.present capture
  have withinScratch (start length : Nat) (bound : start+length≤2048) : TxnScratch.Separate (rx+BitVec.ofNat 32 start) length arena := by
    intro i j
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    exact Ne.symm (WordZero.separated arena rx 128 2048 (by decide +kernel) (by decide +kernel) j ⟨start+i.val,by have := i.isLt;omega⟩)
  have layout : WriteInput.Layout B after arena req eng rx (rx+BitVec.ofNat 32 head.target.1) (rx+BitVec.ofNat 32 head.len)
      (RuntimeRequestSpans.raw input rawUsed) (RuntimeRelayCaptured.path param) (MainRequestSpans.body input head amount) (MainRequestInputs.entries head) (some param) true s := by
    refine ⟨block _ 60128 128 (by decide) (by decide +kernel) (by decide),by decide +kernel,
      block _ 60348 25 (by decide) (by decide +kernel) (by decide),by decide +kernel,
      WordRegions.symm (WordRegions.before arena eng 128 25 (by decide) (by decide)),app.state,app.available,app.principal,app.keyPtr,app.keyLen,
      HeaderFrame.header_fields (RuntimeRouteInputs.headers h.live) requestFrame rawFrame,
      ViewFrame.body bodyView (ViewFrame.shrink requestFrame (by decide)) bodyFrame,pathAfter,paramsView,
      WordRegions.symm (WordRegions.before arena req 128 372 (by decide) (by decide)),
      withinScratch _ _ (by rw [bodyLength];have := (Nat.le_trans h.live.stored.usedBound.1 h.live.stored.usedBound.2);have := h.live.stable.bound;omega),withinScratch _ _ targetBound,?_⟩
    simpa only [BitVec.add_zero] using withinScratch 0 _ (by omega)
  have avoidRX (start length : Nat) (bound : start+length≤2048) : WriteInput.Avoid (rx+BitVec.ofNat 32 start) length (arena+80#32) future := by
    constructor
    · intro i j
      rw [BitVec.add_assoc,←BitVec.ofNat_add]
      exact Ne.symm (WordZero.separated (arena+80#32) rx 96 2048 (by decide +kernel) (by decide +kernel) j ⟨start+i.val,by have := i.isLt;omega⟩)
    · intro i j
      rw [BitVec.add_assoc,←BitVec.ofNat_add]
      exact WordZero.separated rx future 2048 41 (by decide +kernel) (by decide +kernel) ⟨start+i.val,by have := i.isLt;omega⟩ j
  have d2 : d.get 2=sp := (keep 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans c2
  have d8 : d.get 8=fp := (keep 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans c8
  have d18 : d.get 18=2#32 := (keep 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((h.regs 18 (by decide)).trans h.live.two)
  have d22 : d.get 22=1#32 := (keep 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans c22
  have pre : WriteInput.Pre B d after arena future out req eng rx (rx+BitVec.ofNat 32 head.target.1) (rx+BitVec.ofNat 32 head.len)
      (RuntimeRequestSpans.raw input rawUsed) (RuntimeRelayCaptured.path param) (MainRequestSpans.body input head amount) (MainRequestInputs.entries head) (some param) true s := by
    refine ⟨pd,d2,d11,d10,block _ 60208 96 (by decide) (by decide +kernel) (by decide),
      block _ 64044 41 (by decide) (by decide +kernel) (by decide),by decide +kernel,
      WordRegions.symm (WordRegions.before (arena+80#32) future 96 41 (by decide) (by decide)),MainRelayWriteSetup.fresh ram _,
      MainRelayWriteSetup.request ram _,MainRelayWriteSetup.engine ram _,layout,
      ⟨WordRegions.symm (WordRegions.before (arena+80#32) eng 96 25 (by decide) (by decide)),WordRegions.before eng future 25 41 (by decide) (by decide)⟩,
      ⟨WordRegions.symm (WordRegions.before (arena+80#32) req 96 372 (by decide) (by decide)),WordRegions.before req future 372 41 (by decide) (by decide)⟩,?_,avoidRX _ _ targetBound,avoidRX _ _ ?_⟩
    · simpa only [BitVec.add_zero] using avoidRX 0 _ (by omega)
    · rw [bodyLength];have := (Nat.le_trans h.live.stored.usedBound.1 h.live.stored.usedBound.2);have := h.live.stable.bound;omega
  have serveFrame : ViewFrame.Region before after fp 96 := by
    simpa only [show sp+3204#32=fp by decide +kernel] using region 3204 96 (by decide) (Or.inl (by decide)) (Or.inl (by decide))
  have cap : ramRead after 0x80fff9fc#32 .w=832#32 := by
    have word := ViewFrame.word (region 3692 4 (by decide) (Or.inr (by decide)) (Or.inr (Or.inl ⟨by decide,by decide⟩))) 0 (by decide)
    simpa only [BitVec.add_zero,show sp+3692#32=0x80fff9fc#32 by decide +kernel] using word.trans h.live.replyCapacity
  have flag : after 0x80fff878#32=Encoding.boolByte close := by
    have byte := region 3304 1 (by decide) (Or.inl (by decide)) (Or.inl (by decide)) ⟨0,by decide⟩
    simpa only [BitVec.add_zero,show sp+3304#32=0x80fff878#32 by decide +kernel] using byte.trans h.live.closeByte
  have notHead : MainMethod.head (after 0x80fff9f4#32)=false := by
    have byte := frame 3684 1 (by decide) (Or.inr (Or.inl ⟨by decide,by decide⟩)) ⟨0,by decide⟩
    have preserved : after 0x80fff9f4#32=ram 0x80fff9f4#32 := by
      simpa only [BitVec.add_zero,show sp+3684#32=0x80fff9f4#32 by decide +kernel] using byte
    rw [preserved,methodBefore];rfl
  refine ⟨d,steps,⟨pre,d1,d2,d8,d18,d22,app,h.live.stable.invariant,h.live.stable.stack,
    MainServeLayout.preserve (MainServeMemoryFrames.whole serveFrame (by decide)) h.live.serve,cap,
    MainRelayWriteSetup.pointer ram _,MainRelayWriteSetup.capacity ram _,flag,h.live.closeSpec,notHead,by decide +kernel⟩,?_,?_,?_,?_,?_⟩
  · exact (congrArg Prod.fst csr).trans ((congrArg Prod.fst h.csr).trans h.live.stable.masked)
  · simpa only [BitVec.add_zero] using frame 0 3304 (by decide) (Or.inl (by decide))
  · apply keep;all_goals decide
  · apply keep;all_goals decide
  · apply keep;all_goals decide
end E5R.Thermostat.RuntimeRelayWriteInput
