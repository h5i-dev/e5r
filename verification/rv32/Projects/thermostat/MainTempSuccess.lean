import Projects.thermostat.MainTempWriteInput
import Projects.thermostat.MainWriteReturnJoin
import Projects.thermostat.WriteSuccessFrameQuiet
set_option autoImplicit false
set_option maxRecDepth 6000
namespace E5R.Thermostat.MainTempSuccess
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board
abbrev fp : Word := 0x80fff814#32
abbrev future := MainTempWriteInput.future

theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat} {close : Bool}
    (h : MainTempWriteInput.Ready c ram input s head amount served close) (cmd : Spec.Command) (res : Spec.Success)
    (allow : AuthSpec.authorized (HeaderSpec.lookup (MainRequestSpans.raw input head amount) (WireSpec.ascii "authorization") (MainRequestInputs.entries head)) (WireSpec.ascii "dev-key")=true)
    (decoded : WireSpec.decode (WireSpec.ascii "/temp") (MainRequestSpans.body input head amount) none=.ok cmd)
    (result : Spec.transition true s cmd=.ok res)
    (hs bs : List UartTxLoop.Slot)
    (hhs : hs.length=(ResponseHeadSpec.bytes 200 (WireSpec.ascii "application/json") (ReplyJson.snapshot res.reply).length close).length)
    (hbs : bs.length=(ReplyJson.snapshot res.reply).length) :
    ∃ d n after, n≤212*(MainRequestInputs.entries head).length+18*(MainRequestSpans.body input head amount).length+7045+
        UartWriteAll.time (ResponseHeadSpec.bytes 200 (WireSpec.ascii "application/json") (ReplyJson.snapshot res.reply).length close) hs+
        UartWriteAll.time (ReplyJson.snapshot res.reply) bs ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (UartTxLoop.reads hs++UartTxLoop.reads bs)
        (UartTxLoop.events (ResponseHeadSpec.bytes 200 (WireSpec.ascii "application/json") (ReplyJson.snapshot res.reply).length close)++UartTxLoop.events (ReplyJson.snapshot res.reply)) ∧
      d.pc=(if close then 0x80000978#32 else 0x800017be#32) ∧ d.get 2=0x80ffeb90#32 ∧ d.get 8=fp ∧ d.sameCsr c ∧
      AppState.At after (Spec.commit s (.ok res)) ∧ Engine.InvariantAt after 0x80ffebbc#32 ∧ ViewFrame.Region ram after 0x80ffec14#32 2048 := by
  have block (p : Word) (off n : Nat) (positive : 0<n) (address : 0x80ff0000#32+BitVec.ofNat 32 off=p) (bound : off+n≤65536) : Memory.Block B p n := by
    rw [←address]
    exact Memory.sub_block h.stack positive bound
  have pre : WriteInput.Pre B c ram (0x80ffe9f0#32+240#32) future 0x80fffd38#32 0x80fff880#32 0x80ffebbc#32 0x80ffec14#32
      (0x80ffec14#32+BitVec.ofNat 32 head.target.1) (0x80ffec14#32+BitVec.ofNat 32 head.len)
      (MainRequestSpans.raw input head amount) (WireSpec.ascii "/temp") (MainRequestSpans.body input head amount) (MainRequestInputs.entries head) none true s := by
    simpa only [show 0x80ffe9f0#32+240#32=MainTempWriteInput.arena by decide +kernel] using h.pre
  obtain ⟨a,na,mid,ba,ta,ret,response,bytes,state,borrow,inv,_,_,_,memory⟩ := WriteSuccessFrame.contract_inv_quiet c ram
    0x80ffe9f0#32 future 0x80fffd38#32 0x80fff880#32 0x80ffebbc#32 0x80ffec14#32
    (0x80ffec14#32+BitVec.ofNat 32 head.target.1) (0x80ffec14#32+BitVec.ofNat 32 head.len) 0x80fff4d4#32
    (MainRequestSpans.raw input head amount) (WireSpec.ascii "/temp") (MainRequestSpans.body input head amount) (MainRequestInputs.entries head) none 832 true s cmd res pre allow decoded result h.invariant
    (block _ 59888 416 (by decide) (by decide +kernel) (by decide)) (by decide) h.capacity h.pointer (by decide) (by decide)
    (block _ 62676 832 (by decide) (by decide +kernel) (by decide)) (by decide)
    (block _ 64824 15 (by decide) (by decide +kernel) (by decide)) (by decide)
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    (WordRegions.before _ _ _ _ (by decide) (by decide))
    (WordRegions.before _ _ _ _ (by decide) (by decide))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    (WordRegions.before _ _ _ _ (by decide) (by decide))
    (WordRegions.before _ _ _ _ (by decide) (by decide))
  have region (obj : Word) (size : Nat)
      (hs : WordRegions.Disjoint obj size 0x80ffe9f0#32 416)
      (hd : WordRegions.Disjoint obj size 0x80fff4d4#32 832)
      (ho : WordRegions.Disjoint obj size 0x80fffd38#32 15)
      (hf : WordRegions.Disjoint obj size future 41)
      (he : WordRegions.Disjoint obj size 0x80ffebbc#32 14) : ViewFrame.Region ram mid obj size :=
    fun i => memory _ (hs i) (hd i) (ho i) (hf i) (he i)
  have keys : ViewFrame.Region ram mid 0x80ffebcc#32 9 := region _ _
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    (WordRegions.before _ _ _ _ (by decide) (by decide)) (WordRegions.before _ _ _ _ (by decide) (by decide))
    (WordRegions.before _ _ _ _ (by decide) (by decide)) (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
  have app : AppState.At mid (Spec.commit s (.ok res)) := by
    refine ⟨state,borrow,?_,?_,(keys ⟨8,by decide⟩).trans h.app.principal⟩
    · have word := ViewFrame.word keys 0 (by decide)
      simpa only [BitVec.add_zero] using word.trans h.app.keyPtr
    · exact (ViewFrame.word keys 4 (by decide)).trans h.app.keyLen
  have nextInvariant : Spec.Inv (Spec.commit s (.ok res)) := by
    simpa only [result] using Spec.commit_inv true s cmd h.invariant
  have metadata : ViewFrame.Region ram mid fp 532 := region _ _
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    (WordRegions.before _ _ _ _ (by decide) (by decide)) (WordRegions.before _ _ _ _ (by decide) (by decide))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
  have word (off : Nat) (bound : off+4≤532) := ViewFrame.word metadata off bound
  have cap : ramRead mid 0x80fff9fc#32 .w=832#32 := by
    have value := word 488 (by decide)
    simpa only [show fp+BitVec.ofNat 32 (488 : Nat)=0x80fff9fc#32 by decide +kernel] using value.trans h.replyCapacity
  have flag : mid 0x80fff878#32=Encoding.boolByte close := by
    have byte := metadata ⟨100,by decide⟩
    simpa only [show fp+100#32=0x80fff878#32 by decide +kernel] using byte.trans h.closeByte
  have method : mid 0x80fff9f4#32=2#8 := by
    have byte := metadata ⟨480,by decide⟩
    simpa only [show fp+480#32=0x80fff9f4#32 by decide +kernel] using byte.trans h.method
  have body : ResponseHeadSpec.body 200 (MainMethod.head (mid 0x80fff9f4#32)) (ReplyJson.snapshot res.reply)=ReplyJson.snapshot res.reply := by rw [method];rfl
  have pc : a.pc=MainWriteReturnJoin.entry 1 := by rw [ret.pc,h.ret];decide +kernel
  obtain ⟨d,nb,after,bb,tb,pd,d2,d8,dc,appAfter,invAfter,rx⟩ := MainWriteReturnJoin.contract_exact 1 a mid (Spec.commit s (.ok res)) (ramRead ram (fp+72#32) .w)
    (ReplyJson.snapshot res.reply) 200 close pc (ret.sp.trans h.sp) (ret.x8.trans h.fp) (ret.x18.trans h.two) (ret.x22.trans h.one)
    h.stack app nextInvariant (Nat.le_trans (JsonCapacity.snapshot_length res.reply) (by decide)) (by decide) (by decide) response bytes cap
    ((word 64 (by decide)).trans h.serve.tx) ((word 68 (by decide)).trans h.serve.txCapacity) (word 72 (by decide)) flag hs bs hhs (by rw [body];exact hbs)
  rw [body] at bb tb
  refine ⟨d,na+nb,after,by omega,?_,pd,d2,d8,dc.trans ret.csr,appAfter,invAfter,?_⟩
  · simpa only [List.nil_append] using ta.observed.trans tb
  · have beforeRx : ViewFrame.Region ram mid 0x80ffec14#32 2048 := region _ _
      (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
      (WordRegions.before _ _ _ _ (by decide) (by decide)) (WordRegions.before _ _ _ _ (by decide) (by decide))
      (WordRegions.before _ _ _ _ (by decide) (by decide)) (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    intro i
    exact (rx i).trans (beforeRx i)
end E5R.Thermostat.MainTempSuccess
