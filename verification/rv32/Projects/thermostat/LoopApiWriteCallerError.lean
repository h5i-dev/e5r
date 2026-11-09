import Projects.thermostat.LoopWriteReturn
import Projects.thermostat.MainApiWriteCaller
import Projects.thermostat.MainWriteReturnJoin
import Projects.thermostat.WriteErrorFrameQuiet
set_option autoImplicit false
set_option maxRecDepth 6000
namespace E5R.Thermostat.LoopApiWriteCaller
open E5R E5R.Thermostat HttpRequestSpec MainApiWriteCaller
theorem error {kind : Fin 4} {future : Word} {path : List (BitVec 8)} {first : Option (List (BitVec 8))} {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat} {close : Bool}
    (h : Ready kind future path first c ram input s head amount served close) (cmd : Spec.Command) (err : Spec.Error)
    (allow : AuthSpec.authorized (HeaderSpec.lookup (MainRequestSpans.raw input head amount) (WireSpec.ascii "authorization") (MainRequestInputs.entries head)) (WireSpec.ascii "dev-key")=true)
    (decoded : WireSpec.decode path (MainRequestSpans.body input head amount) first=.ok cmd)
    (result : Spec.transition true s cmd=.error err)
    (hs bs : List UartTxLoop.Slot)
    (hhs : hs.length=(ResponseHeadSpec.bytes (ReplyJson.errorStatus err) (WireSpec.ascii "application/json") (ReplyJson.errorBody err).length close).length)
    (hbs : bs.length=(ReplyJson.errorBody err).length) :
    ∃ d n after, n≤212*(MainRequestInputs.entries head).length+18*(MainRequestSpans.body input head amount).length+3320+
        UartWriteAll.time (ResponseHeadSpec.bytes (ReplyJson.errorStatus err) (WireSpec.ascii "application/json") (ReplyJson.errorBody err).length close) hs+
        UartWriteAll.time (ReplyJson.errorBody err) bs ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (UartTxLoop.reads hs++UartTxLoop.reads bs)
        (UartTxLoop.events (ResponseHeadSpec.bytes (ReplyJson.errorStatus err) (WireSpec.ascii "application/json") (ReplyJson.errorBody err).length close)++UartTxLoop.events (ReplyJson.errorBody err)) ∧
      d.pc=(if close then 0x80000978#32 else 0x800017be#32) ∧ d.get 2=0x80ffeb90#32 ∧ d.get 8=fp ∧ d.sameCsr c ∧
      AppState.At after (Spec.commit s (.error err)) ∧ Engine.InvariantAt after 0x80ffebbc#32 ∧ ViewFrame.Region ram after 0x80ffec14#32 2048 ∧
      ViewFrame.Region ram after fp 96 ∧ ViewFrame.Region ram after 0x80ffeba0#32 4 ∧
      ViewFrame.Region ram after 0x80ffebd8#32 60 ∧ d.get 19=c.get 19 ∧ d.get 22=c.get 22 ∧ d.get 18=c.get 18 ∧ d.get 23=c.get 23 ∧ d.get 26=c.get 26 ∧ d.get 21=0xffffffff#32 := by
  have ⟨futureLow,futureHigh⟩ := h.futureBounds
  have block (p : Word) (off n : Nat) (positive : 0<n) (address : 0x80ff0000#32+BitVec.ofNat 32 off=p) (bound : off+n≤65536) : Memory.Block B p n := by
    rw [←address]
    exact Memory.sub_block h.stack positive bound
  have pre : WriteInput.Pre B c ram (0x80ffe9f0#32+240#32) future 0x80fffd38#32 0x80fff880#32 0x80ffebbc#32 0x80ffec14#32
      (0x80ffec14#32+BitVec.ofNat 32 head.target.1) (0x80ffec14#32+BitVec.ofNat 32 head.len)
      (MainRequestSpans.raw input head amount) path (MainRequestSpans.body input head amount) (MainRequestInputs.entries head) first true s := by
    simpa only [show 0x80ffe9f0#32+240#32=0x80ffeae0#32 by decide +kernel] using h.pre
  obtain ⟨a,na,mid,ba,ta,ret,response,bytes,state,borrow,inv,_,_,_,memory⟩ := WriteErrorFrame.contract_inv_quiet c ram
    0x80ffe9f0#32 future 0x80fffd38#32 0x80fff880#32 0x80ffebbc#32 0x80ffec14#32
    (0x80ffec14#32+BitVec.ofNat 32 head.target.1) (0x80ffec14#32+BitVec.ofNat 32 head.len) 0x80fff4d4#32
    (MainRequestSpans.raw input head amount) path (MainRequestSpans.body input head amount) (MainRequestInputs.entries head) first 832 true s cmd err pre allow decoded result h.invariant
    (block _ 59888 416 (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by decide +kernel) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) h.capacity h.pointer (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))
    (block _ 62676 832 (by decide) (by decide +kernel) (by decide)) (by decide) (by decide)
    (block _ 64824 15 (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by decide +kernel) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
  have region (obj : Word) (size : Nat)
      (hs : WordRegions.Disjoint obj size 0x80ffe9f0#32 416)
      (hd : WordRegions.Disjoint obj size 0x80fff4d4#32 832)
      (ho : WordRegions.Disjoint obj size 0x80fffd38#32 15)
      (hf : WordRegions.Disjoint obj size future 41)
      (he : WordRegions.Disjoint obj size 0x80ffebbc#32 14) : ViewFrame.Region ram mid obj size :=
    fun i => memory _ (hs i) (hd i) (ho i) (hf i) (he i)
  have keys : ViewFrame.Region ram mid 0x80ffebcc#32 9 := region _ _
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))) (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))) (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
  have app : AppState.At mid (Spec.commit s (.error err)) := by
    refine ⟨state,borrow,?_,?_,(keys ⟨8,by decide⟩).trans h.app.principal⟩
    · have word := ViewFrame.word keys 0 (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))
      simpa only [BitVec.add_zero] using word.trans h.app.keyPtr
    · exact (ViewFrame.word keys 4 (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))).trans h.app.keyLen
  have nextInvariant : Spec.Inv (Spec.commit s (.error err)) := by
    simpa only [result] using Spec.commit_inv true s cmd h.invariant
  have metadata : ViewFrame.Region ram mid fp 532 := region _ _
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))) (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
  have word (off : Nat) (bound : off+4≤532) := ViewFrame.word metadata off bound
  have cap : ramRead mid 0x80fff9fc#32 .w=832#32 := by
    have value := word 488 (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))
    simpa only [show fp+BitVec.ofNat 32 (488 : Nat)=0x80fff9fc#32 by decide +kernel] using value.trans h.replyCapacity
  have flag : mid 0x80fff878#32=Encoding.boolByte close := by
    have byte := metadata ⟨100,by decide⟩
    simpa only [show fp+100#32=0x80fff878#32 by decide +kernel] using byte.trans h.closeByte
  have notHead : MainMethod.head (mid 0x80fff9f4#32)=false := by
    have byte := metadata ⟨480,by decide⟩
    have preserved : mid 0x80fff9f4#32=ram 0x80fff9f4#32 := by
      simpa only [show fp+480#32=0x80fff9f4#32 by decide +kernel] using byte
    rw [preserved];exact h.notHead
  have body : ResponseHeadSpec.body (ReplyJson.errorStatus err) (MainMethod.head (mid 0x80fff9f4#32)) (ReplyJson.errorBody err)=ReplyJson.errorBody err := by rw [notHead];cases err <;> rfl
  have pc : a.pc=MainWriteReturnJoin.entry kind := by
    have masks : ∀ k : Fin 4, MainWriteReturnJoin.entry k &&& ~~~1=MainWriteReturnJoin.entry k := by decide +kernel
    rw [ret.pc,h.ret,masks]
  obtain ⟨d,nb,after,bb,tb,pd,d2,d8,dc,appAfter,invAfter,rx,low,capFrame,routes,d19,d22,d18,d23,d26,d21⟩ := LoopWriteReturn.contract_exact kind a mid (Spec.commit s (.error err)) (ramRead ram (fp+72#32) .w)
    (ReplyJson.errorBody err) (ReplyJson.errorStatus err) close pc (ret.sp.trans h.sp) (ret.x8.trans h.fp) (ret.x18.trans h.two) (ret.x22.trans h.one)
    h.stack app nextInvariant (by cases err <;> decide +kernel) (by cases err <;> decide +kernel) (by cases err <;> decide +kernel) (by cases err <;> exact response) bytes cap
    ((word 64 (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))).trans h.serve.tx) ((word 68 (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))).trans h.serve.txCapacity) (word 72 (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))) flag hs bs hhs (by rw [body];exact hbs)
  rw [body] at bb tb
  have capacityFrame : ViewFrame.Region ram mid 0x80ffeba0#32 4 := region _ _
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
  have routeFrame : ViewFrame.Region ram mid 0x80ffebd8#32 60 := region _ _
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
  refine ⟨d,na+nb,after,by omega,?_,pd,d2,d8,dc.trans ret.csr,appAfter,invAfter,?_,?_,?_,?_,?_,?_,?_,?_,?_,d21⟩
  · simpa only [List.nil_append] using ta.observed.trans tb
  · have beforeRx : ViewFrame.Region ram mid 0x80ffec14#32 2048 := region _ _
      (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
      (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))) (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
      (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))) (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
    intro i
    exact (rx i).trans (beforeRx i)
  · intro i;exact (low i).trans (metadata ⟨i.val,by have := i.isLt;omega⟩)
  · intro i;exact (capFrame i).trans (capacityFrame i)
  · intro i;exact (routes i).trans (routeFrame i)
  · exact d19.trans ret.x19
  · exact d22.trans ret.x22
  · exact d18.trans ret.x18
  · exact d23.trans ret.x23
  · exact d26.trans ret.x26
end E5R.Thermostat.LoopApiWriteCaller
