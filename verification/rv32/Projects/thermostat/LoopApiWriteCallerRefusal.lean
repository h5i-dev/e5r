import Projects.thermostat.MainApiWriteCallerRefusal
import Projects.thermostat.LoopStatusReturn
set_option autoImplicit false
set_option maxRecDepth 6000
namespace E5R.Thermostat.LoopApiWriteCaller
open E5R E5R.Thermostat HttpRequestSpec MainApiWriteCaller
theorem refusal {kind : Fin 4} {future : Word} {path : List (BitVec 8)} {first : Option (List (BitVec 8))} {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat} {close : Bool}
    (h : Ready kind future path first c ram input s head amount served close) (status : Nat) (outcome : RefusalCase input head amount path first status)
    (hlo : 200≤status) (hst : status≤599) (hs : List UartTxLoop.Slot) (hhs : hs.length=(ResponseHeadSpec.bytes status [] 0 close).length) :
    ∃ d n after, n≤212*(MainRequestInputs.entries head).length+18*(MainRequestSpans.body input head amount).length+2964+
        UartWriteAll.time (ResponseHeadSpec.bytes status [] 0 close) hs+UartWriteAll.time [] [] ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (UartTxLoop.reads hs) (UartTxLoop.events (ResponseHeadSpec.bytes status [] 0 close)) ∧
      d.pc=(if close then 0x80000978#32 else 0x800017be#32) ∧ d.get 2=0x80ffeb90#32 ∧ d.get 8=fp ∧ d.sameCsr c ∧
      AppState.At after s ∧ Engine.InvariantAt after 0x80ffebbc#32 ∧ ViewFrame.Region ram after 0x80ffec14#32 2048 ∧
      ViewFrame.Region ram after fp 96 ∧ ViewFrame.Region ram after 0x80ffeba0#32 4 ∧
      ViewFrame.Region ram after 0x80ffebd8#32 60 ∧ d.get 19=c.get 19 ∧ d.get 22=c.get 22 ∧ d.get 18=c.get 18 ∧ d.get 23=c.get 23 ∧ d.get 26=c.get 26 ∧ d.get 21=0xffffffff#32 := by
  have ⟨futureLow,futureHigh⟩ := h.futureBounds
  obtain ⟨a,na,mid,ba,ta,ret,response,state,borrow,inv,memory⟩ := refusal_handler h status outcome
  have keys : ViewFrame.Region ram mid 0x80ffebcc#32 9 := MainFutureFrame.region memory
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))) (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))) (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
  have app : AppState.At mid s := by
    refine ⟨state,borrow,?_,?_,(keys ⟨8,by decide⟩).trans h.app.principal⟩
    · have word := ViewFrame.word keys 0 (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))
      simpa only [BitVec.add_zero] using word.trans h.app.keyPtr
    · exact (ViewFrame.word keys 4 (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))).trans h.app.keyLen
  have metadata : ViewFrame.Region ram mid fp 532 := MainFutureFrame.region memory
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
  have pc : a.pc=MainWriteReturnJoin.entry kind := by
    have masks : ∀ k : Fin 4, MainWriteReturnJoin.entry k &&& ~~~1=MainWriteReturnJoin.entry k := by decide +kernel
    rw [ret.pc,h.ret,masks]
  obtain ⟨d,nb,after,bb,tb,pd,d2,d8,dc,appAfter,invAfter,rx,low,capFrame,routes,d19,d22,d18,d23,d26,d21⟩ := LoopStatusReturn.contract_exact kind a mid s (ramRead ram (fp+72#32) .w) status close
    pc (ret.sp.trans h.sp) (ret.x8.trans h.fp) (ret.x18.trans h.two) (ret.x22.trans h.one) h.stack app h.invariant hlo hst response cap
    ((word 64 (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))).trans h.serve.tx) ((word 68 (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))).trans h.serve.txCapacity) (word 72 (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))) flag hs hhs
  have capacityFrame : ViewFrame.Region ram mid 0x80ffeba0#32 4 := MainFutureFrame.region memory
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
  have routeFrame : ViewFrame.Region ram mid 0x80ffebd8#32 60 := MainFutureFrame.region memory
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
  refine ⟨d,na+nb,after,by omega,?_,pd,d2,d8,dc.trans ret.csr,appAfter,invAfter,?_,?_,?_,?_,?_,?_,?_,?_,?_,d21⟩
  · simpa only [List.nil_append] using ta.observed.trans tb
  · have beforeRx : ViewFrame.Region ram mid 0x80ffec14#32 2048 := MainFutureFrame.region memory
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
