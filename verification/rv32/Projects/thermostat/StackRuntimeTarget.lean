import Projects.thermostat.RuntimeTarget
import Projects.thermostat.StackBoard
set_option autoImplicit false
set_option maxRecDepth 4000
namespace E5R.Thermostat.StackRuntimeTarget
open E5R E5R.Thermostat HttpRequestSpec RuntimeTarget
abbrev B := StackBoard.board

theorem contract {c ram input s head amount rawUsed served lowValue} (h : RuntimeNext.Ready c ram input s head amount rawUsed served lowValue) :
    ∃ d, Quiet.Steps B img 17 ⟨c,ram⟩
      ⟨d,MainRequestCounter.memory ram sp (BitVec.ofNat 32 served) (BitVec.ofNat 32 rawUsed)⟩ ∧
      Ready d (MainRequestCounter.memory ram sp (BitVec.ofNat 32 served) (BitVec.ofNat 32 rawUsed)) input s head amount rawUsed (served+1) lowValue ∧ d.sameCsr c := by
  have lenBound := h.bounds.length.2
  have bodyBound := h.bodyBound
  have totalBound : rawUsed≤2048 := by have := h.available;have := h.stable.bound;omega
  have targetBound : head.target.2≤2048 := by have := h.bounds.target.2.2;omega
  have startBound : head.target.1≤2048 := by have := h.bounds.target.2.1;omega
  have targetOrder := h.bounds.target.2.1
  have capacity : taken .geu 2048#32 (BitVec.ofNat 32 rawUsed)=true := by
    simpa only [show decide (rawUsed≤2048)=true from decide_eq_true totalBound] using HeadTargetMath.geu 2048 rawUsed (by decide) totalBound
  have order : taken .geu (BitVec.ofNat 32 head.target.2) (BitVec.ofNat 32 head.target.1)=true := by
    simpa only [show decide (head.target.1≤head.target.2)=true from decide_eq_true (by omega)] using HeadTargetMath.geu head.target.2 head.target.1 targetBound startBound
  have inside : taken .geu (BitVec.ofNat 32 rawUsed) (BitVec.ofNat 32 head.target.2)=true := by
    simpa only [show decide (head.target.2≤rawUsed)=true from decide_eq_true (by have := h.contained.1;have := h.usedBound;omega)] using HeadTargetMath.geu rawUsed head.target.2 totalBound targetBound
  have different : BitVec.ofNat 32 head.target.2≠BitVec.ofNat 32 head.target.1 := by
    intro same
    have equal := congrArg BitVec.toNat same
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show head.target.2<2^32 by omega),Nat.mod_eq_of_lt (show head.target.1<2^32 by omega)] at equal
    omega
  have nonempty : taken .ne (BitVec.ofNat 32 head.target.2) (BitVec.ofNat 32 head.target.1)=true := by simp [taken,different]
  have stack : Memory.Block B sp 5232 := by
    have block := Memory.sub_block (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 60304) (m := 5232) StackBoard.available (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60304#32=sp by decide +kernel] using block
  obtain ⟨d,trace,pc,d31,d18,d12,d15,d29,d30,d5,d17,d21,d10,dr,csr⟩ := MainRequestTargetCore.contract B c ram sp (BitVec.ofNat 32 served) (BitVec.ofNat 32 rawUsed) (BitVec.ofNat 32 head.target.1) (BitVec.ofNat 32 head.target.2) rx
    h.pc h.stable.sp (by simpa only [show sp+3204#32=fp by decide +kernel] using h.stable.fp) h.pad h.used
    (by simpa only [show fp+88#32=sp+3292#32 by decide +kernel] using h.serve.servedWord)
    (by simpa only [show fp+60#32=sp+3264#32 by decide +kernel] using h.serve.capacity) h.targetStart h.targetEnd
    (by simpa only [show fp+56#32=sp+3260#32 by decide +kernel] using h.serve.rx) capacity order inside nonempty stack (by decide +kernel)
  let after := MainRequestCounter.memory ram sp (BitVec.ofNat 32 served) (BitVec.ofNat 32 rawUsed)
  have keep (rr : Reg) (safe : rr∈[2,8,9,19,20,22,23,24,25,26,27]) : d.get rr=c.get rr := by
    have ne : ∀ rr : Reg, rr∈[2,8,9,19,20,22,23,24,25,26,27] → rr≠31 ∧ rr≠18 ∧ rr≠12 ∧ rr≠15 ∧ rr≠29 ∧ rr≠30 ∧ rr≠5 ∧ rr≠17 ∧ rr≠21 ∧ rr≠10 := by decide +kernel
    obtain ⟨a,b,e,f,g,i,j,k,l,m⟩ := ne rr safe
    exact dr rr a b e f g i j k l m
  have stable : MainTransactionStable.At d after input s := by
    refine ⟨(keep 2 (by decide)).trans h.stable.sp,(keep 8 (by decide)).trans h.stable.fp,
      (keep 19 (by decide)).trans h.stable.uart,(keep 22 (by decide)).trans h.stable.one,
      h.stable.bound,?_,?_,?_,h.stable.invariant,h.stable.stack,?_⟩
    · have word := ViewFrame.word (MainRequestCounterMemory.frame ram sp (BitVec.ofNat 32 served) (BitVec.ofNat 32 rawUsed) 3288 4 (by decide) (Or.inl (by decide))) 0 (by decide)
      have kept : ramRead after (fp+84#32) .w=ramRead ram (fp+84#32) .w := by
        simpa only [BitVec.add_zero,show sp+3288#32=fp+84#32 by decide +kernel] using word
      exact kept.trans h.stable.filled
    · intro i
      have rxFrame := MainRequestCounterMemory.frame ram sp (BitVec.ofNat 32 served) (BitVec.ofNat 32 rawUsed) 132 2048 (by decide) (Or.inl (by decide))
      exact (show after (0x80ffec14#32+BitVec.ofNat 32 i.val)=ram (0x80ffec14#32+BitVec.ofNat 32 i.val) from by simpa only [show sp+132#32=0x80ffec14#32 by decide +kernel] using rxFrame ⟨i.val,by have := i.isLt;have := h.stable.bound;omega⟩).trans (h.stable.bytes i)
    · apply AppState.preserve ram after s h.stable.app
      simpa only [ViewFrame.Region,show sp+44#32=0x80ffebbc#32 by decide +kernel] using MainRequestCounterMemory.frame ram sp (BitVec.ofNat 32 served) (BitVec.ofNat 32 rawUsed) 44 25 (by decide) (Or.inl (by decide))
    · exact (congrArg Prod.fst csr).trans h.stable.masked
  have word (off : Nat) (bound : off+4≤3292) : ramRead after (sp+BitVec.ofNat 32 off) .w=ramRead ram (sp+BitVec.ofNat 32 off) .w := by
    have slot := ViewFrame.word (MainRequestCounterMemory.frame ram sp (BitVec.ofNat 32 served) (BitVec.ofNat 32 rawUsed) off 4 (by omega) (Or.inl bound)) 0 (by decide)
    simpa only [BitVec.add_zero] using slot
  have usedWord : ramRead after (fp+92#32) .w=BitVec.ofNat 32 rawUsed := by
    simpa only [show fp+92#32=sp+3296#32 by decide +kernel] using MainRequestCounterMemory.used ram sp (BitVec.ofNat 32 served) (BitVec.ofNat 32 rawUsed)
  have headView := MainCopyView.head (MainRequestCounterMemory.frame ram sp (BitVec.ofNat 32 served) (BitVec.ofNat 32 rawUsed) 3320 304 (by decide) (Or.inr (by decide))) head h.headView
  have array := MainNextArrayFrame.preserve h.array (MainRequestCounterMemory.frame ram sp (BitVec.ofNat 32 served) (BitVec.ofNat 32 rawUsed) 4248 264 (by decide) (Or.inr (by decide)))
  refine ⟨d,trace,⟨pc,stable,(keep 23 (by decide)).trans h.bank.future,(keep 26 (by decide)).trans h.bank.three,
    MainRequestCounterMemory.serve ram served _ h.serve,by have := h.countBound;omega,by omega,?_,d31,d12,d15,d29,d30,d5,d17,d21,d10,
    (keep 9 (by decide)).trans h.tag,(keep 27 (by decide)).trans h.low,(keep 20 (by decide)).trans h.start,
    (keep 24 (by decide)).trans h.used,(keep 25 (by decide)).trans h.endReg,usedWord,headView,array,
    (word 28 (by decide)).trans h.methodStart,(word 24 (by decide)).trans h.methodEnd,(word 36 (by decide)).trans h.targetStart,
    (word 32 (by decide)).trans h.targetEnd,(word 40 (by decide)).trans h.minor,h.bounds,h.kind,h.bodyBound,h.usedBound,h.available,h.contained⟩,csr⟩
  simpa only [←BitVec.ofNat_add] using d18
end E5R.Thermostat.StackRuntimeTarget
