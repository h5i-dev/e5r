import Projects.thermostat.RuntimeRouterEntry
import Projects.thermostat.MainRouteEnvelope
set_option autoImplicit false
namespace E5R.Thermostat.RuntimeRouteEnvelope
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := RuntimeRouterEntry.B
abbrev sp := RuntimeRouterEntry.sp
abbrev fp := RuntimeRouterEntry.fp
abbrev rx := RuntimeRouterEntry.rx

/-- Common live data across the real /temp route's three matcher calls.
    PCs, arguments, match results and captures remain separate proof outputs. -/
structure At (c : Core) (ram : Word → BitVec 8) (input : List (BitVec 8)) (s : Spec.Snapshot) (head : Head) (amount rawUsed served : Nat) (lowValue : Word) (close : Bool) : Prop where
  stable : MainTransactionStable.At c ram input s
  stored : RuntimeStored.At ram input head amount rawUsed
  serve : MainServeLayout.At ram served
  table : MainRouterTable.At ram
  futures : MainRouterFutures.At ram
  replyCapacity : ramRead ram 0x80fff9fc#32 .w=832#32
  closeByte : ram (sp+3304#32)=Encoding.boolByte close
  closeSpec : close=MainCloseSpec.mustClose head.minor served (RuntimeRequestSpans.raw input rawUsed) (RuntimeRequestInputs.entries head)
  two : c.get 18=2#32
  future : c.get 23=0x80fff9f0#32
  firstSlot : c.get 24=sp+3740#32
  secondSlot : c.get 25=sp+3784#32
  three : c.get 26=3#32
  low : c.get 27=lowValue
  countBound : served≤100
  positive : 0<served

theorem fromEntry {c ram input s head amount rawUsed served lowValue close}
    (h : RuntimeRouterEntry.At c ram input s head amount rawUsed served lowValue close) :
    At c ram input s head amount rawUsed served lowValue close :=
  ⟨h.stable,h.stored,h.serve,h.table,h.futures,h.replyCapacity,h.closeByte,h.closeSpec,h.two,
    h.future,h.firstSlot,h.secondSlot,h.three,h.low,h.countBound,h.positive⟩

theorem preserve {c d : Core} {before after : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount rawUsed served : Nat} {lowValue : Word} {close : Bool}
    (h : At c before input s head amount rawUsed served lowValue close)
    (regs : ∀ r : Reg, r∈[2,8,18,19,22,23,24,25,26,27] → d.get r=c.get r) (csr : d.sameCsr c)
    (live : ViewFrame.Region before after sp 3780)
    (futureFrames : ∀ route : Fin 5, ViewFrame.Region before after (MainRouterFutures.fp+BitVec.ofNat 32 (512+44*route.val)) 20) :
    At d after input s head amount rawUsed served lowValue close := by
  have region (off size : Nat) (bound : off+size≤3780) : ViewFrame.Region before after (sp+BitVec.ofNat 32 off) size := by
    intro i
    have byte := live ⟨off+i.val,by have := i.isLt;omega⟩
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using byte
  have future : ViewFrame.Region before after fp 96 := by
    simpa only [show sp+3204#32=fp by decide +kernel] using region 3204 96 (by decide)
  have stable : MainTransactionStable.At d after input s := by
    refine ⟨(regs 2 (by decide)).trans h.stable.sp,(regs 8 (by decide)).trans h.stable.fp,
      (regs 19 (by decide)).trans h.stable.uart,(regs 22 (by decide)).trans h.stable.one,h.stable.bound,
      (ViewFrame.word future 84 (by decide)).trans h.stable.filled,?_,?_,h.stable.invariant,h.stable.stack,?_⟩
    · intro i
      have byte := region 132 2048 (by decide) ⟨i.val,by have := i.isLt;have := h.stable.bound;omega⟩
      have atByte : after (rx+BitVec.ofNat 32 i.val)=before (rx+BitVec.ofNat 32 i.val) := by simpa only [show sp+132#32=rx by decide +kernel] using byte
      exact atByte.trans (h.stable.bytes i)
    · apply AppState.preserve before after s h.stable.app
      simpa only [ViewFrame.Region,show sp+44#32=0x80ffebbc#32 by decide +kernel] using region 44 25 (by decide)
    · exact (congrArg Prod.fst csr).trans h.stable.masked
  have flag : after (sp+3304#32)=Encoding.boolByte close := by
    have byte := region 3304 1 (by decide) ⟨0,by decide⟩
    simpa only [BitVec.add_zero] using byte.trans h.closeByte
  have table : MainRouterTable.At after := MainRouterTable.preserve h.table (by
    simpa only [show sp+72#32=0x80ffebd8#32 by decide +kernel] using region 72 60 (by decide))
  have cap : ramRead after 0x80fff9fc#32 .w=832#32 := by
    have word := ViewFrame.word (region 3692 4 (by decide)) 0 (by decide)
    simpa only [BitVec.add_zero,show sp+3692#32=0x80fff9fc#32 by decide +kernel] using word.trans h.replyCapacity
  exact ⟨stable,RuntimeStored.preserve h.stored (region 3312 376 (by decide)),MainServeLayout.preserve (MainServeMemoryFrames.whole future (by decide)) h.serve,
    table,MainRouterFutures.preserve h.futures futureFrames,cap,flag,h.closeSpec,(regs 18 (by decide)).trans h.two,(regs 23 (by decide)).trans h.future,
    (regs 24 (by decide)).trans h.firstSlot,(regs 25 (by decide)).trans h.secondSlot,
    (regs 26 (by decide)).trans h.three,(regs 27 (by decide)).trans h.low,h.countBound,h.positive⟩

/-- The real matcher save slots are below every live caller region. -/
theorem saved {c d : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount rawUsed served : Nat} {lowValue : Word} {close : Bool}
    (h : At c ram input s head amount rawUsed served lowValue close) (origin : Core)
    (regs : ∀ r : Reg, r∈[2,8,18,19,22,23,24,25,26,27] → d.get r=c.get r) (csr : d.sameCsr c) :
    At d (MainPathStateSave.memory ram origin) input s head amount rawUsed served lowValue close := by
  have frame (off size : Nat) (bound : off+size≤5232) : ViewFrame.Region ram (MainPathStateSave.memory ram origin) (sp+BitVec.ofNat 32 off) size := by
    intro i
    rw [MainPathStateSave.memory_eq]
    apply OuterSave.frame
    intro j
    have ne := FrameOffsets.ne 0x80ffeb30#32 (96+off) 0 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;omega) (by have := j.isLt;omega)
    simpa only [BitVec.ofNat_add,←BitVec.add_assoc,show 0x80ffeb30#32+96#32=sp by decide +kernel,BitVec.add_zero] using ne
  apply preserve h regs csr
  · simpa only [BitVec.add_zero] using frame 0 3780 (by decide)
  · intro route
    have region := frame (3716+44*route.val) 20 (by have := route.isLt;omega)
    have address : sp+BitVec.ofNat 32 (3716+44*route.val)=MainRouterFutures.fp+BitVec.ofNat 32 (512+44*route.val) := by
      rw [show 3716+44*route.val=3204+(512+44*route.val) by omega,BitVec.ofNat_add,←BitVec.add_assoc,show sp+3204#32=MainRouterFutures.fp by decide +kernel]
    rw [address] at region
    exact region

end E5R.Thermostat.RuntimeRouteEnvelope
