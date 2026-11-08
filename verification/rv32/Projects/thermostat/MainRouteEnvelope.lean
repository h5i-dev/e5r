import Projects.thermostat.MainTempFirst
set_option autoImplicit false
namespace E5R.Thermostat.MainRouteEnvelope
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := MainRouterEntry.B
abbrev sp := MainRouterEntry.sp
abbrev fp := MainRouterEntry.fp
abbrev rx := MainRouterEntry.rx

/-- Common live data across the real /temp route's three matcher calls.
    PCs, arguments, match results and captures remain separate proof outputs. -/
structure At (c : Core) (ram : Word → BitVec 8) (input : List (BitVec 8)) (s : Spec.Snapshot) (head : Head) (amount served : Nat) (close : Bool) : Prop where
  stable : MainTransactionStable.At c ram input s
  stored : MainRequestStored.At ram input head amount
  serve : MainServeLayout.At ram served
  table : MainRouterTable.At ram
  futures : MainRouterFutures.At ram
  replyCapacity : ramRead ram 0x80fff9fc#32 .w=832#32
  closeByte : ram (sp+3304#32)=Encoding.boolByte close
  closeSpec : close=MainCloseSpec.mustClose head.minor served (MainRequestSpans.raw input head amount) (MainRequestInputs.entries head)
  two : c.get 18=2#32

theorem fromFirst {c ram input s head amount served close} (h : MainTempFirst.Ready c ram input s head amount served close) :
    At c ram input s head amount served close := ⟨h.stable,h.stored,h.serve,h.table,h.futures,h.replyCapacity,h.closeByte,h.closeSpec,h.two⟩

theorem preserve {c d : Core} {before after : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat} {close : Bool}
    (h : At c before input s head amount served close)
    (regs : ∀ r : Reg, r∈[2,8,18,19,22] → d.get r=c.get r) (csr : d.sameCsr c)
    (live : ViewFrame.Region before after sp 3780)
    (futureFrames : ∀ route : Fin 5, ViewFrame.Region before after (MainRouterFutures.fp+BitVec.ofNat 32 (512+44*route.val)) 20) :
    At d after input s head amount served close := by
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
  exact ⟨stable,MainRequestStored.preserve h.stored (region 3312 376 (by decide)),MainServeLayout.preserve (MainServeMemoryFrames.whole future (by decide)) h.serve,
    table,MainRouterFutures.preserve h.futures futureFrames,cap,flag,h.closeSpec,(regs 18 (by decide)).trans h.two⟩

/-- The real matcher save slots are below every live caller region. -/
theorem saved {c d : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat} {close : Bool}
    (h : At c ram input s head amount served close) (origin : Core)
    (regs : ∀ r : Reg, r∈[2,8,18,19,22] → d.get r=c.get r) (csr : d.sameCsr c) :
    At d (MainPathStateSave.memory ram origin) input s head amount served close := by
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

/-- The second/third matcher receive the same actual parsed /temp bytes. -/
theorem temp_view {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat} {close : Bool}
    (h : At c ram input s head amount served close) (route : MainRequestSpans.path input head=WireSpec.ascii "/temp") :
    Bytes.Span B ram (rx+BitVec.ofNat 32 head.target.1) (WireSpec.ascii "/temp") ∧
    MainQuerySpec.pathLength (MainQuerySpec.bytes input) head.target.1 head.target.2=5 ∧
    WordRegions.Disjoint (rx+BitVec.ofNat 32 head.target.1) 5 0x80ffeb30#32 96 := by
  have whole : Bytes.Span B ram rx input := by
    have block := Memory.sub_block h.stable.stack (off := 60436) (m := input.length)
      (by have := h.stored.available;have := h.stored.bounds.length.1;omega) (by have := h.stable.bound;omega)
    have rxblock : Memory.Block B rx input.length := by
      simpa only [show 0x80ff0000#32+60436#32=rx by decide +kernel] using block
    exact Bytes.of_block B ram rx input rxblock (by have := h.stable.bound;omega) h.stable.bytes
  have limits : head.target.1≤MainQuerySpec.position (MainQuerySpec.bytes input) head.target.1 head.target.2 ∧
      MainQuerySpec.position (MainQuerySpec.bytes input) head.target.1 head.target.2≤input.length := by
    have bounds := MainQuerySpec.bounds (MainQuerySpec.bytes input) head.target.1 head.target.2 (by have := h.stored.bounds.target.2.1;omega)
    have := h.stored.contained.1
    have := h.stored.available
    omega
  have pathBytes : Bytes.Span B ram (rx+BitVec.ofNat 32 head.target.1) (WireSpec.ascii "/temp") := by
    have span := Bytes.subspan whole _ _ limits
    change Bytes.Span B ram (rx+BitVec.ofNat 32 head.target.1) (MainRequestSpans.path input head) at span
    rw [route] at span
    exact span
  have length : MainQuerySpec.pathLength (MainQuerySpec.bytes input) head.target.1 head.target.2=5 := by
    have size := Bytes.subspan_length input _ _ limits
    change (MainRequestSpans.path input head).length=MainQuerySpec.pathLength (MainQuerySpec.bytes input) head.target.1 head.target.2 at size
    rw [route] at size
    exact size.symm
  refine ⟨pathBytes,length,?_⟩
  intro i j
  have start : head.target.1+5≤input.length := by
    have := limits.2
    change MainQuerySpec.position (MainQuerySpec.bytes input) head.target.1 head.target.2-head.target.1=5 at length
    omega
  have separated := WordZero.separated 0x80ffeb30#32 rx 96 2048 (by decide +kernel) (by decide +kernel) j
    ⟨head.target.1+i.val,by have := i.isLt;have := h.stable.bound;omega⟩
  rw [BitVec.add_assoc,←BitVec.ofNat_add]
  exact Ne.symm separated
end E5R.Thermostat.MainRouteEnvelope
