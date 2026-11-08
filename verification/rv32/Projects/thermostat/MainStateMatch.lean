import Projects.thermostat.MainRouterEntry
import Projects.thermostat.MainPathState
import Projects.thermostat.MainRequestSpans
import Projects.thermostat.FrameOffsets
import Projects.thermostat.RomSpan
set_option autoImplicit false
set_option maxRecDepth 6000
namespace E5R.Thermostat.MainStateMatch
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := MainRouterEntry.B
abbrev sp := MainRouterEntry.sp
abbrev fp := MainRouterEntry.fp
abbrev rx := MainRouterEntry.rx

/-- Return from the actual first route match, retaining every live caller view. -/
structure Ready (c : Core) (ram : Word → BitVec 8) (input : List (BitVec 8)) (s : Spec.Snapshot) (head : Head) (amount served : Nat) (close : Bool) : Prop where
  pc : c.pc=0x800013d2#32
  stable : MainTransactionStable.At c ram input s
  stored : MainRequestStored.At ram input head amount
  serve : MainServeLayout.At ram served
  table : MainRouterTable.At ram
  futureWords : ∀ i : Fin 5, ramRead ram (fp+BitVec.ofNat 32 (688+4*i.val)) .w=
    (match i.val with | 0 => 0x80ffebf8#32 | 1 => 0x80fff880#32 | 2 => 0x80ffebbc#32 | 3 => 0x80fff4d4#32 | _ => 832#32)
  closeByte : ram (sp+3304#32)=Encoding.boolByte close
  closeSpec : close=MainCloseSpec.mustClose head.minor served (MainRequestSpans.raw input head amount) (MainRequestInputs.entries head)
  result : c.get 10=1#32
  captures : c.get 11=0#32
  two : c.get 18=2#32
  future : c.get 23=0x80fff9f0#32
  firstSlot : c.get 24=sp+3740#32
  secondSlot : c.get 25=sp+3784#32
  three : c.get 26=3#32
  low : c.get 27=BitVec.ofNat 32 amount

theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat} {close : Bool}
    (h : MainRouterEntry.At c ram input s head amount served close)
    (route : MainRequestSpans.path input head=WireSpec.ascii "/state") :
    ∃ d, Quiet.Steps B img 187 ⟨c,ram⟩ ⟨d,MainPathStateSave.memory ram c⟩ ∧
      Ready d (MainPathStateSave.memory ram c) input s head amount served close ∧ d.sameCsr c := by
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
  have pathBytes : Bytes.Span B ram (rx+BitVec.ofNat 32 head.target.1) (WireSpec.ascii "/state") := by
    have span := Bytes.subspan whole _ _ limits
    change Bytes.Span B ram (rx+BitVec.ofNat 32 head.target.1) (MainRequestSpans.path input head) at span
    rw [route] at span
    exact span
  have length : MainQuerySpec.pathLength (MainQuerySpec.bytes input) head.target.1 head.target.2=6 := by
    have size := Bytes.subspan_length input _ _ limits
    change (MainRequestSpans.path input head).length=MainQuerySpec.pathLength (MainQuerySpec.bytes input) head.target.1 head.target.2 at size
    rw [route] at size
    exact size.symm
  have h13 : c.get 13=6#32 := by
    rw [h.pathLength]
    change BitVec.ofNat 32 (MainQuerySpec.pathLength (MainQuerySpec.bytes input) head.target.1 head.target.2)=6#32
    rw [length]
  have pattern : ReadBytes.Span B img ram 0x80005b83#32 (WireSpec.ascii "/state") :=
    ReadBytes.of_data B ram _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have stack : Memory.Block B 0x80ffeb50#32 64 := by
    have block := Memory.sub_block h.stable.stack (off := 60240) (m := 64) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60240#32=0x80ffeb50#32 by decide +kernel] using block
  have separate : WordRegions.Disjoint (rx+BitVec.ofNat 32 head.target.1) 6 0x80ffeb30#32 96 := by
    intro i j
    have start : head.target.1+6≤input.length := by
      have := limits.2
      change MainQuerySpec.position (MainQuerySpec.bytes input) head.target.1 head.target.2-head.target.1=6 at length
      omega
    have separated := WordZero.separated 0x80ffeb30#32 rx 96 2048 (by decide +kernel) (by decide +kernel) j
      ⟨head.target.1+i.val,by have := i.isLt;have := h.stable.bound;omega⟩
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    exact Ne.symm separated
  obtain ⟨d,steps,pd,result,captures,keep,csr⟩ := MainPathState.contract B c ram _ _ h.pc h.stable.sp h.ret h.pattern h.patternLength h.path h13 h.params stack pattern pathBytes separate
  let after := MainPathStateSave.memory ram c
  have frame (off size : Nat) (bound : off+size≤5232) : ViewFrame.Region ram after (sp+BitVec.ofNat 32 off) size := by
    intro i
    dsimp only [after]
    rw [MainPathStateSave.memory_eq]
    apply OuterSave.frame
    intro j
    have ne := FrameOffsets.ne 0x80ffeb30#32 (96+off) 0 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;omega) (by have := j.isLt;omega)
    simpa only [BitVec.ofNat_add,←BitVec.add_assoc,show 0x80ffeb30#32+96#32=sp by decide +kernel,BitVec.add_zero] using ne
  have future : ViewFrame.Region ram after fp 96 := by simpa only [show sp+3204#32=fp by decide +kernel] using frame 3204 96 (by decide)
  have stable : MainTransactionStable.At d after input s := by
    refine ⟨(keep 2 (by decide)).trans h.stable.sp,(keep 8 (by decide)).trans h.stable.fp,
      (keep 19 (by decide)).trans h.stable.uart,(keep 22 (by decide)).trans h.stable.one,h.stable.bound,
      (ViewFrame.word future 84 (by decide)).trans h.stable.filled,?_,?_,h.stable.invariant,h.stable.stack,?_⟩
    · intro i
      have byte := frame 132 2048 (by decide) ⟨i.val,by have := i.isLt;have := h.stable.bound;omega⟩
      have atByte : after (rx+BitVec.ofNat 32 i.val)=ram (rx+BitVec.ofNat 32 i.val) := by simpa only [show sp+132#32=rx by decide +kernel] using byte
      exact atByte.trans (h.stable.bytes i)
    · apply AppState.preserve ram after s h.stable.app
      simpa only [ViewFrame.Region,show sp+44#32=0x80ffebbc#32 by decide +kernel] using frame 44 25 (by decide)
    · exact (congrArg Prod.fst csr).trans h.stable.masked
  have flag : after (sp+3304#32)=Encoding.boolByte close := by
    have byte := frame 3304 1 (by decide) ⟨0,by decide⟩
    simpa only [BitVec.add_zero] using byte.trans h.closeByte
  have table : MainRouterTable.At after := MainRouterTable.preserve h.table (by
    simpa only [show sp+72#32=0x80ffebd8#32 by decide +kernel] using frame 72 60 (by decide))
  have futureWords : ∀ i : Fin 5, ramRead after (fp+BitVec.ofNat 32 (688+4*i.val)) .w=
      (match i.val with | 0 => 0x80ffebf8#32 | 1 => 0x80fff880#32 | 2 => 0x80ffebbc#32 | 3 => 0x80fff4d4#32 | _ => 832#32) := by
    intro i
    have region : ViewFrame.Region ram after fp 708 := by
      simpa only [show sp+3204#32=fp by decide +kernel] using frame 3204 708 (by decide)
    exact (ViewFrame.word region (688+4*i.val) (by have := i.isLt;omega)).trans (h.futureWords i)
  exact ⟨d,steps,⟨pd,stable,MainRequestStored.preserve h.stored (frame 3312 376 (by decide)),
    MainServeLayout.preserve (MainServeMemoryFrames.whole future (by decide)) h.serve,table,futureWords,flag,h.closeSpec,result,captures,
    (keep 18 (by decide)).trans h.two,(keep 23 (by decide)).trans h.future,(keep 24 (by decide)).trans h.firstSlot,
    (keep 25 (by decide)).trans h.secondSlot,(keep 26 (by decide)).trans h.three,(keep 27 (by decide)).trans h.low⟩,csr⟩
end E5R.Thermostat.MainStateMatch
