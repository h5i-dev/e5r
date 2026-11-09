import Projects.thermostat.NextFramingMemory
import Projects.thermostat.RuntimeRequest
set_option autoImplicit false
namespace E5R.Thermostat.RuntimeNext
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board
abbrev sp := 0x80ffeb90#32
abbrev fp := 0x80fff814#32
structure Ready (c : Core) (ram : Word → BitVec 8) (input : List (BitVec 8)) (s : Spec.Snapshot) (head : Head) (amount rawUsed served : Nat) (lowValue : Word) : Prop where
  pc : c.pc=0x80000b50#32
  stable : MainTransactionStable.At c ram input s
  bank : MainGprBank.At c
  serve : MainServeLayout.At ram served
  countBound : served<100
  tag : c.get 9=HeadCompletedView.framingTag head.framing
  pad : c.get 18=0#32
  low : c.get 27=lowValue
  start : c.get 20=BitVec.ofNat 32 head.len
  used : c.get 24=BitVec.ofNat 32 rawUsed
  endReg : c.get 25=BitVec.ofNat 32 (head.len+amount)
  headView : HeadCompletedView.At ram (sp+3320#32) head
  array : MainNextArrayView.At ram (sp+4248#32) head
  methodStart : ramRead ram (sp+28#32) .w=BitVec.ofNat 32 head.method.1
  methodEnd : ramRead ram (sp+24#32) .w=BitVec.ofNat 32 head.method.2
  targetStart : ramRead ram (sp+36#32) .w=BitVec.ofNat 32 head.target.1
  targetEnd : ramRead ram (sp+32#32) .w=BitVec.ofNat 32 head.target.2
  minor : ramRead ram (sp+40#32) .w=BitVec.ofNat 32 head.minor
  bounds : MainHeadAcceptedBounds.At 1024 1024 head
  kind : head.framing=.empty ∨ head.framing=.chunked
  bodyBound : amount≤1024
  usedBound : head.len+amount≤rawUsed
  available : rawUsed≤input.length
  contained : head.target.2<head.len ∧ (∀ entry∈head.headers, MainHeadBounds.FieldAt head.len entry)

structure Entry (c : Core) (ram : Word → BitVec 8) (input : List (BitVec 8)) (s : Spec.Snapshot) (head : Head) (amount rawUsed served : Nat) (lowValue : Word) : Prop where
  pc : c.pc=0x80000a9a#32
  stable : MainTransactionStable.At c ram input s
  bank : MainGprBank.At c
  serve : MainServeLayout.At ram served
  countBound : served<100
  tag : c.get 9=HeadCompletedView.framingTag head.framing
  pad : c.get 18=0#32
  low : c.get 27=lowValue
  start : c.get 20=BitVec.ofNat 32 head.len
  used : c.get 24=BitVec.ofNat 32 rawUsed
  endReg : c.get 25=BitVec.ofNat 32 (head.len+amount)
  headView : HeadCompletedView.At ram (sp+3320#32) head
  array : MainNextArrayView.At ram (sp+4904#32) head
  methodStart : ramRead ram (sp+28#32) .w=BitVec.ofNat 32 head.method.1
  methodEnd : ramRead ram (sp+24#32) .w=BitVec.ofNat 32 head.method.2
  targetStart : ramRead ram (sp+36#32) .w=BitVec.ofNat 32 head.target.1
  targetEnd : ramRead ram (sp+32#32) .w=BitVec.ofNat 32 head.target.2
  minor : ramRead ram (sp+40#32) .w=BitVec.ofNat 32 head.minor
  bounds : MainHeadAcceptedBounds.At 1024 1024 head
  kind : head.framing=.empty ∨ head.framing=.chunked
  bodyBound : amount≤1024
  usedBound : head.len+amount≤rawUsed
  available : rawUsed≤input.length
  contained : head.target.2<head.len ∧ (∀ entry∈head.headers, MainHeadBounds.FieldAt head.len entry)


/-- The actual successful Next staging retains each original framing and
    relocates the real header array; no unused payload bytes are prescribed. -/
theorem contract {c ram input s head amount rawUsed served lowValue}
    (h : Entry c ram input s head amount rawUsed served lowValue) :
    ∃ d, Quiet.Steps B img 755 ⟨c,ram⟩ ⟨d,RejectNextCore.memory ram sp⟩ ∧
      Ready d (RejectNextCore.memory ram sp) input s head amount rawUsed served lowValue ∧ d.sameCsr c := by
  have stack : Memory.Block B sp 5232 := by
    have block := Memory.sub_block h.stable.stack (off := 60304) (m := 5232) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60304#32=sp by decide +kernel] using block
  obtain ⟨d,trace,pc,regs,csr,_⟩ := NextFramingCore.contract B c ram sp head.framing h.pc h.stable.sp
    (by simpa only [show sp+3204#32=fp by decide +kernel] using h.stable.fp) h.tag h.pad h.bank.minusOne h.stable.one stack (by decide)
  let after := RejectNextCore.memory ram sp
  have future : ViewFrame.Region ram after fp 96 := by
    simpa only [show sp+3204#32=fp by decide +kernel] using NextFramingMemory.frame ram sp 3204 96 (by decide)
  have stable : MainTransactionStable.At d after input s := by
    refine ⟨(regs 2 (by decide)).trans h.stable.sp,(regs 8 (by decide)).trans h.stable.fp,
      (regs 19 (by decide)).trans h.stable.uart,(regs 22 (by decide)).trans h.stable.one,h.stable.bound,
      (ViewFrame.word future 84 (by decide)).trans h.stable.filled,?_,?_,h.stable.invariant,h.stable.stack,(congrArg Prod.fst csr).trans h.stable.masked⟩
    · intro i
      have region := NextFramingMemory.frame ram sp 132 2048 (by decide)
      exact (region ⟨i.val,by have := i.isLt;have := h.stable.bound;omega⟩).trans (h.stable.bytes i)
    · apply AppState.preserve ram after s h.stable.app
      simpa only [ViewFrame.Region,show sp+44#32=0x80ffebbc#32 by decide +kernel] using NextFramingMemory.frame ram sp 44 25 (by decide)
  have bank := MainGprBank.preserve (fun rr safe => regs rr (by
    have subset : ∀ rr : Reg, rr∈[21,23,26] → rr∈MainSavedGpr.regs := by decide +kernel
    exact subset rr safe)) h.bank
  have word (off : Nat) (bound : off+4≤3652) : ramRead after (sp+BitVec.ofNat 32 off) .w=ramRead ram (sp+BitVec.ofNat 32 off) .w := by
    simpa only [BitVec.add_zero] using ViewFrame.word (NextFramingMemory.frame ram sp off 4 bound) 0 (by decide)
  have view := MainCopyView.head (NextFramingMemory.frame ram sp 3320 304 (by decide)) head h.headView
  exact ⟨d,trace,⟨pc,stable,bank,MainServeLayout.preserve (MainServeMemoryFrames.whole future (by decide)) h.serve,h.countBound,
    (regs 9 (by decide)).trans h.tag,(regs 18 (by decide)).trans h.pad,(regs 27 (by decide)).trans h.low,
    (regs 20 (by decide)).trans h.start,(regs 24 (by decide)).trans h.used,(regs 25 (by decide)).trans h.endReg,
    view,NextFramingMemory.array ram sp head stack h.array,(word 28 (by decide)).trans h.methodStart,(word 24 (by decide)).trans h.methodEnd,
    (word 36 (by decide)).trans h.targetStart,(word 32 (by decide)).trans h.targetEnd,(word 40 (by decide)).trans h.minor,
    h.bounds,h.kind,h.bodyBound,h.usedBound,h.available,h.contained⟩,csr⟩
end E5R.Thermostat.RuntimeNext
