import Projects.thermostat.RuntimeNext
import Projects.thermostat.StackBoard
set_option autoImplicit false
set_option maxRecDepth 4000
namespace E5R.Thermostat.StackRuntimeNext
open E5R E5R.Thermostat HttpRequestSpec RuntimeNext
abbrev B := StackBoard.board

theorem contract {c ram input s head amount rawUsed served lowValue}
    (h : Entry c ram input s head amount rawUsed served lowValue) :
    ∃ d, Quiet.Steps B img 755 ⟨c,ram⟩ ⟨d,RejectNextCore.memory ram sp⟩ ∧
      Ready d (RejectNextCore.memory ram sp) input s head amount rawUsed served lowValue ∧ d.sameCsr c := by
  have stack : Memory.Block B sp 5232 := by
    have block := Memory.sub_block StackBoard.available (off := 60304) (m := 5232) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60304#32=sp by decide +kernel] using block
  have originalStack : Memory.Block UartPlatform.board sp 5232 := by
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
    view,NextFramingMemory.array ram sp head originalStack h.array,(word 28 (by decide)).trans h.methodStart,(word 24 (by decide)).trans h.methodEnd,
    (word 36 (by decide)).trans h.targetStart,(word 32 (by decide)).trans h.targetEnd,(word 40 (by decide)).trans h.minor,
    h.bounds,h.kind,h.bodyBound,h.usedBound,h.available,h.contained⟩,csr⟩
end E5R.Thermostat.StackRuntimeNext
