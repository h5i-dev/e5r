import Projects.thermostat.MainServeNext
import Projects.thermostat.StackBoard
set_option autoImplicit false
set_option maxRecDepth 4000
namespace E5R.Thermostat.StackMainServeNext
open E5R E5R.Thermostat HttpRequestSpec MainServeNext
abbrev B := StackBoard.board

theorem contract {c ram input s head amount served} (h : MainNextLength.Ready c ram input s head amount)
    (bank : MainGprBank.At c) (serve : MainServeLayout.At ram served) (countBound : served<100)
    (payload : MainNextLengthPayloadWords.At ram sp)
    (contained : head.target.2<head.len ∧ (∀ entry∈head.headers, MainHeadBounds.FieldAt head.len entry)) :
    ∃ d, Quiet.Steps B img 755 ⟨c,ram⟩ ⟨d,MainServeNextMemory.memory ram sp⟩ ∧
      Ready d (MainServeNextMemory.memory ram sp) input s head amount served ∧ d.sameCsr c := by
  have stack : Memory.Block B sp 5232 := by
    have block := Memory.sub_block (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 60304) (m := 5232) StackBoard.available (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60304#32=sp by decide +kernel] using block
  obtain ⟨d,trace,pc,regs,csr⟩ := MainServeNextCore.contract B c ram sp h.pc h.stable.sp
    (by simpa only [show sp+3204#32=fp by decide +kernel] using h.stable.fp) h.tag h.pad bank.minusOne h.stable.one payload stack (by decide +kernel)
  have future : ViewFrame.Region ram (MainServeNextMemory.memory ram sp) fp 448 := by
    simpa only [show sp+3204#32=fp by decide +kernel] using MainServeNextMemory.frame ram sp 3204 448 (by decide)
  have sub (off size : Nat) (bound : off+size≤448) : ViewFrame.Region ram (MainServeNextMemory.memory ram sp) (fp+BitVec.ofNat 32 off) size := by
    intro i
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add,Nat.add_assoc] using future ⟨off+i.val,by have := i.isLt;omega⟩
  have layoutAfter := MainHeaderLayoutParts.preserve h.stable.layout
    (by simpa only [BitVec.add_zero] using sub 0 116 (by decide)) (sub 432 12 (by decide))
  have stable : MainHeaderLoopTwo.Stable d (MainServeNextMemory.memory ram sp) input s := by
    refine ⟨(regs 2 (by decide)).trans h.stable.sp,(regs 8 (by decide)).trans h.stable.fp,
      (regs 19 (by decide)).trans h.stable.uart,(regs 22 (by decide)).trans h.stable.one,
      layoutAfter,?_,?_,h.stable.invariant,h.stable.stack,?_⟩
    · intro i
      have rx := MainServeNextMemory.frame ram sp 132 2048 (by decide)
      exact (show MainServeNextMemory.memory ram sp (0x80ffec14#32+BitVec.ofNat 32 i.val)=ram (0x80ffec14#32+BitVec.ofNat 32 i.val) from by simpa only [show sp+132#32=0x80ffec14#32 by decide +kernel] using rx ⟨i.val,by have := i.isLt;have := h.stable.layout.bound;omega⟩).trans (h.stable.bytes i)
    · apply AppState.preserve ram _ s h.stable.app
      simpa only [ViewFrame.Region,show sp+44#32=0x80ffebbc#32 by decide +kernel] using MainServeNextMemory.frame ram sp 44 25 (by decide)
    · exact (congrArg Prod.fst csr).trans h.stable.masked
  have bankAfter : MainGprBank.At d := ⟨(regs 21 (by decide)).trans bank.minusOne,(regs 23 (by decide)).trans bank.future,(regs 26 (by decide)).trans bank.three⟩
  have serveAfter := MainServeLayout.preserve (MainServeMemoryFrames.whole future (by decide)) serve
  have word (off : Nat) (bound : off+4≤3652) : ramRead (MainServeNextMemory.memory ram sp) (sp+BitVec.ofNat 32 off) .w=ramRead ram (sp+BitVec.ofNat 32 off) .w := by
    have slot := ViewFrame.word (MainServeNextMemory.frame ram sp off 4 bound) 0 (by decide)
    simpa only [BitVec.add_zero] using slot
  have headView := MainCopyView.head (MainServeNextMemory.frame ram sp 3320 304 (by decide)) head h.headView
  exact ⟨d,trace,⟨pc,stable,bankAfter,serveAfter,countBound,(regs 9 (by decide)).trans h.tag,(regs 18 (by decide)).trans h.pad,
    (regs 27 (by decide)).trans h.low,(regs 20 (by decide)).trans h.start,(regs 24 (by decide)).trans h.used,(regs 25 (by decide)).trans h.endReg,
    headView,MainServeNextMemory.array ram sp head stack h.array,(word 28 (by decide)).trans h.methodStart,(word 24 (by decide)).trans h.methodEnd,
    (word 36 (by decide)).trans h.targetStart,(word 32 (by decide)).trans h.targetEnd,(word 40 (by decide)).trans h.minor,
    h.bounds,h.kind,h.available,contained⟩,csr⟩
end E5R.Thermostat.StackMainServeNext
