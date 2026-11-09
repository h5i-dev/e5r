import Projects.thermostat.RequestPayloadReady
import Projects.thermostat.StackBoard
set_option autoImplicit false
set_option maxRecDepth 4000
namespace E5R.Thermostat.StackRequestPayloadReady
open E5R E5R.Thermostat HttpRequestSpec RequestPayloadReady
abbrev B := StackBoard.board

theorem contract {c ram input s head amount rawUsed served low}
    (h : Entry c ram input s head amount rawUsed served low) :
    ∃ d, Quiet.Steps B img 460 ⟨c,ram⟩
      ⟨d,RequestPayloadFields.memory ram input head amount rawUsed (HeadCompletedView.framingTag head.framing) 0#32 low⟩ ∧
      RuntimeRequest.Ready d (RequestPayloadFields.memory ram input head amount rawUsed (HeadCompletedView.framingTag head.framing) 0#32 low)
        input s head amount rawUsed served ∧ d.sameCsr c := by
  have stack : Memory.Block B sp 5232 := by
    have block := Memory.sub_block StackBoard.available (off := 60304) (m := 5232) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60304#32=sp by decide +kernel] using block
  have originalStack : Memory.Block UartPlatform.board sp 5232 := by
    have block := Memory.sub_block h.stable.stack (off := 60304) (m := 5232) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60304#32=sp by decide +kernel] using block
  obtain ⟨d,trace,pc,minorReg,_,regs,csr⟩ := RequestPayloadCore.contract B c ram sp rx head.len (head.len+amount) rawUsed
    (MainRequestBuild.method input head) (rx+BitVec.ofNat 32 head.target.1) (MainRequestBuild.pathLength input head)
    (MainRequestBuild.queryPtr input head) (MainRequestBuild.queryLength input head) (HeadCompletedView.framingTag head.framing) 0#32 low
    (BitVec.ofNat 32 head.method.1) (BitVec.ofNat 32 head.method.2) (BitVec.ofNat 32 head.target.1) (BitVec.ofNat 32 head.target.2) (BitVec.ofNat 32 head.minor)
    h.pc h.stable.sp h.stable.fp h.start h.finish h.consumed h.rxReg h.method h.path h.pathLength h.query h.queryLength h.tag h.pad h.lowReg
    h.methodStart h.methodEnd h.targetStart h.targetEnd h.minor (by omega) h.usedBound.1 (by have := h.stable.bound;have := h.usedBound.2;omega) stack (by decide)
  let after := RequestPayloadFields.memory ram input head amount rawUsed (HeadCompletedView.framingTag head.framing) 0#32 low
  have frame (off size : Nat) (bound : off+size≤5232) (apart : off+size≤3312 ∨ 3685≤off) :
      ViewFrame.Region ram after (sp+BitVec.ofNat 32 off) size := RequestPayloadMemory.frame ram sp rx head.len (head.len+amount) rawUsed
        (MainRequestBuild.method input head) (rx+BitVec.ofNat 32 head.target.1) (MainRequestBuild.pathLength input head)
        (MainRequestBuild.queryPtr input head) (MainRequestBuild.queryLength input head) (HeadCompletedView.framingTag head.framing) 0#32 low
        (BitVec.ofNat 32 head.method.1) (BitVec.ofNat 32 head.method.2) (BitVec.ofNat 32 head.target.1) (BitVec.ofNat 32 head.target.2) (BitVec.ofNat 32 head.minor) off size bound apart
  have keep (r : Reg) (safe : r∈[2,8,18,19,22,23,26]) : d.get r=c.get r := by
    have yes : ∀ r : Reg, r∈[2,8,18,19,22,23,26] → r∈MainRequestSaved.regs ∧ r≠20 := by decide +kernel
    obtain ⟨member,ne⟩ := yes r safe
    exact regs r member ne
  have future : ViewFrame.Region ram after fp 96 := by
    simpa only [show sp+3204#32=fp by decide +kernel] using frame 3204 96 (by decide) (Or.inl (by decide))
  have stable : MainTransactionStable.At d after input s := by
    refine ⟨(keep 2 (by decide)).trans h.stable.sp,(keep 8 (by decide)).trans h.stable.fp,
      (keep 19 (by decide)).trans h.stable.uart,(keep 22 (by decide)).trans h.stable.one,h.stable.bound,
      (ViewFrame.word future 84 (by decide)).trans h.stable.filled,?_,?_,h.stable.invariant,h.stable.stack,(congrArg Prod.fst csr).trans h.stable.masked⟩
    · intro i
      have region := frame 132 2048 (by decide) (Or.inl (by decide))
      exact (region ⟨i.val,by have := i.isLt;have := h.stable.bound;omega⟩).trans (h.stable.bytes i)
    · apply AppState.preserve ram after s h.stable.app
      simpa only [ViewFrame.Region,show sp+44#32=0x80ffebbc#32 by decide +kernel] using frame 44 25 (by decide) (Or.inl (by decide))
  have fields := RequestPayloadFields.contract ram input head amount rawUsed (HeadCompletedView.framingTag head.framing) 0#32 low h.usedBound.1 (by have := h.usedBound.2;have := h.stable.bound;omega) originalStack
  have headView := RequestPayloadHead.contract ram input head amount rawUsed low h.kind h.bounds.version originalStack h.array
  refine ⟨d,trace,⟨pc,stable,(keep 23 (by decide)).trans h.future,(keep 26 (by decide)).trans h.three,
    MainServeLayout.preserve (MainServeMemoryFrames.whole future (by decide)) h.serve,h.countBound,h.positive,(keep 18 (by decide)).trans h.countReg,
    minorReg,(ViewFrame.word future 92 (by decide)).trans h.usedWord,headView,fields,?_,h.bounds,h.bodyBound,h.usedBound,h.contained⟩,csr⟩
  exact fields.method.trans (MainRequestByteValue.ofNat _ (by have := MainRequestByteValue.tag (MainMethodSpec.decode (MainMethodBytes.token input head.method.2));omega))
end E5R.Thermostat.StackRequestPayloadReady
