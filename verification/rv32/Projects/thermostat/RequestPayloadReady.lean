import Projects.thermostat.RequestPayloadHead
import Projects.thermostat.RuntimeRequestInputs
set_option autoImplicit false
set_option maxRecDepth 4000
namespace E5R.Thermostat.RequestPayloadReady
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board
abbrev sp := RuntimeRequest.sp
abbrev fp := RuntimeRequest.fp
abbrev rx := RuntimeRequest.rx

/-- Arguments at the real common Request-construction entry. The predecessor
    must derive these from actual Next/counter/query/method execution. Encoded
    rawUsed, decoded amount, original framing and unused payload stay distinct. -/
structure Entry (c : Core) (ram : Word → BitVec 8) (input : List (BitVec 8)) (s : Spec.Snapshot)
    (head : Head) (amount rawUsed served : Nat) (low : Word) : Prop where
  pc : c.pc=0x80001160#32
  stable : MainTransactionStable.At c ram input s
  future : c.get 23=0x80fff9f0#32
  three : c.get 26=3#32
  serve : MainServeLayout.At ram served
  countBound : served≤100
  positive : 0<served
  countReg : c.get 18=BitVec.ofNat 32 served
  method : c.get 14=MainRequestBuild.method input head
  path : c.get 10=rx+BitVec.ofNat 32 head.target.1
  pathLength : c.get 28=MainRequestBuild.pathLength input head
  query : c.get 12=MainRequestBuild.queryPtr input head
  queryLength : c.get 13=MainRequestBuild.queryLength input head
  tag : c.get 9=HeadCompletedView.framingTag head.framing
  pad : c.get 31=0#32
  lowReg : c.get 27=low
  start : c.get 20=BitVec.ofNat 32 head.len
  finish : c.get 25=BitVec.ofNat 32 (head.len+amount)
  consumed : c.get 24=BitVec.ofNat 32 rawUsed
  rxReg : c.get 21=rx
  methodStart : c.get 7=BitVec.ofNat 32 head.method.1
  methodEnd : c.get 11=BitVec.ofNat 32 head.method.2
  targetStart : c.get 29=BitVec.ofNat 32 head.target.1
  targetEnd : c.get 30=BitVec.ofNat 32 head.target.2
  minor : ramRead ram (sp+40#32) .w=BitVec.ofNat 32 head.minor
  usedWord : ramRead ram (fp+92#32) .w=BitVec.ofNat 32 rawUsed
  array : MainNextArrayView.At ram (sp+4248#32) head
  bounds : MainHeadAcceptedBounds.At 1024 1024 head
  bodyBound : amount≤1024
  usedBound : head.len+amount≤rawUsed ∧ rawUsed≤input.length
  kind : head.framing=.empty ∨ head.framing=.chunked
  contained : head.target.2<head.len ∧ (∀ entry∈head.headers, MainHeadBounds.FieldAt head.len entry)

/-- Every actual common constructor instruction establishes the broader
    Request view and real Header/path/body inputs. No finished Request fields
    or canonical unused payload bytes are assumed at its entry. -/
theorem contract {c ram input s head amount rawUsed served low}
    (h : Entry c ram input s head amount rawUsed served low) :
    ∃ d, Quiet.Steps B img 460 ⟨c,ram⟩
      ⟨d,RequestPayloadFields.memory ram input head amount rawUsed (HeadCompletedView.framingTag head.framing) 0#32 low⟩ ∧
      RuntimeRequest.Ready d (RequestPayloadFields.memory ram input head amount rawUsed (HeadCompletedView.framingTag head.framing) 0#32 low)
        input s head amount rawUsed served ∧ d.sameCsr c := by
  have stack : Memory.Block B sp 5232 := by
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
  have fields := RequestPayloadFields.contract ram input head amount rawUsed (HeadCompletedView.framingTag head.framing) 0#32 low h.usedBound.1 (by have := h.usedBound.2;have := h.stable.bound;omega) stack
  have headView := RequestPayloadHead.contract ram input head amount rawUsed low h.kind h.bounds.version stack h.array
  refine ⟨d,trace,⟨pc,stable,(keep 23 (by decide)).trans h.future,(keep 26 (by decide)).trans h.three,
    MainServeLayout.preserve (MainServeMemoryFrames.whole future (by decide)) h.serve,h.countBound,h.positive,(keep 18 (by decide)).trans h.countReg,
    minorReg,(ViewFrame.word future 92 (by decide)).trans h.usedWord,headView,fields,?_,h.bounds,h.bodyBound,h.usedBound,h.contained⟩,csr⟩
  exact fields.method.trans (MainRequestByteValue.ofNat _ (by have := MainRequestByteValue.tag (MainMethodSpec.decode (MainMethodBytes.token input head.method.2));omega))
end E5R.Thermostat.RequestPayloadReady
