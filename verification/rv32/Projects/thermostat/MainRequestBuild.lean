import Projects.thermostat.MainRequestMethod
import Projects.thermostat.MainRequestMemoryHead
import Projects.thermostat.MainRequestMemoryViews
import Projects.thermostat.MainRequestMemoryGlobalFrame
import Projects.thermostat.MainTransactionStable
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.MainRequestBuild
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := MainRequestMethod.B
abbrev sp := MainRequestMethod.sp
abbrev fp := MainRequestMethod.fp
abbrev rx := MainRequestMethod.rx

def method (input : List (BitVec 8)) (head : Head) : Word :=
  BitVec.ofNat 32 (MainMethodSpec.tag (MainMethodSpec.decode (MainMethodBytes.token input head.method.2)))
def pathLength (input : List (BitVec 8)) (head : Head) : Word :=
  BitVec.ofNat 32 (MainQuerySpec.pathLength (MainQuerySpec.bytes input) head.target.1 head.target.2)
def queryPtr (input : List (BitVec 8)) (head : Head) : Word :=
  rx+BitVec.ofNat 32 (MainQuerySpec.queryStart (MainQuerySpec.bytes input) head.target.1 head.target.2)
def queryLength (input : List (BitVec 8)) (head : Head) : Word :=
  BitVec.ofNat 32 (MainQuerySpec.queryLength (MainQuerySpec.bytes input) head.target.1 head.target.2)
def memory (ram : Word → BitVec 8) (input : List (BitVec 8)) (head : Head) (amount : Nat) :=
  MainRequestMemory.after ram sp rx head amount (method input head) (rx+BitVec.ofNat 32 head.target.1) (pathLength input head) (queryPtr input head) (queryLength input head)

structure Ready (c : Core) (ram : Word → BitVec 8) (input : List (BitVec 8)) (s : Spec.Snapshot) (head : Head) (amount served : Nat) : Prop where
  pc : c.pc=0x80001246#32
  stable : MainTransactionStable.At c ram input s
  future : c.get 23=0x80fff9f0#32
  three : c.get 26=3#32
  serve : MainServeLayout.At ram served
  countBound : served≤100
  positive : 0<served
  countReg : c.get 18=BitVec.ofNat 32 served
  minorReg : c.get 9=BitVec.ofNat 32 head.minor
  bodyReg : c.get 20=rx+BitVec.ofNat 32 head.len
  rxReg : c.get 21=rx
  low : c.get 27=BitVec.ofNat 32 amount
  used : c.get 24=BitVec.ofNat 32 (head.len+amount)
  endReg : c.get 25=BitVec.ofNat 32 (head.len+amount)
  usedWord : ramRead ram (fp+92#32) .w=BitVec.ofNat 32 (head.len+amount)
  headView : HeadCompletedView.At ram (sp+3312#32) head
  request : MainRequestMemoryViews.At ram sp rx head amount (method input head) (rx+BitVec.ofNat 32 head.target.1) (pathLength input head) (queryPtr input head) (queryLength input head)
  methodByte : ram (sp+3684#32)=BitVec.ofNat 8 (MainMethodSpec.tag (MainMethodSpec.decode (MainMethodBytes.token input head.method.2)))
  bounds : MainHeadAcceptedBounds.At 1024 1024 head
  kind : head.framing=.length amount
  available : head.len+amount≤input.length
  contained : head.target.2<head.len ∧ (∀ entry∈head.headers, MainHeadBounds.FieldAt head.len entry)

/-- Actual full Request construction with exact UART-derived method/path/query
    and body spans. The new Head and parameter array are real RAM contents;
    overwritten parser-future fields are replaced by a live transaction envelope. -/
theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat}
    (h : MainRequestMethod.Ready c ram input s head amount served) (payload : MainServeNextPayloadWords.At ram sp) :
    ∃ d, Quiet.Steps B img 460 ⟨c,ram⟩ ⟨d,memory ram input head amount⟩ ∧ Ready d (memory ram input head amount) input s head amount served ∧ d.sameCsr c := by
  have bodyBound := h.bounds.content amount h.kind
  have totalBound : head.len+amount≤2048 := by have := h.bounds.length.2;omega
  have stack : Memory.Block B sp 5232 := by
    have block := Memory.sub_block (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 60304) (m := 5232) h.stable.stack (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60304#32=sp by decide +kernel] using block
  obtain ⟨d,trace,pc,d9,d20,dr,csr⟩ := MainRequestBuildCore.contract B c ram sp rx head.len (head.len+amount) (head.len+amount)
    (method input head) (rx+BitVec.ofNat 32 head.target.1) (pathLength input head) (queryPtr input head) (queryLength input head)
    1#32 0#32 (BitVec.ofNat 32 amount) (BitVec.ofNat 32 head.method.1) (BitVec.ofNat 32 head.method.2) (BitVec.ofNat 32 head.target.1) (BitVec.ofNat 32 head.target.2) (BitVec.ofNat 32 head.minor)
    h.pc h.stable.sp (by simpa only [show sp+3204#32=fp by decide +kernel] using h.stable.fp)
    h.start h.endReg h.used h.rxReg h.method h.targetPtr h.pathLength h.queryPtr h.queryLength h.tag h.zeroHigh h.low h.methodStartReg h.methodEndReg h.targetStartReg h.targetEndReg h.minor
    (by omega) (by omega) totalBound payload stack (by decide +kernel)
  let after := memory ram input head amount
  have frame (off size : Nat) (bound : off+size≤5232) (apart : off+size≤3312 ∨ 3685≤off) : ViewFrame.Region ram after (sp+BitVec.ofNat 32 off) size :=
    MainRequestMemoryGlobalFrame.contract ram sp rx head amount (method input head) (rx+BitVec.ofNat 32 head.target.1) (pathLength input head) (queryPtr input head) (queryLength input head) off size bound apart
  have keep (r : Reg) (safe : r∈[2,8,18,19,21,22,23,24,25,26,27]) : d.get r=c.get r := by
    have yes : ∀ r : Reg, r∈[2,8,18,19,21,22,23,24,25,26,27] → r∈MainRequestSaved.regs ∧ r≠20 := by decide +kernel
    obtain ⟨mem,neq⟩ := yes r safe
    exact dr r mem neq
  have future : ViewFrame.Region ram after fp 96 := by
    simpa only [show sp+3204#32=fp by decide +kernel] using frame 3204 96 (by decide) (Or.inl (by decide))
  have stable : MainTransactionStable.At d after input s := by
    refine ⟨(keep 2 (by decide)).trans h.stable.sp,(keep 8 (by decide)).trans h.stable.fp,
      (keep 19 (by decide)).trans h.stable.uart,(keep 22 (by decide)).trans h.stable.one,h.stable.layout.bound,
      (ViewFrame.word future 84 (by decide)).trans h.stable.layout.filled,?_,?_,h.stable.invariant,h.stable.stack,(congrArg Prod.fst csr).trans h.stable.masked⟩
    · intro i
      have byte := frame 132 2048 (by decide) (Or.inl (by decide)) ⟨i.val,by have := i.isLt;have := h.stable.layout.bound;omega⟩
      have atByte : after (rx+BitVec.ofNat 32 i.val)=ram (rx+BitVec.ofNat 32 i.val) := by
        simpa only [show sp+132#32=rx by decide +kernel] using byte
      exact atByte.trans (h.stable.bytes i)
    · apply AppState.preserve ram after s h.stable.app
      simpa only [ViewFrame.Region,show sp+44#32=0x80ffebbc#32 by decide +kernel] using frame 44 25 (by decide) (Or.inl (by decide))
  have view := MainRequestMemoryViews.contract B ram sp rx head amount (method input head) (rx+BitVec.ofNat 32 head.target.1) (pathLength input head) (queryPtr input head) (queryLength input head) totalBound stack
  have headView := MainRequestMemoryHead.contract B ram sp rx head amount (method input head) (rx+BitVec.ofNat 32 head.target.1) (pathLength input head) (queryPtr input head) (queryLength input head) h.kind bodyBound h.bounds.version stack h.array
  have methodByte : after (sp+3684#32)=BitVec.ofNat 8 (MainMethodSpec.tag (MainMethodSpec.decode (MainMethodBytes.token input head.method.2))) :=
    view.method.trans (MainRequestByteValue.ofNat _ (by have := MainRequestByteValue.tag (MainMethodSpec.decode (MainMethodBytes.token input head.method.2));omega))
  refine ⟨d,trace,⟨pc,stable,(keep 23 (by decide)).trans h.future,(keep 26 (by decide)).trans h.three,
    MainServeLayout.preserve (MainServeMemoryFrames.whole future (by decide)) h.serve,h.countBound,h.positive,
    (keep 18 (by decide)).trans h.countReg,d9,?_,(keep 21 (by decide)).trans h.rxReg,(keep 27 (by decide)).trans h.low,
    (keep 24 (by decide)).trans h.used,(keep 25 (by decide)).trans h.endReg,(ViewFrame.word future 92 (by decide)).trans h.usedWord,
    headView,view,methodByte,h.bounds,h.kind,h.available,h.contained⟩,csr⟩
  exact d20.trans (BitVec.add_comm _ _)
end E5R.Thermostat.MainRequestBuild
