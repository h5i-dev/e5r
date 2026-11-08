import Projects.thermostat.MainRequestQuery
import Projects.thermostat.MainMethodDecode
import Projects.thermostat.MainMethodBytes
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainRequestMethod
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := MainRequestQuery.B
abbrev sp := MainRequestQuery.sp
abbrev fp := MainRequestQuery.fp
abbrev rx := MainRequestQuery.rx

structure Ready (c : Core) (ram : Word → BitVec 8) (input : List (BitVec 8)) (s : Spec.Snapshot) (head : Head) (amount served : Nat) : Prop where
  pc : c.pc=0x80001160#32
  stable : MainHeaderLoopTwo.Stable c ram input s
  future : c.get 23=0x80fff9f0#32
  three : c.get 26=3#32
  serve : MainServeLayout.At ram served
  countBound : served≤100
  positive : 0<served
  countReg : c.get 18=BitVec.ofNat 32 served
  zeroHigh : c.get 31=0#32
  targetStartReg : c.get 29=BitVec.ofNat 32 head.target.1
  targetEndReg : c.get 30=BitVec.ofNat 32 head.target.2
  six : c.get 5=6#32
  rxReg : c.get 21=rx
  targetPtr : c.get 10=rx+BitVec.ofNat 32 head.target.1
  tag : c.get 9=1#32
  low : c.get 27=BitVec.ofNat 32 amount
  start : c.get 20=BitVec.ofNat 32 head.len
  used : c.get 24=BitVec.ofNat 32 (head.len+amount)
  endReg : c.get 25=BitVec.ofNat 32 (head.len+amount)
  usedWord : ramRead ram (fp+92#32) .w=BitVec.ofNat 32 (head.len+amount)
  headView : HeadCompletedView.At ram (sp+3320#32) head
  array : MainNextArrayView.At ram (sp+4248#32) head
  methodStart : ramRead ram (sp+28#32) .w=BitVec.ofNat 32 head.method.1
  methodEnd : ramRead ram (sp+24#32) .w=BitVec.ofNat 32 head.method.2
  targetStart : ramRead ram (sp+36#32) .w=BitVec.ofNat 32 head.target.1
  targetEnd : ramRead ram (sp+32#32) .w=BitVec.ofNat 32 head.target.2
  minor : ramRead ram (sp+40#32) .w=BitVec.ofNat 32 head.minor
  bounds : MainHeadAcceptedBounds.At 1024 1024 head
  kind : head.framing=.length amount
  available : head.len+amount≤input.length
  contained : head.target.2<head.len ∧ (∀ entry∈head.headers, MainHeadBounds.FieldAt head.len entry)

  methodStartReg : c.get 7=BitVec.ofNat 32 head.method.1
  methodEndReg : c.get 11=BitVec.ofNat 32 head.method.2
  pathLength : c.get 28=BitVec.ofNat 32 (MainQuerySpec.pathLength (MainQuerySpec.bytes input) head.target.1 head.target.2)
  queryPtr : c.get 12=rx+BitVec.ofNat 32 (MainQuerySpec.queryStart (MainQuerySpec.bytes input) head.target.1 head.target.2)
  queryLength : c.get 13=BitVec.ofNat 32 (MainQuerySpec.queryLength (MainQuerySpec.bytes input) head.target.1 head.target.2)

  method : c.get 14=BitVec.ofNat 32 (MainMethodSpec.tag (MainMethodSpec.decode (MainMethodBytes.token input head.method.2)))

/-- Method classification is derived from the actual bytes received over UART;
    accepted-parser method spans start at zero. Both real guards are proved. -/
theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat}
    (h : MainRequestQuery.Ready c ram input s head amount served) :
    ∃ n d, n≤34 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ Ready d ram input s head amount served ∧ d.sameCsr c := by
  have zero := h.bounds.method.1
  have methodTarget := h.bounds.target.1
  have targetOrdered := h.bounds.target.2.1
  have contained := h.contained.1
  have headBound := h.bounds.length.2
  have amountBound := h.bounds.content amount h.kind
  have inputBound : head.method.2≤input.length := by have := h.available;omega
  have totalBound : head.len+amount≤2048 := by omega
  have rxBlock : Memory.Block B rx 2048 := by
    have block := Memory.sub_block (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 60436) (m := 2048) h.stable.stack (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60436#32=rx by decide +kernel] using block
  have memory (k : Nat) (inside : k<head.method.2-head.method.1) :
      B.inRam ((rx+BitVec.ofNat 32 head.method.1)+BitVec.ofNat 32 k) 1=true := by
    rw [zero,BitVec.add_zero]
    exact Memory.block_access rxBlock (by decide) (by omega)
  have data (k : Nat) (inside : k<head.method.2-head.method.1) :
      ram ((rx+BitVec.ofNat 32 head.method.1)+BitVec.ofNat 32 k)=MainMethodBytes.byte input k := by
    have hi : k<input.length := by omega
    rw [zero,BitVec.add_zero]
    have atByte := h.stable.bytes ⟨k,hi⟩
    change ram (rx+BitVec.ofNat 32 k)=input[k] at atByte
    simpa only [MainMethodBytes.byte,List.getElem?_eq_getElem hi,Option.getD_some] using atByte
  obtain ⟨n,d,nb,trace,pc,d14,dr,csr⟩ := MainMethodDecode.contract B c ram rx (MainMethodBytes.byte input) head.method.1 head.method.2 (head.len+amount)
    (by omega) (by omega) totalBound h.pc h.methodStartReg h.methodEndReg h.used h.rxReg h.three h.five h.six memory data
  have method : d.get 14=BitVec.ofNat 32 (MainMethodSpec.tag (MainMethodSpec.decode (MainMethodBytes.token input head.method.2))) := by
    rw [zero,Nat.sub_zero,MainMethodBytes.take_correspondence input head.method.2 inputBound] at d14
    exact d14
  have keep (r : Reg) (safe : r∈[2,5,7,8,9,10,11,12,13,18,19,20,21,22,23,24,25,26,27,28,29,30,31]) : d.get r=c.get r := by
    have yes : ∀ r : Reg, r∈[2,5,7,8,9,10,11,12,13,18,19,20,21,22,23,24,25,26,27,28,29,30,31] → r≠6 ∧ r≠14 ∧ r≠15 ∧ r≠16 ∧ r≠17 := by decide +kernel
    obtain ⟨a,b,e,f,g⟩ := yes r safe
    exact dr r a b e f g
  have stable : MainHeaderLoopTwo.Stable d ram input s := ⟨(keep 2 (by decide)).trans h.stable.sp,
    (keep 8 (by decide)).trans h.stable.fp,(keep 19 (by decide)).trans h.stable.uart,(keep 22 (by decide)).trans h.stable.one,
    h.stable.layout,h.stable.bytes,h.stable.app,h.stable.invariant,h.stable.stack,(congrArg Prod.fst csr).trans h.stable.masked⟩
  refine ⟨n,d,nb,trace,⟨pc,stable,(keep 23 (by decide)).trans h.future,(keep 26 (by decide)).trans h.three,h.serve,h.countBound,h.positive,(keep 18 (by decide)).trans h.countReg,(keep 31 (by decide)).trans h.zeroHigh,(keep 29 (by decide)).trans h.targetStartReg,(keep 30 (by decide)).trans h.targetEndReg,(keep 5 (by decide)).trans h.six,(keep 21 (by decide)).trans h.rxReg,(keep 10 (by decide)).trans h.targetPtr,(keep 9 (by decide)).trans h.tag,(keep 27 (by decide)).trans h.low,(keep 20 (by decide)).trans h.start,(keep 24 (by decide)).trans h.used,(keep 25 (by decide)).trans h.endReg,h.usedWord,h.headView,h.array,h.methodStart,h.methodEnd,h.targetStart,h.targetEnd,h.minor,h.bounds,h.kind,h.available,h.contained,(keep 7 (by decide)).trans h.methodStartReg,(keep 11 (by decide)).trans h.methodEndReg,(keep 28 (by decide)).trans h.pathLength,(keep 12 (by decide)).trans h.queryPtr,(keep 13 (by decide)).trans h.queryLength,method⟩,csr⟩
end E5R.Thermostat.MainRequestMethod
