import Projects.thermostat.RuntimeTarget
import Projects.thermostat.MainQuery
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.RuntimeQuery
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := RuntimeTarget.B
abbrev sp := RuntimeTarget.sp
abbrev fp := RuntimeTarget.fp
abbrev rx := RuntimeTarget.rx

structure Ready (c : Core) (ram : Word → BitVec 8) (input : List (BitVec 8)) (s : Spec.Snapshot) (head : Head) (amount rawUsed served : Nat) (lowValue : Word) : Prop where
  pc : c.pc=0x80000d50#32
  stable : MainTransactionStable.At c ram input s
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
  five : c.get 17=5#32
  rxReg : c.get 21=rx
  targetPtr : c.get 10=rx+BitVec.ofNat 32 head.target.1
  tag : c.get 9=HeadCompletedView.framingTag head.framing
  low : c.get 27=lowValue
  start : c.get 20=BitVec.ofNat 32 head.len
  used : c.get 24=BitVec.ofNat 32 rawUsed
  endReg : c.get 25=BitVec.ofNat 32 (head.len+amount)
  usedWord : ramRead ram (fp+92#32) .w=BitVec.ofNat 32 rawUsed
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

  methodStartReg : c.get 7=BitVec.ofNat 32 head.method.1
  methodEndReg : c.get 11=BitVec.ofNat 32 head.method.2
  pathLength : c.get 28=BitVec.ofNat 32 (MainQuerySpec.pathLength (MainQuerySpec.bytes input) head.target.1 head.target.2)
  queryPtr : c.get 12=rx+BitVec.ofNat 32 (MainQuerySpec.queryStart (MainQuerySpec.bytes input) head.target.1 head.target.2)
  queryLength : c.get 13=BitVec.ofNat 32 (MainQuerySpec.queryLength (MainQuerySpec.bytes input) head.target.1 head.target.2)

/-- Actual method span loads and URI split, derived from the bytes received
    from UART and the actual accepted parser target span. -/
theorem contract {c ram input s head amount rawUsed served lowValue} (h : RuntimeTarget.Ready c ram input s head amount rawUsed served lowValue) :
    ∃ n d, n≤5*(head.target.2-head.target.1)+12 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      Ready d ram input s head amount rawUsed served lowValue ∧ d.sameCsr c := by
  have targetBound : head.target.2≤2048 := by have := h.contained.1;have := h.bounds.length.2;omega
  have targetInput : head.target.2<input.length := by have := h.contained.1;have := h.available;have := h.usedBound;omega
  have stack : Memory.Block B sp 5232 := by
    have block := Memory.sub_block (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 60304) (m := 5232) h.stable.stack (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60304#32=sp by decide +kernel] using block
  have rxBlock : Memory.Block B rx 2048 := by
    have block := Memory.sub_block (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 60436) (m := 2048) h.stable.stack (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60436#32=rx by decide +kernel] using block
  let bytes : Nat → BitVec 8 := fun k => input[k]?.getD 0#8
  have memory (k : Nat) (inside : k<head.target.2) : B.inRam (rx+BitVec.ofNat 32 k) 1=true :=
    Memory.block_access rxBlock (by decide) (by omega)
  have data (k : Nat) (inside : k<head.target.2) : ram (rx+BitVec.ofNat 32 k)=bytes k := by
    have hi : k<input.length := by omega
    have atByte := h.stable.bytes ⟨k,hi⟩
    change ram (rx+BitVec.ofNat 32 k)=input[k] at atByte
    simpa only [bytes,List.getElem?_eq_getElem hi,Option.getD_some] using atByte
  obtain ⟨n,d,nb,trace,pc,d7,d11,d28,d12,d13,dr,csr⟩ := MainQuery.contract B c ram sp rx (BitVec.ofNat 32 head.method.1) (BitVec.ofNat 32 head.method.2) bytes head.target.1 head.target.2
    h.bounds.target.2.1 targetBound memory data stack (by decide +kernel) h.pc h.stable.sp h.rxReg h.targetStartReg h.targetEndReg h.targetPtr h.question h.methodStart h.methodEnd
  have keep (r : Reg) (safe : r∈[2,5,8,9,10,17,18,19,20,21,22,23,24,25,26,27,29,30,31]) : d.get r=c.get r := by
    have yes : ∀ r : Reg, r∈[2,5,8,9,10,17,18,19,20,21,22,23,24,25,26,27,29,30,31] → r∉[7,11,12,13,14,15,28] := by decide +kernel
    exact dr r (yes r safe)
  have stable : MainTransactionStable.At d ram input s := ⟨(keep 2 (by decide)).trans h.stable.sp,
    (keep 8 (by decide)).trans h.stable.fp,(keep 19 (by decide)).trans h.stable.uart,(keep 22 (by decide)).trans h.stable.one,
    h.stable.bound,h.stable.filled,h.stable.bytes,h.stable.app,h.stable.invariant,h.stable.stack,(congrArg Prod.fst csr).trans h.stable.masked⟩
  refine ⟨n,d,nb,trace,⟨pc,stable,(keep 23 (by decide)).trans h.future,(keep 26 (by decide)).trans h.three,h.serve,h.countBound,h.positive,(keep 18 (by decide)).trans h.countReg,(keep 31 (by decide)).trans h.zeroHigh,(keep 29 (by decide)).trans h.targetStartReg,(keep 30 (by decide)).trans h.targetEndReg,(keep 5 (by decide)).trans h.six,(keep 17 (by decide)).trans h.five,(keep 21 (by decide)).trans h.rxReg,(keep 10 (by decide)).trans h.targetPtr,(keep 9 (by decide)).trans h.tag,(keep 27 (by decide)).trans h.low,(keep 20 (by decide)).trans h.start,(keep 24 (by decide)).trans h.used,(keep 25 (by decide)).trans h.endReg,h.usedWord,h.headView,h.array,h.methodStart,h.methodEnd,h.targetStart,h.targetEnd,h.minor,h.bounds,h.kind,h.bodyBound,h.usedBound,h.available,h.contained,d7,d11,d28,d12,d13⟩,csr⟩
end E5R.Thermostat.RuntimeQuery
