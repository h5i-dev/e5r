import Projects.thermostat.RuntimeMethod
import Projects.thermostat.StackBoard
set_option autoImplicit false
set_option maxRecDepth 4000
namespace E5R.Thermostat.StackRuntimeMethod
open E5R E5R.Thermostat HttpRequestSpec RuntimeMethod
abbrev B := StackBoard.board

theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount rawUsed served : Nat} {lowValue : Word}
    (h : RuntimeQuery.Ready c ram input s head amount rawUsed served lowValue) :
    ∃ n d, n≤34 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ Ready d ram input s head amount rawUsed served lowValue ∧ d.sameCsr c := by
  have usedBound := h.usedBound
  have zero := h.bounds.method.1
  have methodTarget := h.bounds.target.1
  have targetOrdered := h.bounds.target.2.1
  have contained := h.contained.1
  have headBound := h.bounds.length.2
  have amountBound := h.bodyBound
  have inputBound : head.method.2≤input.length := by have := h.available;have := h.usedBound;omega
  have totalBound : rawUsed≤2048 := by have := h.available;have := h.stable.bound;omega
  have rxBlock : Memory.Block B rx 2048 := by
    have block := Memory.sub_block (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 60436) (m := 2048) StackBoard.available (by decide) (by decide)
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
  obtain ⟨n,d,nb,trace,pc,d14,dr,csr⟩ := MainMethodDecode.contract B c ram rx (MainMethodBytes.byte input) head.method.1 head.method.2 rawUsed
    (by omega) (by omega) totalBound h.pc h.methodStartReg h.methodEndReg h.used h.rxReg h.three h.five h.six memory data
  have method : d.get 14=BitVec.ofNat 32 (MainMethodSpec.tag (MainMethodSpec.decode (MainMethodBytes.token input head.method.2))) := by
    rw [zero,Nat.sub_zero,MainMethodBytes.take_correspondence input head.method.2 inputBound] at d14
    exact d14
  have keep (r : Reg) (safe : r∈[2,5,7,8,9,10,11,12,13,18,19,20,21,22,23,24,25,26,27,28,29,30,31]) : d.get r=c.get r := by
    have yes : ∀ r : Reg, r∈[2,5,7,8,9,10,11,12,13,18,19,20,21,22,23,24,25,26,27,28,29,30,31] → r≠6 ∧ r≠14 ∧ r≠15 ∧ r≠16 ∧ r≠17 := by decide +kernel
    obtain ⟨a,b,e,f,g⟩ := yes r safe
    exact dr r a b e f g
  have stable : MainTransactionStable.At d ram input s := ⟨(keep 2 (by decide)).trans h.stable.sp,
    (keep 8 (by decide)).trans h.stable.fp,(keep 19 (by decide)).trans h.stable.uart,(keep 22 (by decide)).trans h.stable.one,
    h.stable.bound,h.stable.filled,h.stable.bytes,h.stable.app,h.stable.invariant,h.stable.stack,(congrArg Prod.fst csr).trans h.stable.masked⟩
  refine ⟨n,d,nb,trace,⟨pc,stable,(keep 23 (by decide)).trans h.future,(keep 26 (by decide)).trans h.three,h.serve,h.countBound,h.positive,(keep 18 (by decide)).trans h.countReg,(keep 31 (by decide)).trans h.zeroHigh,(keep 29 (by decide)).trans h.targetStartReg,(keep 30 (by decide)).trans h.targetEndReg,(keep 5 (by decide)).trans h.six,(keep 21 (by decide)).trans h.rxReg,(keep 10 (by decide)).trans h.targetPtr,(keep 9 (by decide)).trans h.tag,(keep 27 (by decide)).trans h.low,(keep 20 (by decide)).trans h.start,(keep 24 (by decide)).trans h.used,(keep 25 (by decide)).trans h.endReg,h.usedWord,h.headView,h.array,h.methodStart,h.methodEnd,h.targetStart,h.targetEnd,h.minor,h.bounds,h.kind,h.bodyBound,h.usedBound,h.available,h.contained,(keep 7 (by decide)).trans h.methodStartReg,(keep 11 (by decide)).trans h.methodEndReg,(keep 28 (by decide)).trans h.pathLength,(keep 12 (by decide)).trans h.queryPtr,(keep 13 (by decide)).trans h.queryLength,method⟩,csr⟩
end E5R.Thermostat.StackRuntimeMethod
