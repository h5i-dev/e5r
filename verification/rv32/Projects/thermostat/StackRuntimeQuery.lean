import Projects.thermostat.RuntimeQuery
import Projects.thermostat.StackBoard
set_option autoImplicit false
set_option maxRecDepth 4000
namespace E5R.Thermostat.StackRuntimeQuery
open E5R E5R.Thermostat HttpRequestSpec RuntimeQuery
abbrev B := StackBoard.board

theorem contract {c ram input s head amount rawUsed served lowValue} (h : RuntimeTarget.Ready c ram input s head amount rawUsed served lowValue) :
    ∃ n d, n≤5*(head.target.2-head.target.1)+12 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      Ready d ram input s head amount rawUsed served lowValue ∧ d.sameCsr c := by
  have targetBound : head.target.2≤2048 := by have := h.contained.1;have := h.bounds.length.2;omega
  have targetInput : head.target.2<input.length := by have := h.contained.1;have := h.available;have := h.usedBound;omega
  have stack : Memory.Block B sp 5232 := by
    have block := Memory.sub_block (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 60304) (m := 5232) StackBoard.available (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60304#32=sp by decide +kernel] using block
  have rxBlock : Memory.Block B rx 2048 := by
    have block := Memory.sub_block (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 60436) (m := 2048) StackBoard.available (by decide) (by decide)
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
end E5R.Thermostat.StackRuntimeQuery
