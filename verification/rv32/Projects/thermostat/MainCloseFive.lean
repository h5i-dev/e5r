import Projects.thermostat.MainCloseValueChain
import Projects.thermostat.MainCloseValueTail
import Projects.thermostat.Bytes
set_option autoImplicit false
namespace E5R.Thermostat.MainCloseFive
open E5R E5R.Thermostat

/-- Exact five-byte close check, including its delimiter-dependent continuation.
    The first character is the cached left-trim byte, the remaining four are
    loaded by the actual ELF. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (base delimiter : Word) (g : Nat → BitVec 8)
    (hp : c.pc=0x8000260c#32) (h15 : c.get 15=base) (h25 : c.get 25=BitVec.ofNat 32 (g 0).toNat)
    (literals : MainCloseValueChain.Literals c) (h11 : c.get 11=delimiter) (h8 : c.get 8=44#32) (h29 : c.get 29=101#32)
    (memory : ∀ k, 1≤k → k<5 → B.inRam (base+BitVec.ofNat 32 k) 1=true)
    (data : ∀ k, 1≤k → k<5 → ram (base+BitVec.ofNat 32 k)=g k) :
    ∃ n d, n≤32 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if MainCloseFiveSpec.all g then 0x800026bc#32 else if delimiter=44#32 then 0x800025d8#32 else 0x80002474#32) ∧
      MainCloseValueChain.Frame c d ∧ d.sameCsr c := by
  obtain ⟨n,a,nb,sa,pa,frame,value,ac⟩ := MainCloseValueChain.contract B c ram base g hp h15 h25 literals memory data
  have a11 : a.get 11=delimiter := (frame 11 (by decide) (by decide) (by decide)).trans h11
  have a8 : a.get 8=44#32 := (frame 8 (by decide) (by decide) (by decide)).trans h8
  cases accepted : MainCloseValueChain.accepts0 g with
  | false =>
    have pa' : a.pc=0x800025d4#32 := by simpa only [accepted,Bool.false_eq_true,ite_false] using pa
    obtain ⟨d,sd,pd,dr,dc⟩ := MainCloseValueTail.next B a ram delimiter pa' a11 a8
    refine ⟨n+1,d,by omega,sa.trans sd,?_,fun r x y z => (dr r).trans (frame r x y z),dc.trans ac⟩
    rw [MainCloseValueChain.accepts_all,accepted,Bool.false_and]
    by_cases comma : delimiter=44#32 <;> simpa [comma] using pd
  | true =>
    have pa' : a.pc=0x80002672#32 := by simpa only [accepted,ite_true] using pa
    obtain ⟨k,d,kb,sd,pd,dr,dc⟩ := MainCloseValueTail.contract B a ram delimiter (g 4) pa' a11 a8 (value accepted)
      ((frame 29 (by decide) (by decide) (by decide)).trans h29)
    refine ⟨n+k,d,by omega,sa.trans sd,?_,fun r x y z => (dr r).trans (frame r x y z),dc.trans ac⟩
    simpa only [MainCloseValueChain.accepts_all,accepted,Bool.true_and,decide_eq_true_eq] using pd

/-- Slice-level connection to the independent byte specification. -/
theorem span (B : Board) (c : Core) (ram : Word → BitVec 8) (base delimiter : Word) (xs : List (BitVec 8))
    (bytes : Bytes.Span B ram base xs) (length : xs.length=5)
    (hp : c.pc=0x8000260c#32) (h15 : c.get 15=base) (h25 : c.get 25=BitVec.ofNat 32 (xs[0]?.getD 0#8).toNat)
    (literals : MainCloseValueChain.Literals c) (h11 : c.get 11=delimiter) (h8 : c.get 8=44#32) (h29 : c.get 29=101#32) :
    ∃ n d, n≤32 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if HeaderSpec.same xs (WireSpec.ascii "close") then 0x800026bc#32 else if delimiter=44#32 then 0x800025d8#32 else 0x80002474#32) ∧
      MainCloseValueChain.Frame c d ∧ d.sameCsr c := by
  rw [MainCloseFiveSpec.correspondence xs length]
  apply contract B c ram base delimiter (fun i => xs[i]?.getD 0#8) hp h15 h25 literals h11 h8 h29
  · intro k _ hi
    exact bytes.memory ⟨k,by omega⟩
  · intro k _ hi
    have bound : k<xs.length := by omega
    rw [List.getElem?_eq_getElem bound]
    exact bytes.bytes ⟨k,bound⟩
end E5R.Thermostat.MainCloseFive
