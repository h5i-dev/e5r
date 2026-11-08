import Projects.thermostat.MainCloseScan
import Projects.thermostat.MainCloseToken
import Projects.thermostat.MainCloseValueContext
set_option autoImplicit false
set_option maxRecDepth 4000
namespace E5R.Thermostat.MainClosePiece
open E5R E5R.Thermostat

def accepts (xs : List (BitVec 8)) := HeaderSpec.same (TrimMath.trim (MainCloseScanSpec.token xs)) (WireSpec.ascii "close")

theorem skip_pc (delimiter : Word) (found : Bool) (correct : delimiter=44#32 ↔ found=true) :
    (if delimiter≠44#32 then 0x80002474#32 else 0x800025d8#32)=(if found then 0x800025d8#32 else 0x80002474#32) := by
  cases found <;> simp_all

/-- One actual first-comma partition and token test. Empty tokens are skipped
    by the real code, and nonempty token bytes are derived from the whole input
    slice rather than supplied as an independent semantic summary. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (xs : List (BitVec 8))
    (span : Bytes.Span B ram base xs) (positive : 0<xs.length) (hp : c.pc=0x80002584#32)
    (h22 : c.get 22=base) (h14 : c.get 14=BitVec.ofNat 32 xs.length)
    (h15 : c.get 15=base+BitVec.ofNat 32 xs.length) (literals : MainCloseValueContext.Literals c) :
    ∃ n d, n≤24*(MainCloseScanSpec.token xs).length+62 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if accepts xs then 0x800026bc#32 else if (MainCloseScanSpec.rest xs).isSome then 0x800025d8#32 else 0x80002474#32) ∧
      (∀ ys, MainCloseScanSpec.rest xs=some ys →
        d.get 10=base+BitVec.ofNat 32 ((MainCloseScanSpec.token xs).length+1) ∧ d.get 14=BitVec.ofNat 32 ys.length) ∧
      MainCloseValueContext.Frame c d ∧ d.sameCsr c := by
  obtain ⟨n,a,nb,sa,pa,a22,a23,delimiter,next,ar,ac⟩ := MainCloseScan.contract B c ram base xs span positive hp h22 h14 h15 literals.c8
  have frame : MainCloseValueContext.Frame c a := fun r n10 n11 n14 n15 _ n23 _ _ _ => ar r n10 n11 n14 n15 n23
  have aLiterals := literals.preserve frame
  by_cases empty : MainCloseScanSpec.token xs=[]
  · have pa' : a.pc=0x800025d4#32 := by simpa only [empty,ite_true] using pa
    have rejects : accepts xs=false := MainCloseTokenMath.other_length _ (by simp only [empty,TrimMath.trim,TrimMath.left,List.reverse_nil,List.dropWhile_nil,List.length_nil];decide)
    obtain ⟨d,sd,pd,dr,dc⟩ := MainCloseValueTail.next B a ram (a.get 11) pa' rfl aLiterals.c8
    refine ⟨n+1,d,by omega,sa.trans sd,?_,?_,?_,dc.trans ac⟩
    · rw [rejects]
      simpa only [Bool.false_eq_true,ite_false,skip_pc (a.get 11) _ delimiter] using pd
    · intro ys found
      have metadata := next ys found
      exact ⟨(dr 10).trans metadata.1,(dr 14).trans metadata.2⟩
    · intro r n10 n11 n14 n15 n22 n23 n24 n25 n26
      exact (dr r).trans (frame r n10 n11 n14 n15 n22 n23 n24 n25 n26)
  · have pa' : a.pc=0x800025b0#32 := by simpa only [empty,ite_false] using pa
    have tokenSpan := MainCloseScanSpec.token_span span
    have positiveToken : 0<(MainCloseScanSpec.token xs).length := List.length_pos_iff.mpr empty
    obtain ⟨k,d,kb,sd,pd,dr,dc⟩ := MainCloseToken.contract B a ram base (a.get 11) (MainCloseScanSpec.token xs) tokenSpan positiveToken pa' a22 a23
      aLiterals.c9 aLiterals.c21 aLiterals.toLiterals aLiterals.c18 aLiterals.c29 rfl aLiterals.c8
    refine ⟨n+k,d,by omega,sa.trans sd,?_,?_,?_,dc.trans ac⟩
    · change d.pc=(if accepts xs then 0x800026bc#32 else if a.get 11=44#32 then 0x800025d8#32 else 0x80002474#32) at pd
      cases someFound : (MainCloseScanSpec.rest xs).isSome with
      | false =>
        have word : a.get 11≠44#32 := by
          intro equal
          have impossible := delimiter.mp equal
          simpa only [someFound,Bool.false_eq_true] using impossible
        simpa only [word,ite_false,someFound,Bool.false_eq_true] using pd
      | true =>
        have word : a.get 11=44#32 := delimiter.mpr someFound
        simpa only [word,ite_true,someFound] using pd
    · intro ys found
      have metadata := next ys found
      exact ⟨(dr 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans metadata.1,
        (dr 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans metadata.2⟩
    · intro r n10 n11 n14 n15 n22 n23 n24 n25 n26
      exact (dr r n15 n22 n23 n24 n25 n26).trans (frame r n10 n11 n14 n15 n22 n23 n24 n25 n26)
end E5R.Thermostat.MainClosePiece
