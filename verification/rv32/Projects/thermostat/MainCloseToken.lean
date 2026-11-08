import Projects.thermostat.MainCloseTrim
import Projects.thermostat.MainCloseFive
import Projects.thermostat.MainCloseTokenLength
set_option autoImplicit false
set_option maxRecDepth 4000
namespace E5R.Thermostat.MainCloseToken
open E5R E5R.Thermostat

/-- One nonempty comma token: actual trim, length test, case-insensitive close
    test, and the real continuation selected by the delimiter. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (p delimiter : Word) (xs : List (BitVec 8))
    (span : Bytes.Span B ram p xs) (positive : 0<xs.length) (hp : c.pc=0x800025b0#32)
    (h22 : c.get 22=p) (h23 : c.get 23=BitVec.ofNat 32 xs.length)
    (h9 : c.get 9=23#32) (h21 : c.get 21=0x80001b#32)
    (literals : MainCloseValueChain.Literals c) (h18 : c.get 18=5#32) (h29 : c.get 29=101#32)
    (h11 : c.get 11=delimiter) (h8 : c.get 8=44#32) :
    ∃ n d, n≤18*xs.length+51 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if HeaderSpec.same (TrimMath.trim xs) (WireSpec.ascii "close") then 0x800026bc#32 else if delimiter=44#32 then 0x800025d8#32 else 0x80002474#32) ∧
      MainCloseTrim.Frame c d ∧ d.sameCsr c := by
  obtain ⟨n,a,nb,sa,pa,a15,a24,trimSpan,cache,ar,ac⟩ := MainCloseTrim.contract B c ram p xs span positive hp h22 h23 h9 h21
  have a11 : a.get 11=delimiter := (ar 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h11
  have a8 : a.get 8=44#32 := (ar 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h8
  by_cases empty : TrimMath.trim xs=[]
  · have pa' : a.pc=0x800025d4#32 := by simpa only [empty,ite_true] using pa
    obtain ⟨d,sd,pd,dr,dc⟩ := MainCloseValueTail.next B a ram delimiter pa' a11 a8
    have rejects : HeaderSpec.same (TrimMath.trim xs) (WireSpec.ascii "close")=false := MainCloseTokenMath.other_length _ (by rw [empty];decide)
    refine ⟨n+1,d,by omega,sa.trans sd,?_,?_,dc.trans ac⟩
    · rw [rejects]
      by_cases comma : delimiter=44#32 <;> simpa [comma] using pd
    · intro r n15 n22 n23 n24 n25 n26
      exact (dr r).trans (ar r n15 n22 n23 n24 n25 n26)
  · have pa' : a.pc=0x80002608#32 := by simpa only [empty,ite_false] using pa
    have a18 : a.get 18=5#32 := (ar 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h18
    obtain ⟨e,se,pe,er,ec⟩ := MainCloseTokenLength.contract B a ram (TrimMath.trim xs).length trimSpan.length pa' a24 a18
    by_cases length : (TrimMath.trim xs).length=5
    · have pe' : e.pc=0x8000260c#32 := by simpa only [length,ite_true] using pe
      have trimmedPositive : 0<(TrimMath.trim xs).length := by omega
      have firstRead : ram (a.get 15)=(TrimMath.trim xs)[0]?.getD 0#8 := by
        have actual := trimSpan.bytes ⟨0,trimmedPositive⟩
        change ram (a.get 15+0#32)=((TrimMath.trim xs)[0]'(trimmedPositive)) at actual
        rw [List.getElem?_eq_getElem trimmedPositive]
        simpa only [BitVec.add_zero,Option.getD_some] using actual
      have e25 : e.get 25=BitVec.ofNat 32 ((TrimMath.trim xs)[0]?.getD 0#8).toNat := by
        rw [er 25,cache empty,firstRead]
      have eLiterals : MainCloseValueChain.Literals e := ⟨
        (er 6).trans ((ar 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans literals.c6),
        (er 19).trans ((ar 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans literals.c19),
        (er 7).trans ((ar 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans literals.c7),
        (er 20).trans ((ar 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans literals.c20)⟩
      obtain ⟨k,d,kb,sd,pd,dr,dc⟩ := MainCloseFive.span B e ram (a.get 15) delimiter (TrimMath.trim xs) trimSpan length pe' (er 15) e25 eLiterals
        ((er 11).trans a11) ((er 8).trans a8)
        ((er 29).trans ((ar 29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h29))
      refine ⟨n+1+k,d,by omega,(sa.trans se).trans sd,pd,?_,dc.trans (ec.trans ac)⟩
      intro r n15 n22 n23 n24 n25 n26
      exact (dr r n15 n22 n23).trans ((er r).trans (ar r n15 n22 n23 n24 n25 n26))
    · have pe' : e.pc=0x800025d4#32 := by simpa only [length,ite_false] using pe
      obtain ⟨d,sd,pd,dr,dc⟩ := MainCloseValueTail.next B e ram delimiter pe' ((er 11).trans a11) ((er 8).trans a8)
      have rejects := MainCloseTokenMath.other_length (TrimMath.trim xs) length
      refine ⟨n+1+1,d,by omega,(sa.trans se).trans sd,?_,?_,dc.trans (ec.trans ac)⟩
      · rw [rejects]
        by_cases comma : delimiter=44#32 <;> simpa [comma] using pd
      · intro r n15 n22 n23 n24 n25 n26
        exact (dr r).trans ((er r).trans (ar r n15 n22 n23 n24 n25 n26))
end E5R.Thermostat.MainCloseToken
