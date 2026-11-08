import Projects.thermostat.MainClosePiece
import Projects.thermostat.MainCloseNextToken
set_option autoImplicit false
set_option maxRecDepth 4000
namespace E5R.Thermostat.MainCloseValueLoop
open E5R E5R.Thermostat

/-- Entire actual comma-token loop for a nonempty value. Its instruction bound
    is linear in the original byte count; every recursive call consumes its
    first comma and token. RAM and all non-scratch registers are preserved. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (xs : List (BitVec 8))
    (span : Bytes.Span B ram base xs) (positive : 0<xs.length) (hp : c.pc=0x80002584#32)
    (h22 : c.get 22=base) (h14 : c.get 14=BitVec.ofNat 32 xs.length)
    (h15 : c.get 15=base+BitVec.ofNat 32 xs.length) (literals : MainCloseValueContext.Literals c) :
    ∃ n d, n≤86*xs.length ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if MainCloseSpec.hasClose xs then 0x800026bc#32 else 0x80002474#32) ∧ MainCloseValueContext.Frame c d ∧ d.sameCsr c := by
  obtain ⟨n,a,nb,sa,pa,next,ar,ac⟩ := MainClosePiece.contract B c ram base xs span positive hp h22 h14 h15 literals
  have tokenBound := MainCloseScanSpec.bounded xs
  cases accepted : MainClosePiece.accepts xs with
  | true =>
    have result : MainCloseSpec.hasClose xs=true := by
      rw [MainCloseScanSpec.hasClose]
      change (MainClosePiece.accepts xs || _)=true
      simp only [accepted,Bool.true_or]
    refine ⟨n,a,by omega,sa,?_,ar,ac⟩
    simpa only [accepted,ite_true,result] using pa
  | false =>
    cases found : MainCloseScanSpec.rest xs with
    | none =>
      have result : MainCloseSpec.hasClose xs=false := by
        rw [MainCloseScanSpec.hasClose]
        change (MainClosePiece.accepts xs || _)=false
        simp only [accepted,Bool.false_or,found]
      refine ⟨n,a,by omega,sa,?_,ar,ac⟩
      simpa only [accepted,Bool.false_eq_true,ite_false,found,Option.isSome_none,result] using pa
    | some ys =>
      have corresponds : MainCloseSpec.hasClose xs=MainCloseSpec.hasClose ys := by
        rw [MainCloseScanSpec.hasClose]
        change (MainClosePiece.accepts xs || _)=_
        simp only [accepted,Bool.false_or,found]
      have pa' : a.pc=0x800025d8#32 := by simpa only [accepted,Bool.false_eq_true,ite_false,found,Option.isSome_some,ite_true] using pa
      have metadata := next ys found
      have spanNext := MainCloseScanSpec.rest_span span found
      obtain ⟨k,e,kb,se,pe,registers,er,ec⟩ := MainCloseNextToken.contract B a ram _ ys.length spanNext.length pa' metadata.1 metadata.2
      have ae : MainCloseValueContext.Frame a e := fun r _ _ _ n15 n22 _ _ _ _ => er r n15 n22
      cases ys with
      | nil =>
        have result : MainCloseSpec.hasClose xs=false := corresponds.trans (by decide +kernel)
        have sizes := MainCloseScanSpec.remaining xs [] found
        refine ⟨n+k,e,by simp only [List.length_nil] at sizes;omega,sa.trans se,?_,ar.trans ae,ec.trans ac⟩
        simpa only [result,Bool.false_eq_true,ite_false,List.length_nil,ite_true] using pe
      | cons b bs =>
        have nonzero : (b::bs).length≠0 := by simp
        have pe' : e.pc=0x80002584#32 := by simpa only [nonzero,ite_false] using pe
        have eRegs := registers nonzero
        have e14 : e.get 14=BitVec.ofNat 32 (b::bs).length := (er 14 (by decide) (by decide)).trans metadata.2
        obtain ⟨m,d,mb,sd,pd,dr,dc⟩ := contract B e ram _ (b::bs) spanNext (by simp) pe' eRegs.1 e14 eRegs.2
          ((literals.preserve ar).preserve ae)
        have sizes := MainCloseScanSpec.remaining xs (b::bs) found
        refine ⟨n+k+m,d,by omega,(sa.trans se).trans sd,?_,(ar.trans ae).trans dr,dc.trans (ec.trans ac)⟩
        simpa only [corresponds] using pd
termination_by xs.length
 decreasing_by
  have sizes := MainCloseScanSpec.remaining xs (b::bs) found
  omega
end E5R.Thermostat.MainCloseValueLoop
