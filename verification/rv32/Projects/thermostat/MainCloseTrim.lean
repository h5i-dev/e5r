import Projects.thermostat.MainCloseLeft
import Projects.thermostat.MainCloseRight
import Projects.thermostat.MainCloseTrimFlow
import Projects.thermostat.TrimLeft
import Projects.thermostat.TrimRight
set_option autoImplicit false
set_option maxRecDepth 4000
namespace E5R.Thermostat.MainCloseTrim
open E5R E5R.Thermostat

def Frame (c d : Core) : Prop := ∀ r : Reg, r≠15 → r≠22 → r≠23 → r≠24 → r≠25 → r≠26 → d.get r=c.get r

/-- Actual inlined token trim, including the saved first byte and the optimized
    exits for an all-white token. The scanner supplies a nonempty token. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (xs : List (BitVec 8))
    (span : Bytes.Span B ram p xs) (positive : 0<xs.length) (hp : c.pc=0x800025b0#32)
    (h22 : c.get 22=p) (h23 : c.get 23=BitVec.ofNat 32 xs.length)
    (h9 : c.get 9=23#32) (h21 : c.get 21=0x80001b#32) :
    ∃ n d, n≤18*xs.length+17 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if TrimMath.trim xs=[] then 0x800025d4#32 else 0x80002608#32) ∧
      d.get 15=p+BitVec.ofNat 32 (xs.length-(TrimMath.left xs).length) ∧
      d.get 24=BitVec.ofNat 32 (TrimMath.trim xs).length ∧
      Bytes.Span B ram (d.get 15) (TrimMath.trim xs) ∧
      (TrimMath.trim xs≠[] → d.get 25=BitVec.ofNat 32 (ram (d.get 15)).toNat) ∧ Frame c d ∧ d.sameCsr c := by
  let ds := TrimMath.left xs
  let q := p+BitVec.ofNat 32 (xs.length-ds.length)
  have dsBound : ds.length≤xs.length := TrimMath.left_length xs
  have dsSpan : Bytes.Span B ram q ds := TrimLeft.span B ram p xs span
  obtain ⟨u,su,pu,u15,u24,ur,uc⟩ := MainCloseTrimFlow.leftSetup B c ram p (BitVec.ofNat 32 xs.length) hp h22 h23
  obtain ⟨kl,a,lb,sl,pa,a24,a15,a25,ar,ac⟩ := MainCloseLeft.contract B u ram p xs span positive pu u15 u24
    ((ur 9 (by decide) (by decide)).trans h9) ((ur 21 (by decide) (by decide)).trans h21)
  have leftFrame : Frame c a := fun r n15 _ _ n24 n25 n26 => (ar r n15 n24 n25 n26).trans (ur r n15 n24)
  have leftPC : a.pc=(if ds=[] then 0x800025d4#32 else 0x800025e4#32) := pa
  have leftPtr : a.get 15=q := a15
  have leftCount : a.get 24=BitVec.ofNat 32 ds.length := a24
  by_cases empty : ds=[]
  · have trimEmpty : TrimMath.trim xs=[] := by change (ds.reverse.dropWhile TrimMath.white).reverse=[];rw [empty];rfl
    refine ⟨2+kl,a,by omega,su.trans sl,?_,a15,?_,?_,?_,leftFrame,ac.trans uc⟩
    · simpa only [trimEmpty,empty,ite_true] using leftPC
    · simpa only [trimEmpty,empty,List.length_nil] using leftCount
    · rw [trimEmpty]
      exact Bytes.empty B ram (a.get 15)
    · simp only [trimEmpty,ne_eq,not_true_eq_false,false_implies]
  · have dsPositive : 0<ds.length := List.length_pos_iff.mpr empty
    have pa' : a.pc=0x800025e4#32 := by simpa only [empty,ite_false] using leftPC
    have cache : a.get 25=BitVec.ofNat 32 (ram q).toNat := by
      have loaded := dsSpan.bytes ⟨0,dsPositive⟩
      change ram (q+0#32)=(ds[0]'(dsPositive)) at loaded
      have read : ram q=ds[0]?.getD 0#8 := by
        rw [List.getElem?_eq_getElem dsPositive]
        simpa only [BitVec.add_zero,Option.getD_some] using loaded
      rw [read]
      exact a25 empty
    obtain ⟨w,sw,pw,w22,wr,wc⟩ := MainCloseTrimFlow.rightSetup B a ram p (BitVec.ofNat 32 xs.length) pa'
      ((ar 22 (by decide) (by decide) (by decide) (by decide)).trans ((ur 22 (by decide) (by decide)).trans h22))
      ((ar 23 (by decide) (by decide) (by decide) (by decide)).trans ((ur 23 (by decide) (by decide)).trans h23))
    have lastAddress : (p+BitVec.ofNat 32 xs.length)+0xffffffff#32=q+BitVec.ofNat 32 (ds.length-1) :=
      TrimMath.end_pred p xs.length ds.length dsPositive dsBound
    obtain ⟨kr,d,rb,sr,pd,d24,dr,dc⟩ := MainCloseRight.contract B w ram q ds dsSpan dsPositive pw (w22.trans lastAddress)
      ((wr 24 (by decide)).trans leftCount)
      ((wr 9 (by decide)).trans ((leftFrame 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h9))
      ((wr 21 (by decide)).trans ((leftFrame 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h21))
    have d15 : d.get 15=q := (dr 15 (by decide) (by decide) (by decide)).trans ((wr 15 (by decide)).trans leftPtr)
    refine ⟨2+kl+2+kr,d,by omega,((su.trans sl).trans sw).trans sr,?_,d15,?_,?_,?_,?_,dc.trans (wc.trans (ac.trans uc))⟩
    · have emptyIff : TrimMath.trim xs=[] ↔ TrimMath.left ds.reverse=[] := by
        change (TrimMath.left ds.reverse).reverse=[] ↔ _
        simp only [List.reverse_eq_nil_iff]
      simpa only [←emptyIff] using pd
    · simpa only [TrimMath.trim,TrimMath.left,List.length_reverse,ds] using d24
    · rw [d15]
      exact TrimRight.span B ram q ds dsSpan
    · intro _
      rw [d15]
      exact (dr 25 (by decide) (by decide) (by decide)).trans ((wr 25 (by decide)).trans cache)
    · intro r n15 n22 n23 n24 n25 n26
      exact (dr r n22 n23 n24).trans ((wr r n22).trans (leftFrame r n15 n22 n23 n24 n25 n26))
end E5R.Thermostat.MainCloseTrim
