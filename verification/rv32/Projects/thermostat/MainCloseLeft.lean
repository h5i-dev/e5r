import Projects.thermostat.MainCloseWhitespace
import Projects.thermostat.MainCloseTrimAdvance
import Projects.thermostat.Bytes
set_option autoImplicit false
set_option maxRecDepth 4000
namespace E5R.Thermostat.MainCloseLeft
open E5R E5R.Thermostat

def Frame (c d : Core) : Prop := ∀ r : Reg, r≠15 → r≠24 → r≠25 → r≠26 → d.get r=c.get r

/-- The actual leading-trim loop, retaining the nonwhite first byte used by
    the optimized close comparison. All-white slices exit without a load past
    the end; the cached byte is used only when the result is nonempty. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (xs : List (BitVec 8))
    (span : Bytes.Span B ram p xs) (positive : 0<xs.length)
    (hp : c.pc=0x800025b4#32) (h15 : c.get 15=p) (h24 : c.get 24=BitVec.ofNat 32 xs.length)
    (h9 : c.get 9=23#32) (h21 : c.get 21=0x80001b#32) :
    ∃ n d, n≤9*xs.length+6 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if TrimMath.left xs=[] then 0x800025d4#32 else 0x800025e4#32) ∧
      d.get 24=BitVec.ofNat 32 (TrimMath.left xs).length ∧
      d.get 15=p+BitVec.ofNat 32 (xs.length-(TrimMath.left xs).length) ∧
      (TrimMath.left xs≠[] → d.get 25=BitVec.ofNat 32 ((TrimMath.left xs)[0]?.getD 0#8).toNat) ∧
      Frame c d ∧ d.sameCsr c := by
  induction xs generalizing c p with
  | nil => simp at positive
  | cons b bs ih =>
    obtain ⟨byte,memory⟩ := Bytes.head span
    obtain ⟨k,a,kb,sa,pa,cache,ar,ac⟩ := MainCloseWhitespace.leftTest B c ram p b hp h15 h9 h21 memory byte
    cases white : TrimMath.white b with
    | false =>
      have hl : TrimMath.left (b::bs)=b::bs := by simp [TrimMath.left,List.dropWhile_cons,white]
      refine ⟨k,a,by simp only [List.length_cons];omega,sa,?_,?_,?_,?_,?_,ac⟩
      · simpa only [hl,List.cons_ne_nil,ite_false,white,Bool.false_eq_true] using pa
      · simpa only [hl] using (ar 24 (by decide) (by decide)).trans h24
      · simpa only [hl,Nat.sub_self,BitVec.add_zero] using (ar 15 (by decide) (by decide)).trans h15
      · intro _
        simpa only [hl,List.getElem?_cons_zero,Option.getD_some] using cache
      · intro r _ _ n25 n26
        exact ar r n25 n26
    | true =>
      have hl : TrimMath.left (b::bs)=TrimMath.left bs := by simp [TrimMath.left,List.dropWhile_cons,white]
      have pa' : a.pc=0x800025cc#32 := by simpa only [white,ite_true] using pa
      obtain ⟨e,se,pe,e24,e15,er,ec⟩ := MainCloseTrimAdvance.left B a ram p (b::bs).length positive span.length pa'
        ((ar 24 (by decide) (by decide)).trans h24) ((ar 15 (by decide) (by decide)).trans h15)
      have frame : Frame c e := fun r n15 n24 n25 n26 => (er r n24 n15).trans (ar r n25 n26)
      cases bs with
      | nil =>
        have empty : TrimMath.left ([] : List (BitVec 8))=[] := rfl
        refine ⟨k+3,e,by simp;omega,sa.trans se,?_,?_,?_,?_,frame,ec.trans ac⟩
        · simpa only [hl,empty,List.length_cons,List.length_nil,ite_true] using pe
        · simpa only [hl,empty,List.length_cons,List.length_nil,Nat.add_sub_cancel] using e24
        · simpa only [hl,empty,List.length_cons,List.length_nil,Nat.sub_zero] using e15
        · simp only [hl,empty,ne_eq,not_true_eq_false,false_implies]
      | cons b' bs' =>
        have pe' : e.pc=0x800025b4#32 := by simpa [show (b::b'::bs').length≠1 by simp] using pe
        have e24' : e.get 24=BitVec.ofNat 32 (b'::bs').length := by simpa only [List.length_cons,Nat.add_sub_cancel] using e24
        obtain ⟨m,d,mb,sd,pd,d24,d15,d25,dr,dc⟩ := ih e (p+1#32) (Bytes.tail span) (by simp) pe' e15 e24'
          ((frame 9 (by decide) (by decide) (by decide) (by decide)).trans h9)
          ((frame 21 (by decide) (by decide) (by decide) (by decide)).trans h21)
        refine ⟨k+3+m,d,by simp only [List.length_cons] at mb ⊢;omega,(sa.trans se).trans sd,?_,?_,?_,?_,?_,dc.trans (ec.trans ac)⟩
        · simpa only [hl] using pd
        · simpa only [hl] using d24
        · rw [hl,d15,BitVec.add_assoc,←BitVec.ofNat_add]
          have bounded := TrimMath.left_length (b'::bs')
          exact congrArg (fun n => p+BitVec.ofNat 32 n) (by simp only [List.length_cons] at bounded ⊢;omega)
        · simpa only [hl] using d25
        · intro r n15 n24 n25 n26
          exact (dr r n15 n24 n25 n26).trans (frame r n15 n24 n25 n26)
end E5R.Thermostat.MainCloseLeft
