import Projects.thermostat.MainCloseWhitespace
import Projects.thermostat.MainCloseTrimAdvance
import Projects.thermostat.ByteSlices
set_option autoImplicit false
set_option maxRecDepth 4000
namespace E5R.Thermostat.MainCloseRight
open E5R E5R.Thermostat

def Frame (c d : Core) : Prop := ∀ r : Reg, r≠22 → r≠23 → r≠24 → d.get r=c.get r

/-- Induction on the reverse list follows the actual backwards RAM loads. -/
theorem loop (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (ys : List (BitVec 8))
    (span : Bytes.Span B ram p ys.reverse) (positive : 0<ys.length)
    (hp : c.pc=0x800025e8#32) (h22 : c.get 22=p+BitVec.ofNat 32 (ys.length-1))
    (h24 : c.get 24=BitVec.ofNat 32 ys.length) (h9 : c.get 9=23#32) (h21 : c.get 21=0x80001b#32) :
    ∃ n d, n≤9*ys.length+6 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if TrimMath.left ys=[] then 0x80002606#32 else 0x80002608#32) ∧
      d.get 24=BitVec.ofNat 32 (TrimMath.left ys).length ∧ Frame c d ∧ d.sameCsr c := by
  induction ys generalizing c with
  | nil => simp at positive
  | cons b bs ih =>
    have span' : Bytes.Span B ram p (bs.reverse++[b]) := by simpa using span
    have memory : B.inRam (p+BitVec.ofNat 32 bs.length) 1=true := by
      simpa using span'.memory ⟨bs.length,by simp⟩
    have byte : ram (p+BitVec.ofNat 32 bs.length)=b := by
      have actual := span'.bytes ⟨bs.length,by simp⟩
      change ram (p+BitVec.ofNat 32 bs.length)=(bs.reverse++[b])[bs.length] at actual
      rw [List.getElem_append_right (by simp)] at actual
      simpa using actual
    have pointer : c.get 22=p+BitVec.ofNat 32 bs.length := by simpa using h22
    obtain ⟨k,a,kb,sa,pa,ar,ac⟩ := MainCloseWhitespace.rightTest B c ram _ b hp pointer h9 h21 memory byte
    cases white : TrimMath.white b with
    | false =>
      have hl : TrimMath.left (b::bs)=b::bs := by simp [TrimMath.left,white]
      refine ⟨k,a,by simp only [List.length_cons];omega,sa,?_,?_,?_,ac⟩
      · simpa only [hl,List.cons_ne_nil,ite_false,white,Bool.false_eq_true] using pa
      · simpa only [hl] using (ar 24 (by decide)).trans h24
      · intro r _ n23 _
        exact ar r n23
    | true =>
      have hl : TrimMath.left (b::bs)=TrimMath.left bs := by simp [TrimMath.left,white]
      have pa' : a.pc=0x800025fe#32 := by simpa only [white,ite_true] using pa
      obtain ⟨e,se,pe,e24,e22,er,ec⟩ := MainCloseTrimAdvance.right B a ram _ (b::bs).length positive
        (by simpa only [List.length_reverse] using span.length) pa'
        ((ar 24 (by decide)).trans h24) ((ar 22 (by decide)).trans pointer)
      have frame : Frame c e := fun r n22 n23 n24 => (er r n24 n22).trans (ar r n23)
      cases bs with
      | nil =>
        refine ⟨k+3,e,by simp;omega,sa.trans se,?_,?_,frame,ec.trans ac⟩
        · simpa [hl,TrimMath.left,white] using pe
        · simpa [hl,TrimMath.left,white] using e24
      | cons b' bs' =>
        have span0 : Bytes.Span B ram p (b'::bs').reverse := Bytes.left_part span'
        have address : (p+BitVec.ofNat 32 (b'::bs').length)+0xffffffff#32=p+BitVec.ofNat 32 ((b'::bs').length-1) := by
          rw [BitVec.add_assoc,TrimAdvanceProgram.decrement _ (by simp)]
        have pe' : e.pc=0x800025e8#32 := by simpa [show (b::b'::bs').length≠1 by simp] using pe
        have e24' : e.get 24=BitVec.ofNat 32 (b'::bs').length := by simpa only [List.length_cons,Nat.add_sub_cancel] using e24
        obtain ⟨m,d,mb,sd,pd,d24,dr,dc⟩ := ih e span0 (by simp) pe' (e22.trans address) e24'
          ((frame 9 (by decide) (by decide) (by decide)).trans h9)
          ((frame 21 (by decide) (by decide) (by decide)).trans h21)
        refine ⟨k+3+m,d,by simp only [List.length_cons] at mb ⊢;omega,(sa.trans se).trans sd,?_,?_,?_,dc.trans (ec.trans ac)⟩
        · simpa only [hl] using pd
        · simpa only [hl] using d24
        · intro r n22 n23 n24
          exact (dr r n22 n23 n24).trans (frame r n22 n23 n24)

theorem emptyJump (B : Board) (c : Core) (ram : Word → BitVec 8) (hp : c.pc=0x80002606#32) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800025d4#32 ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  let d := c.goto 0x800025d4#32
  have step : Quiet.Step B img ⟨c,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact re2147493382) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok d ram [],[]⟩
    rw [exec_jal,Core.set_zero,hp,show 0x80002606#32+0xffffffce#32=0x800025d4#32 by decide +kernel,jump_ok _ _ (by decide)]
    rfl
  exact ⟨d,.single step,rfl,fun _ => rfl,rfl⟩

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (xs : List (BitVec 8))
    (span : Bytes.Span B ram p xs) (positive : 0<xs.length)
    (hp : c.pc=0x800025e8#32) (h22 : c.get 22=p+BitVec.ofNat 32 (xs.length-1))
    (h24 : c.get 24=BitVec.ofNat 32 xs.length) (h9 : c.get 9=23#32) (h21 : c.get 21=0x80001b#32) :
    ∃ n d, n≤9*xs.length+7 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if TrimMath.left xs.reverse=[] then 0x800025d4#32 else 0x80002608#32) ∧
      d.get 24=BitVec.ofNat 32 (TrimMath.left xs.reverse).length ∧ Frame c d ∧ d.sameCsr c := by
  obtain ⟨n,a,nb,sa,pa,a24,ar,ac⟩ := loop B c ram p xs.reverse (by simpa using span) (by simpa using positive) hp
    (by simpa using h22) (by simpa using h24) h9 h21
  by_cases empty : TrimMath.left xs.reverse=[]
  · have pa' : a.pc=0x80002606#32 := by simpa only [empty,ite_true] using pa
    obtain ⟨d,sd,pd,dr,dc⟩ := emptyJump B a ram pa'
    refine ⟨n+1,d,by simp only [List.length_reverse] at nb;omega,sa.trans sd,?_,(dr 24).trans a24,?_,dc.trans ac⟩
    · simpa only [empty,ite_true] using pd
    · intro r n22 n23 n24
      exact (dr r).trans (ar r n22 n23 n24)
  · refine ⟨n,a,by simp only [List.length_reverse] at nb;omega,sa,?_,a24,ar,ac⟩
    simpa only [empty,ite_false] using pa
end E5R.Thermostat.MainCloseRight
