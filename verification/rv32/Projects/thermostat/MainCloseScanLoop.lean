import Projects.thermostat.MainCloseScanSpec
import Projects.thermostat.MainCloseScanHead
import Projects.thermostat.MainCloseScanAdvance
set_option autoImplicit false
set_option maxRecDepth 4000
namespace E5R.Thermostat.MainCloseScanLoop
open E5R E5R.Thermostat

def Frame (c d : Core) : Prop := ∀ r : Reg, r≠10 → r≠11 → r≠23 → d.get r=c.get r

/-- Actual first-comma scan. The absent-comma exit advances to the end before
    leaving, while a found comma leaves its own position in the index. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (i : Nat) (xs : List (BitVec 8))
    (span : Bytes.Span B ram (base+BitVec.ofNat 32 i) xs) (positive : 0<xs.length) (bound : i+xs.length<2^32)
    (hp : c.pc=0x80002586#32) (h22 : c.get 22=base) (h23 : c.get 23=BitVec.ofNat 32 i)
    (h15 : c.get 15=base+BitVec.ofNat 32 (i+xs.length)) (h8 : c.get 8=44#32) :
    ∃ n d, n≤6*(MainCloseScanSpec.token xs).length+6 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if (MainCloseScanSpec.rest xs).isSome then 0x800025a4#32 else 0x8000259c#32) ∧
      d.get 23=BitVec.ofNat 32 (i+(MainCloseScanSpec.token xs).length) ∧
      d.get 10=base+BitVec.ofNat 32 (i+(MainCloseScanSpec.token xs).length) ∧
      (d.get 11=44#32 ↔ (MainCloseScanSpec.rest xs).isSome=true) ∧ Frame c d ∧ d.sameCsr c := by
  induction xs generalizing c i with
  | nil => simp at positive
  | cons b bs ih =>
    obtain ⟨byte,memory⟩ := Bytes.head span
    obtain ⟨a,sa,pa,a10,a11,ar,ac⟩ := MainCloseScanHead.contract B c ram base i b hp h22 h23 h8 memory byte
    by_cases comma : b=44#8
    · have partition : MainCloseScanSpec.token (b::bs)=[] ∧ MainCloseScanSpec.rest (b::bs)=some bs := by
        simpa only [comma] using MainCloseScanSpec.hit bs
      refine ⟨3,a,by rw [partition.1];simp,sa,?_,?_,?_,?_,?_,ac⟩
      · rw [partition.2]
        simpa only [Option.isSome_some,ite_true,comma] using pa
      · simpa only [partition.1,List.length_nil,Nat.add_zero] using (ar 23 (by decide) (by decide)).trans h23
      · simpa only [partition.1,List.length_nil,Nat.add_zero] using a10
      · rw [partition.2,Option.isSome_some]
        have value : a.get 11=44#32 := by simpa only [comma,show BitVec.ofNat 32 (44#8).toNat=44#32 by decide +kernel] using a11
        simp only [value,true_iff]
      · intro r n10 n11 _
        exact ar r n10 n11
    · have partition := MainCloseScanSpec.miss b bs comma
      have pa' : a.pc=0x80002592#32 := by simpa only [comma,ite_false] using pa
      obtain ⟨e,se,pe,e10,e23,er,ec⟩ := MainCloseScanAdvance.contract B a ram base i (i+(b::bs).length)
        (by simp only [List.length_cons];omega) bound pa'
        ((ar 22 (by decide) (by decide)).trans h22) ((ar 23 (by decide) (by decide)).trans h23)
        ((ar 15 (by decide) (by decide)).trans h15)
      have frame : Frame c e := fun r n10 n11 n23 => (er r n10 n23).trans (ar r n10 n11)
      cases bs with
      | nil =>
        have absent : MainCloseScanSpec.rest (b::[])=none := by simpa only [MainCloseScanSpec.rest,MainCloseScanSpec.scan] using partition.2
        have token : MainCloseScanSpec.token (b::[])=[b] := by simpa only [MainCloseScanSpec.token,MainCloseScanSpec.scan] using partition.1
        have notComma : e.get 11≠44#32 := by
          rw [er 11 (by decide) (by decide),a11]
          intro equal
          have byteEqual : b=44#8 := (Literal.byte_injective b 44#8).mp equal
          exact comma byteEqual
        refine ⟨6,e,by simp only [token,List.length_cons,List.length_nil];omega,(sa.trans se),?_,?_,?_,?_,frame,ec.trans ac⟩
        · simpa only [absent,Option.isSome_none,Bool.false_eq_true,ite_false,List.length_cons,List.length_nil,ite_true] using pe
        · simpa only [token,List.length_cons,List.length_nil] using e23
        · simpa only [token,List.length_cons,List.length_nil] using e10
        · simp only [absent,Option.isSome_none,Bool.false_eq_true,notComma]
      | cons b' bs' =>
        have more : i+1≠i+(b::b'::bs').length := by simp only [List.length_cons];omega
        have pe' : e.pc=0x80002586#32 := by simpa only [more,ite_false] using pe
        have spanNext : Bytes.Span B ram (base+BitVec.ofNat 32 (i+1)) (b'::bs') := by
          simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using Bytes.tail span
        have endEq : i+(b::b'::bs').length=(i+1)+(b'::bs').length := by simp only [List.length_cons];omega
        have e15 : e.get 15=base+BitVec.ofNat 32 ((i+1)+(b'::bs').length) := by
          rw [er 15 (by decide) (by decide),ar 15 (by decide) (by decide),h15,endEq]
        obtain ⟨m,d,mb,sd,pd,d23,d10,delimiter,dr,dc⟩ := ih e (i+1) spanNext (by simp) (by rw [←endEq];exact bound) pe'
          ((frame 22 (by decide) (by decide) (by decide)).trans h22) e23 e15
          ((frame 8 (by decide) (by decide) (by decide)).trans h8)
        have offsetEq : i+(MainCloseScanSpec.token (b::b'::bs')).length=(i+1)+(MainCloseScanSpec.token (b'::bs')).length := by
          rw [partition.1,List.length_cons]
          omega
        refine ⟨6+m,d,by rw [partition.1,List.length_cons];omega,(sa.trans se).trans sd,?_,?_,?_,?_,?_,dc.trans (ec.trans ac)⟩
        · simpa only [partition.2] using pd
        · rw [offsetEq]
          exact d23
        · rw [offsetEq]
          exact d10
        · simpa only [partition.2] using delimiter
        · intro r n10 n11 n23
          exact (dr r n10 n11 n23).trans (frame r n10 n11 n23)
end E5R.Thermostat.MainCloseScanLoop
