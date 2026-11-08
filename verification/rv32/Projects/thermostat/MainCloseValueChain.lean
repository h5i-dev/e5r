import Projects.thermostat.MainCloseValueCompare
import Projects.thermostat.MainCloseFiveSpec
set_option autoImplicit false
set_option maxRecDepth 4000
namespace E5R.Thermostat.MainCloseValueChain
open E5R E5R.Thermostat

def Frame (c d : Core) : Prop := ∀ r : Reg, r≠15 → r≠22 → r≠23 → d.get r=c.get r

theorem Frame.trans {a b c : Core} (h : Frame a b) (k : Frame b c) : Frame a c :=
  fun r x y z => (k r x y z).trans (h r x y z)

structure Literals (c : Core) : Prop where
  c6 : c.get 6=99#32
  c19 : c.get 19=108#32
  c7 : c.get 7=111#32
  c20 : c.get 20=115#32

theorem Literals.preserve {c d : Core} (h : Literals c) (frame : Frame c d) : Literals d :=
  ⟨(frame _ (by decide) (by decide) (by decide)).trans h.c6,
   (frame _ (by decide) (by decide) (by decide)).trans h.c19,
   (frame _ (by decide) (by decide) (by decide)).trans h.c7,
   (frame _ (by decide) (by decide) (by decide)).trans h.c20⟩

def accepts4 (_g : Nat → BitVec 8) : Bool := true

def accepts3 (g : Nat → BitVec 8) : Bool := decide (HeaderSpec.lower (g 3)=115#8) && accepts4 g

def accepts2 (g : Nat → BitVec 8) : Bool := decide (HeaderSpec.lower (g 2)=111#8) && accepts3 g

def accepts1 (g : Nat → BitVec 8) : Bool := decide (HeaderSpec.lower (g 1)=108#8) && accepts2 g

def accepts0 (g : Nat → BitVec 8) : Bool := decide (HeaderSpec.lower (g 0)=99#8) && accepts1 g

theorem accepts_all (g : Nat → BitVec 8) :
    MainCloseFiveSpec.all g=(accepts0 g && decide (HeaderSpec.lower (g 4)=101#8)) := by
  simp [accepts0,accepts1,accepts2,accepts3,accepts4,MainCloseFiveSpec.all,MainCloseFiveSpec.folded,MainCloseFiveSpec.close,Bool.and_assoc]

theorem from4 (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (g : Nat → BitVec 8)
    (hp : c.pc=0x80002660#32) (h15 : c.get 15=base) (_literals : Literals c)
    (memory : ∀ k, 4≤k → k<5 → B.inRam (base+BitVec.ofNat 32 k) 1=true)
    (data : ∀ k, 4≤k → k<5 → ram (base+BitVec.ofNat 32 k)=g k) :
    ∃ n d, n≤5 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if accepts4 g then 0x80002672#32 else 0x800025d4#32) ∧ Frame c d ∧
      (accepts4 g=true → d.get 15=BitVec.ofNat 32 (HeaderSpec.lower (g 4)).toNat) ∧ d.sameCsr c := by
  obtain ⟨d,trace,pc,value,frame,csr⟩ := MainCloseValueCompare.lastByte B c ram base (g 4) hp h15
    (memory 4 (by omega) (by omega)) (data 4 (by omega) (by omega))
  exact ⟨5,d,by omega,trace,pc,fun r n15 n22 _ => frame r n15 n22,fun _ => value,csr⟩

theorem from3 (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (g : Nat → BitVec 8)
    (hp : c.pc=0x8000264a#32) (h15 : c.get 15=base) (literals : Literals c)
    (memory : ∀ k, 3≤k → k<5 → B.inRam (base+BitVec.ofNat 32 k) 1=true)
    (data : ∀ k, 3≤k → k<5 → ram (base+BitVec.ofNat 32 k)=g k) :
    ∃ n d, n≤11 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if accepts3 g then 0x80002672#32 else 0x800025d4#32) ∧ Frame c d ∧
      (accepts3 g=true → d.get 15=BitVec.ofNat 32 (HeaderSpec.lower (g 4)).toNat) ∧ d.sameCsr c := by
  obtain ⟨a,step,pa,_,ar,ac⟩ := MainCloseValueCompare.byte3 B c ram base (g 3) hp h15 literals.c20
    (memory 3 (by omega) (by omega)) (data 3 (by omega) (by omega))
  have frame : Frame c a := fun r _ n22 n23 => ar r n22 n23
  by_cases equal : HeaderSpec.lower (g 3)=115#8
  · have notUnequal : ¬HeaderSpec.lower (g 3)≠115#8 := not_not_intro equal
    have next : a.pc=0x80002660#32 := by simpa only [notUnequal,ite_false] using pa
    obtain ⟨n,d,nb,tail,pd,dr,value,dc⟩ := from4 B a ram base g next
      ((ar 15 (by decide) (by decide)).trans h15) (literals.preserve frame)
      (fun k lo hi => memory k (by omega) hi) (fun k lo hi => data k (by omega) hi)
    refine ⟨6+n,d,by omega,step.trans tail,?_,frame.trans dr,?_,dc.trans ac⟩
    · simpa only [accepts3,equal,decide_true,Bool.true_and] using pd
    · simpa only [accepts3,equal,decide_true,Bool.true_and] using value
  · have failed : a.pc=0x800025d4#32 := by simpa [equal] using pa
    refine ⟨6,a,by omega,step,?_,frame,?_,ac⟩
    · simpa only [accepts3,equal,decide_false,Bool.false_and,Bool.false_eq_true,ite_false] using failed
    · simp only [accepts3,equal,decide_false,Bool.false_and,Bool.false_eq_true,false_implies]

theorem from2 (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (g : Nat → BitVec 8)
    (hp : c.pc=0x80002634#32) (h15 : c.get 15=base) (literals : Literals c)
    (memory : ∀ k, 2≤k → k<5 → B.inRam (base+BitVec.ofNat 32 k) 1=true)
    (data : ∀ k, 2≤k → k<5 → ram (base+BitVec.ofNat 32 k)=g k) :
    ∃ n d, n≤17 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if accepts2 g then 0x80002672#32 else 0x800025d4#32) ∧ Frame c d ∧
      (accepts2 g=true → d.get 15=BitVec.ofNat 32 (HeaderSpec.lower (g 4)).toNat) ∧ d.sameCsr c := by
  obtain ⟨a,step,pa,_,ar,ac⟩ := MainCloseValueCompare.byte2 B c ram base (g 2) hp h15 literals.c7
    (memory 2 (by omega) (by omega)) (data 2 (by omega) (by omega))
  have frame : Frame c a := fun r _ n22 n23 => ar r n22 n23
  by_cases equal : HeaderSpec.lower (g 2)=111#8
  · have notUnequal : ¬HeaderSpec.lower (g 2)≠111#8 := not_not_intro equal
    have next : a.pc=0x8000264a#32 := by simpa only [notUnequal,ite_false] using pa
    obtain ⟨n,d,nb,tail,pd,dr,value,dc⟩ := from3 B a ram base g next
      ((ar 15 (by decide) (by decide)).trans h15) (literals.preserve frame)
      (fun k lo hi => memory k (by omega) hi) (fun k lo hi => data k (by omega) hi)
    refine ⟨6+n,d,by omega,step.trans tail,?_,frame.trans dr,?_,dc.trans ac⟩
    · simpa only [accepts2,equal,decide_true,Bool.true_and] using pd
    · simpa only [accepts2,equal,decide_true,Bool.true_and] using value
  · have failed : a.pc=0x800025d4#32 := by simpa [equal] using pa
    refine ⟨6,a,by omega,step,?_,frame,?_,ac⟩
    · simpa only [accepts2,equal,decide_false,Bool.false_and,Bool.false_eq_true,ite_false] using failed
    · simp only [accepts2,equal,decide_false,Bool.false_and,Bool.false_eq_true,false_implies]

theorem from1 (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (g : Nat → BitVec 8)
    (hp : c.pc=0x8000261e#32) (h15 : c.get 15=base) (literals : Literals c)
    (memory : ∀ k, 1≤k → k<5 → B.inRam (base+BitVec.ofNat 32 k) 1=true)
    (data : ∀ k, 1≤k → k<5 → ram (base+BitVec.ofNat 32 k)=g k) :
    ∃ n d, n≤23 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if accepts1 g then 0x80002672#32 else 0x800025d4#32) ∧ Frame c d ∧
      (accepts1 g=true → d.get 15=BitVec.ofNat 32 (HeaderSpec.lower (g 4)).toNat) ∧ d.sameCsr c := by
  obtain ⟨a,step,pa,_,ar,ac⟩ := MainCloseValueCompare.byte1 B c ram base (g 1) hp h15 literals.c19
    (memory 1 (by omega) (by omega)) (data 1 (by omega) (by omega))
  have frame : Frame c a := fun r _ n22 n23 => ar r n22 n23
  by_cases equal : HeaderSpec.lower (g 1)=108#8
  · have notUnequal : ¬HeaderSpec.lower (g 1)≠108#8 := not_not_intro equal
    have next : a.pc=0x80002634#32 := by simpa only [notUnequal,ite_false] using pa
    obtain ⟨n,d,nb,tail,pd,dr,value,dc⟩ := from2 B a ram base g next
      ((ar 15 (by decide) (by decide)).trans h15) (literals.preserve frame)
      (fun k lo hi => memory k (by omega) hi) (fun k lo hi => data k (by omega) hi)
    refine ⟨6+n,d,by omega,step.trans tail,?_,frame.trans dr,?_,dc.trans ac⟩
    · simpa only [accepts1,equal,decide_true,Bool.true_and] using pd
    · simpa only [accepts1,equal,decide_true,Bool.true_and] using value
  · have failed : a.pc=0x800025d4#32 := by simpa [equal] using pa
    refine ⟨6,a,by omega,step,?_,frame,?_,ac⟩
    · simpa only [accepts1,equal,decide_false,Bool.false_and,Bool.false_eq_true,ite_false] using failed
    · simp only [accepts1,equal,decide_false,Bool.false_and,Bool.false_eq_true,false_implies]

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (g : Nat → BitVec 8)
    (hp : c.pc=0x8000260c#32) (h15 : c.get 15=base) (h25 : c.get 25=BitVec.ofNat 32 (g 0).toNat) (literals : Literals c)
    (memory : ∀ k, 1≤k → k<5 → B.inRam (base+BitVec.ofNat 32 k) 1=true)
    (data : ∀ k, 1≤k → k<5 → ram (base+BitVec.ofNat 32 k)=g k) :
    ∃ n d, n≤28 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if accepts0 g then 0x80002672#32 else 0x800025d4#32) ∧ Frame c d ∧
      (accepts0 g=true → d.get 15=BitVec.ofNat 32 (HeaderSpec.lower (g 4)).toNat) ∧ d.sameCsr c := by
  obtain ⟨a,step,pa,_,ar,ac⟩ := MainCloseValueCompare.first B c ram (g 0) hp h25 literals.c6
  have frame : Frame c a := fun r _ n22 _ => ar r n22
  by_cases equal : HeaderSpec.lower (g 0)=99#8
  · have notUnequal : ¬HeaderSpec.lower (g 0)≠99#8 := not_not_intro equal
    have next : a.pc=0x8000261e#32 := by simpa only [notUnequal,ite_false] using pa
    obtain ⟨n,d,nb,tail,pd,dr,value,dc⟩ := from1 B a ram base g next ((ar 15 (by decide)).trans h15) (literals.preserve frame) memory data
    refine ⟨5+n,d,by omega,step.trans tail,?_,frame.trans dr,?_,dc.trans ac⟩
    · simpa only [accepts0,equal,decide_true,Bool.true_and] using pd
    · simpa only [accepts0,equal,decide_true,Bool.true_and] using value
  · have failed : a.pc=0x800025d4#32 := by simpa [equal] using pa
    refine ⟨5,a,by omega,step,?_,frame,?_,ac⟩
    · simpa only [accepts0,equal,decide_false,Bool.false_and,Bool.false_eq_true,ite_false] using failed
    · simp only [accepts0,equal,decide_false,Bool.false_and,Bool.false_eq_true,false_implies]
end E5R.Thermostat.MainCloseValueChain
