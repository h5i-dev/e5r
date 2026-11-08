import Projects.thermostat.MainCloseNameCompare
import Projects.thermostat.MainCloseConnectionSpec
set_option autoImplicit false
set_option maxRecDepth 4000
namespace E5R.Thermostat.MainCloseNameChain
open E5R E5R.Thermostat

def Frame (c d : Core) : Prop := ∀ r : Reg, r≠14 → r≠15 → r≠22 → d.get r=c.get r

theorem Frame.trans {a b c : Core} (h : Frame a b) (k : Frame b c) : Frame a c :=
  fun r x y z => (k r x y z).trans (h r x y z)

structure Literals (c : Core) : Prop where
  c6 : c.get 6=99#32
  c7 : c.get 7=111#32
  c28 : c.get 28=110#32
  c29 : c.get 29=101#32
  c30 : c.get 30=116#32
  c31 : c.get 31=105#32

theorem Literals.preserve {c d : Core} (h : Literals c) (frame : Frame c d) : Literals d :=
  ⟨(frame _ (by decide) (by decide) (by decide)).trans h.c6,
   (frame _ (by decide) (by decide) (by decide)).trans h.c7,
   (frame _ (by decide) (by decide) (by decide)).trans h.c28,
   (frame _ (by decide) (by decide) (by decide)).trans h.c29,
   (frame _ (by decide) (by decide) (by decide)).trans h.c30,
   (frame _ (by decide) (by decide) (by decide)).trans h.c31⟩

def accepts9 (g : Nat → BitVec 8) : Bool := decide (HeaderSpec.lower (g 9)=110#8)

def accepts8 (g : Nat → BitVec 8) : Bool := decide (HeaderSpec.lower (g 8)=111#8) && accepts9 g

def accepts7 (g : Nat → BitVec 8) : Bool := decide (HeaderSpec.lower (g 7)=105#8) && accepts8 g

def accepts6 (g : Nat → BitVec 8) : Bool := decide (HeaderSpec.lower (g 6)=116#8) && accepts7 g

def accepts5 (g : Nat → BitVec 8) : Bool := decide (HeaderSpec.lower (g 5)=99#8) && accepts6 g

def accepts4 (g : Nat → BitVec 8) : Bool := decide (HeaderSpec.lower (g 4)=101#8) && accepts5 g

def accepts3 (g : Nat → BitVec 8) : Bool := decide (HeaderSpec.lower (g 3)=110#8) && accepts4 g

def accepts2 (g : Nat → BitVec 8) : Bool := decide (HeaderSpec.lower (g 2)=110#8) && accepts3 g

def accepts1 (g : Nat → BitVec 8) : Bool := decide (HeaderSpec.lower (g 1)=111#8) && accepts2 g

def accepts0 (g : Nat → BitVec 8) : Bool := decide (HeaderSpec.lower (g 0)=99#8) && accepts1 g

theorem accepts_all (g : Nat → BitVec 8) : accepts0 g=MainCloseConnectionSpec.all g := by
  simp [accepts0,accepts1,accepts2,accepts3,accepts4,accepts5,accepts6,accepts7,accepts8,accepts9,MainCloseConnectionSpec.all,MainCloseConnectionSpec.folded,MainCloseConnectionSpec.connection,Bool.and_assoc]

theorem from9 (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (g : Nat → BitVec 8)
    (hp : c.pc=0x80002560#32) (h15 : c.get 15=base) (literals : Literals c)
    (memory : ∀ k, 9≤k → k<10 → B.inRam (base+BitVec.ofNat 32 k) 1=true)
    (data : ∀ k, 9≤k → k<10 → ram (base+BitVec.ofNat 32 k)=g k) :
    ∃ n d, n≤6 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if accepts9 g then 0x80002574#32 else 0x80002474#32) ∧ Frame c d ∧ d.sameCsr c := by
  obtain ⟨a,step,pa,_,ar,ac⟩ := MainCloseNameCompare.at2147493216 B c ram base (g 9) hp h15 literals.c28
    (memory 9 (by omega) (by omega)) (data 9 (by omega) (by omega))
  have frame : Frame c a := fun r n14 n15 n22 => ar r n14 n15
  refine ⟨6,a,by omega,step,?_,frame,ac⟩
  by_cases equal : HeaderSpec.lower (g 9)=110#8
  · simpa [accepts9,equal] using pa
  · simpa [accepts9,equal] using pa

theorem from8 (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (g : Nat → BitVec 8)
    (hp : c.pc=0x8000254a#32) (h15 : c.get 15=base) (literals : Literals c)
    (memory : ∀ k, 8≤k → k<10 → B.inRam (base+BitVec.ofNat 32 k) 1=true)
    (data : ∀ k, 8≤k → k<10 → ram (base+BitVec.ofNat 32 k)=g k) :
    ∃ n d, n≤12 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if accepts8 g then 0x80002574#32 else 0x80002474#32) ∧ Frame c d ∧ d.sameCsr c := by
  obtain ⟨a,step,pa,_,ar,ac⟩ := MainCloseNameCompare.at2147493194 B c ram base (g 8) hp h15 literals.c7
    (memory 8 (by omega) (by omega)) (data 8 (by omega) (by omega))
  have frame : Frame c a := fun r n14 n15 n22 => ar r n14 n22
  by_cases equal : HeaderSpec.lower (g 8)=111#8
  · have notUnequal : ¬HeaderSpec.lower (g 8)≠111#8 := not_not_intro equal
    have next : a.pc=0x80002560#32 := by simpa only [notUnequal,ite_false] using pa
    obtain ⟨n,d,nb,tail,pd,dr,dc⟩ := from9 B a ram base g next
      ((ar 15 (by decide) (by decide)).trans h15) (literals.preserve frame)
      (fun k lo hi => memory k (by omega) hi) (fun k lo hi => data k (by omega) hi)
    refine ⟨6+n,d,by omega,step.trans tail,?_,frame.trans dr,dc.trans ac⟩
    simpa only [accepts8,equal,decide_true,Bool.true_and] using pd
  · have failed : a.pc=0x80002474#32 := by simpa [equal] using pa
    refine ⟨6,a,by omega,step,?_,frame,ac⟩
    simpa only [accepts8,equal,decide_false,Bool.false_and,Bool.false_eq_true,ite_false] using failed

theorem from7 (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (g : Nat → BitVec 8)
    (hp : c.pc=0x80002534#32) (h15 : c.get 15=base) (literals : Literals c)
    (memory : ∀ k, 7≤k → k<10 → B.inRam (base+BitVec.ofNat 32 k) 1=true)
    (data : ∀ k, 7≤k → k<10 → ram (base+BitVec.ofNat 32 k)=g k) :
    ∃ n d, n≤18 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if accepts7 g then 0x80002574#32 else 0x80002474#32) ∧ Frame c d ∧ d.sameCsr c := by
  obtain ⟨a,step,pa,_,ar,ac⟩ := MainCloseNameCompare.at2147493172 B c ram base (g 7) hp h15 literals.c31
    (memory 7 (by omega) (by omega)) (data 7 (by omega) (by omega))
  have frame : Frame c a := fun r n14 n15 n22 => ar r n14 n22
  by_cases equal : HeaderSpec.lower (g 7)=105#8
  · have notUnequal : ¬HeaderSpec.lower (g 7)≠105#8 := not_not_intro equal
    have next : a.pc=0x8000254a#32 := by simpa only [notUnequal,ite_false] using pa
    obtain ⟨n,d,nb,tail,pd,dr,dc⟩ := from8 B a ram base g next
      ((ar 15 (by decide) (by decide)).trans h15) (literals.preserve frame)
      (fun k lo hi => memory k (by omega) hi) (fun k lo hi => data k (by omega) hi)
    refine ⟨6+n,d,by omega,step.trans tail,?_,frame.trans dr,dc.trans ac⟩
    simpa only [accepts7,equal,decide_true,Bool.true_and] using pd
  · have failed : a.pc=0x80002474#32 := by simpa [equal] using pa
    refine ⟨6,a,by omega,step,?_,frame,ac⟩
    simpa only [accepts7,equal,decide_false,Bool.false_and,Bool.false_eq_true,ite_false] using failed

theorem from6 (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (g : Nat → BitVec 8)
    (hp : c.pc=0x8000251e#32) (h15 : c.get 15=base) (literals : Literals c)
    (memory : ∀ k, 6≤k → k<10 → B.inRam (base+BitVec.ofNat 32 k) 1=true)
    (data : ∀ k, 6≤k → k<10 → ram (base+BitVec.ofNat 32 k)=g k) :
    ∃ n d, n≤24 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if accepts6 g then 0x80002574#32 else 0x80002474#32) ∧ Frame c d ∧ d.sameCsr c := by
  obtain ⟨a,step,pa,_,ar,ac⟩ := MainCloseNameCompare.at2147493150 B c ram base (g 6) hp h15 literals.c30
    (memory 6 (by omega) (by omega)) (data 6 (by omega) (by omega))
  have frame : Frame c a := fun r n14 n15 n22 => ar r n14 n22
  by_cases equal : HeaderSpec.lower (g 6)=116#8
  · have notUnequal : ¬HeaderSpec.lower (g 6)≠116#8 := not_not_intro equal
    have next : a.pc=0x80002534#32 := by simpa only [notUnequal,ite_false] using pa
    obtain ⟨n,d,nb,tail,pd,dr,dc⟩ := from7 B a ram base g next
      ((ar 15 (by decide) (by decide)).trans h15) (literals.preserve frame)
      (fun k lo hi => memory k (by omega) hi) (fun k lo hi => data k (by omega) hi)
    refine ⟨6+n,d,by omega,step.trans tail,?_,frame.trans dr,dc.trans ac⟩
    simpa only [accepts6,equal,decide_true,Bool.true_and] using pd
  · have failed : a.pc=0x80002474#32 := by simpa [equal] using pa
    refine ⟨6,a,by omega,step,?_,frame,ac⟩
    simpa only [accepts6,equal,decide_false,Bool.false_and,Bool.false_eq_true,ite_false] using failed

theorem from5 (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (g : Nat → BitVec 8)
    (hp : c.pc=0x80002508#32) (h15 : c.get 15=base) (literals : Literals c)
    (memory : ∀ k, 5≤k → k<10 → B.inRam (base+BitVec.ofNat 32 k) 1=true)
    (data : ∀ k, 5≤k → k<10 → ram (base+BitVec.ofNat 32 k)=g k) :
    ∃ n d, n≤30 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if accepts5 g then 0x80002574#32 else 0x80002474#32) ∧ Frame c d ∧ d.sameCsr c := by
  obtain ⟨a,step,pa,_,ar,ac⟩ := MainCloseNameCompare.at2147493128 B c ram base (g 5) hp h15 literals.c6
    (memory 5 (by omega) (by omega)) (data 5 (by omega) (by omega))
  have frame : Frame c a := fun r n14 n15 n22 => ar r n14 n22
  by_cases equal : HeaderSpec.lower (g 5)=99#8
  · have notUnequal : ¬HeaderSpec.lower (g 5)≠99#8 := not_not_intro equal
    have next : a.pc=0x8000251e#32 := by simpa only [notUnequal,ite_false] using pa
    obtain ⟨n,d,nb,tail,pd,dr,dc⟩ := from6 B a ram base g next
      ((ar 15 (by decide) (by decide)).trans h15) (literals.preserve frame)
      (fun k lo hi => memory k (by omega) hi) (fun k lo hi => data k (by omega) hi)
    refine ⟨6+n,d,by omega,step.trans tail,?_,frame.trans dr,dc.trans ac⟩
    simpa only [accepts5,equal,decide_true,Bool.true_and] using pd
  · have failed : a.pc=0x80002474#32 := by simpa [equal] using pa
    refine ⟨6,a,by omega,step,?_,frame,ac⟩
    simpa only [accepts5,equal,decide_false,Bool.false_and,Bool.false_eq_true,ite_false] using failed

theorem from4 (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (g : Nat → BitVec 8)
    (hp : c.pc=0x800024f2#32) (h15 : c.get 15=base) (literals : Literals c)
    (memory : ∀ k, 4≤k → k<10 → B.inRam (base+BitVec.ofNat 32 k) 1=true)
    (data : ∀ k, 4≤k → k<10 → ram (base+BitVec.ofNat 32 k)=g k) :
    ∃ n d, n≤36 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if accepts4 g then 0x80002574#32 else 0x80002474#32) ∧ Frame c d ∧ d.sameCsr c := by
  obtain ⟨a,step,pa,_,ar,ac⟩ := MainCloseNameCompare.at2147493106 B c ram base (g 4) hp h15 literals.c29
    (memory 4 (by omega) (by omega)) (data 4 (by omega) (by omega))
  have frame : Frame c a := fun r n14 n15 n22 => ar r n14 n22
  by_cases equal : HeaderSpec.lower (g 4)=101#8
  · have notUnequal : ¬HeaderSpec.lower (g 4)≠101#8 := not_not_intro equal
    have next : a.pc=0x80002508#32 := by simpa only [notUnequal,ite_false] using pa
    obtain ⟨n,d,nb,tail,pd,dr,dc⟩ := from5 B a ram base g next
      ((ar 15 (by decide) (by decide)).trans h15) (literals.preserve frame)
      (fun k lo hi => memory k (by omega) hi) (fun k lo hi => data k (by omega) hi)
    refine ⟨6+n,d,by omega,step.trans tail,?_,frame.trans dr,dc.trans ac⟩
    simpa only [accepts4,equal,decide_true,Bool.true_and] using pd
  · have failed : a.pc=0x80002474#32 := by simpa [equal] using pa
    refine ⟨6,a,by omega,step,?_,frame,ac⟩
    simpa only [accepts4,equal,decide_false,Bool.false_and,Bool.false_eq_true,ite_false] using failed

theorem from3 (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (g : Nat → BitVec 8)
    (hp : c.pc=0x800024dc#32) (h15 : c.get 15=base) (literals : Literals c)
    (memory : ∀ k, 3≤k → k<10 → B.inRam (base+BitVec.ofNat 32 k) 1=true)
    (data : ∀ k, 3≤k → k<10 → ram (base+BitVec.ofNat 32 k)=g k) :
    ∃ n d, n≤42 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if accepts3 g then 0x80002574#32 else 0x80002474#32) ∧ Frame c d ∧ d.sameCsr c := by
  obtain ⟨a,step,pa,_,ar,ac⟩ := MainCloseNameCompare.at2147493084 B c ram base (g 3) hp h15 literals.c28
    (memory 3 (by omega) (by omega)) (data 3 (by omega) (by omega))
  have frame : Frame c a := fun r n14 n15 n22 => ar r n14 n22
  by_cases equal : HeaderSpec.lower (g 3)=110#8
  · have notUnequal : ¬HeaderSpec.lower (g 3)≠110#8 := not_not_intro equal
    have next : a.pc=0x800024f2#32 := by simpa only [notUnequal,ite_false] using pa
    obtain ⟨n,d,nb,tail,pd,dr,dc⟩ := from4 B a ram base g next
      ((ar 15 (by decide) (by decide)).trans h15) (literals.preserve frame)
      (fun k lo hi => memory k (by omega) hi) (fun k lo hi => data k (by omega) hi)
    refine ⟨6+n,d,by omega,step.trans tail,?_,frame.trans dr,dc.trans ac⟩
    simpa only [accepts3,equal,decide_true,Bool.true_and] using pd
  · have failed : a.pc=0x80002474#32 := by simpa [equal] using pa
    refine ⟨6,a,by omega,step,?_,frame,ac⟩
    simpa only [accepts3,equal,decide_false,Bool.false_and,Bool.false_eq_true,ite_false] using failed

theorem from2 (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (g : Nat → BitVec 8)
    (hp : c.pc=0x800024c6#32) (h15 : c.get 15=base) (literals : Literals c)
    (memory : ∀ k, 2≤k → k<10 → B.inRam (base+BitVec.ofNat 32 k) 1=true)
    (data : ∀ k, 2≤k → k<10 → ram (base+BitVec.ofNat 32 k)=g k) :
    ∃ n d, n≤48 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if accepts2 g then 0x80002574#32 else 0x80002474#32) ∧ Frame c d ∧ d.sameCsr c := by
  obtain ⟨a,step,pa,_,ar,ac⟩ := MainCloseNameCompare.at2147493062 B c ram base (g 2) hp h15 literals.c28
    (memory 2 (by omega) (by omega)) (data 2 (by omega) (by omega))
  have frame : Frame c a := fun r n14 n15 n22 => ar r n14 n22
  by_cases equal : HeaderSpec.lower (g 2)=110#8
  · have notUnequal : ¬HeaderSpec.lower (g 2)≠110#8 := not_not_intro equal
    have next : a.pc=0x800024dc#32 := by simpa only [notUnequal,ite_false] using pa
    obtain ⟨n,d,nb,tail,pd,dr,dc⟩ := from3 B a ram base g next
      ((ar 15 (by decide) (by decide)).trans h15) (literals.preserve frame)
      (fun k lo hi => memory k (by omega) hi) (fun k lo hi => data k (by omega) hi)
    refine ⟨6+n,d,by omega,step.trans tail,?_,frame.trans dr,dc.trans ac⟩
    simpa only [accepts2,equal,decide_true,Bool.true_and] using pd
  · have failed : a.pc=0x80002474#32 := by simpa [equal] using pa
    refine ⟨6,a,by omega,step,?_,frame,ac⟩
    simpa only [accepts2,equal,decide_false,Bool.false_and,Bool.false_eq_true,ite_false] using failed

theorem from1 (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (g : Nat → BitVec 8)
    (hp : c.pc=0x800024b0#32) (h15 : c.get 15=base) (literals : Literals c)
    (memory : ∀ k, 1≤k → k<10 → B.inRam (base+BitVec.ofNat 32 k) 1=true)
    (data : ∀ k, 1≤k → k<10 → ram (base+BitVec.ofNat 32 k)=g k) :
    ∃ n d, n≤54 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if accepts1 g then 0x80002574#32 else 0x80002474#32) ∧ Frame c d ∧ d.sameCsr c := by
  obtain ⟨a,step,pa,_,ar,ac⟩ := MainCloseNameCompare.at2147493040 B c ram base (g 1) hp h15 literals.c7
    (memory 1 (by omega) (by omega)) (data 1 (by omega) (by omega))
  have frame : Frame c a := fun r n14 n15 n22 => ar r n14 n22
  by_cases equal : HeaderSpec.lower (g 1)=111#8
  · have notUnequal : ¬HeaderSpec.lower (g 1)≠111#8 := not_not_intro equal
    have next : a.pc=0x800024c6#32 := by simpa only [notUnequal,ite_false] using pa
    obtain ⟨n,d,nb,tail,pd,dr,dc⟩ := from2 B a ram base g next
      ((ar 15 (by decide) (by decide)).trans h15) (literals.preserve frame)
      (fun k lo hi => memory k (by omega) hi) (fun k lo hi => data k (by omega) hi)
    refine ⟨6+n,d,by omega,step.trans tail,?_,frame.trans dr,dc.trans ac⟩
    simpa only [accepts1,equal,decide_true,Bool.true_and] using pd
  · have failed : a.pc=0x80002474#32 := by simpa [equal] using pa
    refine ⟨6,a,by omega,step,?_,frame,ac⟩
    simpa only [accepts1,equal,decide_false,Bool.false_and,Bool.false_eq_true,ite_false] using failed

theorem from0 (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (g : Nat → BitVec 8)
    (hp : c.pc=0x8000249a#32) (h15 : c.get 15=base) (literals : Literals c)
    (memory : ∀ k, 0≤k → k<10 → B.inRam (base+BitVec.ofNat 32 k) 1=true)
    (data : ∀ k, 0≤k → k<10 → ram (base+BitVec.ofNat 32 k)=g k) :
    ∃ n d, n≤60 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if accepts0 g then 0x80002574#32 else 0x80002474#32) ∧ Frame c d ∧ d.sameCsr c := by
  obtain ⟨a,step,pa,_,ar,ac⟩ := MainCloseNameCompare.at2147493018 B c ram base (g 0) hp h15 literals.c6
    (memory 0 (by omega) (by omega)) (data 0 (by omega) (by omega))
  have frame : Frame c a := fun r n14 n15 n22 => ar r n14 n22
  by_cases equal : HeaderSpec.lower (g 0)=99#8
  · have notUnequal : ¬HeaderSpec.lower (g 0)≠99#8 := not_not_intro equal
    have next : a.pc=0x800024b0#32 := by simpa only [notUnequal,ite_false] using pa
    obtain ⟨n,d,nb,tail,pd,dr,dc⟩ := from1 B a ram base g next
      ((ar 15 (by decide) (by decide)).trans h15) (literals.preserve frame)
      (fun k lo hi => memory k (by omega) hi) (fun k lo hi => data k (by omega) hi)
    refine ⟨6+n,d,by omega,step.trans tail,?_,frame.trans dr,dc.trans ac⟩
    simpa only [accepts0,equal,decide_true,Bool.true_and] using pd
  · have failed : a.pc=0x80002474#32 := by simpa [equal] using pa
    refine ⟨6,a,by omega,step,?_,frame,ac⟩
    simpa only [accepts0,equal,decide_false,Bool.false_and,Bool.false_eq_true,ite_false] using failed

/-- All ten actual load/fold/branch groups, with early rejection. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (g : Nat → BitVec 8)
    (hp : c.pc=0x8000249a#32) (h15 : c.get 15=base) (literals : Literals c)
    (memory : ∀ k, k<10 → B.inRam (base+BitVec.ofNat 32 k) 1=true)
    (data : ∀ k, k<10 → ram (base+BitVec.ofNat 32 k)=g k) :
    ∃ n d, n≤60 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if MainCloseConnectionSpec.all g then 0x80002574#32 else 0x80002474#32) ∧ Frame c d ∧ d.sameCsr c := by
  simpa only [accepts_all] using from0 B c ram base g hp h15 literals
    (fun k _ hi => memory k hi) (fun k _ hi => data k hi)
end E5R.Thermostat.MainCloseNameChain
