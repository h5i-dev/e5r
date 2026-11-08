import Projects.thermostat.HeadClNumberStep
import Projects.thermostat.HeadClNumberAdvance
import Projects.thermostat.HeadClNumberSpec
namespace E5R.Thermostat.HeadClNumberLoop
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

def Post (d : Core) : Num → Prop
  | .bad status => d.pc=0x8000342c#32 ∧ d.get 1=BitVec.ofNat 32 status
  | .ok value => d.pc=0x8000325e#32 ∧ d.get 14=BitVec.ofNat 32 value ∧ d.get 13=0#32

/-- The actual complete CL decimal loop computes the independent bounded
    decimal specification; neither an unbounded input read nor arithmetic
    overflow is assumed away. RAM is unchanged until the separate final stores. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (pos finish length acc : Nat)
    (hp : c.pc=0x80003206#32) (h1 : c.get 1=400#32) (h2 : c.get 2=sp)
    (h10 : c.get 10=buf+BitVec.ofNat 32 pos) (h31 : c.get 31=BitVec.ofNat 32 (length-pos))
    (h11 : c.get 11=BitVec.ofNat 32 (finish-pos))
    (h14 : c.get 14=BitVec.ofNat 32 acc) (h13 : c.get 13=0#32) (h16 : c.get 16=10#32)
    (hlimit : ramRead ram (sp+8#32) .w=1024#32) (inside : pos<finish) (upper : finish≤length)
    (bound : length≤2048) (accepted : acc≤1024) (memory : Memory.Block B buf length)
    (stack : Memory.Block B sp 56) (aligned : sp.toNat%4=0) :
    ∃ n d, 0<n ∧ n≤30*(finish-pos) ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      Post d (clLoop (bytes ram buf) finish 1024 acc pos) ∧
      (∀ r : Reg, r≠1 → r≠30 → r≠12 → r≠29 → r≠14 → r≠13 → r≠11 → r≠10 → r≠31 → d.get r=c.get r) ∧ d.sameCsr c := by
  let g := bytes ram buf
  let byte := ram (buf+BitVec.ofNat 32 pos)
  change ∃ n d, 0<n ∧ n≤30*(finish-pos) ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
    Post d (clLoop g finish 1024 acc pos) ∧
    (∀ r : Reg, r≠1 → r≠30 → r≠12 → r≠29 → r≠14 → r≠13 → r≠11 → r≠10 → r≠31 → d.get r=c.get r) ∧ d.sameCsr c
  obtain ⟨n,a,lo,hi,step,pc,status,values,frame,csr⟩ := HeadClNumberStep.contract B c ram sp buf pos length acc hp h1 h2 h10 h31 h14 h13 h16 hlimit (by omega) bound accepted memory stack aligned
  change a.pc=(if HeadClNumberStep.good acc byte then 0x80003256#32 else 0x8000342c#32) at pc
  change a.get 1=HeadClNumberStep.status acc byte at status
  change (DecimalSpec.digit byte=true → _) at values
  have spec := HeadClNumberSpec.unfoldLoop g finish acc pos byte inside rfl
  cases digit : DecimalSpec.digit byte with
  | false =>
    have result : clLoop g finish 1024 acc pos=.bad 400 := by rw [spec];simp only [digit,Bool.false_eq_true,ite_false]
    have noGood : ¬HeadClNumberStep.good acc byte := by simp only [HeadClNumberStep.good,digit,Bool.false_eq_true,false_and,not_false_eq_true]
    rw [result]
    refine ⟨n,a,by omega,by omega,step,?_,fun r h1 h30 h12 h29 h14 h13 _ _ _ => frame r h1 h30 h12 h29 h14 h13,csr⟩
    constructor
    · simpa only [noGood,ite_false] using pc
    · simpa only [HeadClNumberStep.status,digit,Bool.false_eq_true,false_and,ite_false] using status
  | true =>
    by_cases large : 1024<HeadClNumberMath.next acc byte
    · have result : clLoop g finish 1024 acc pos=.bad 413 := by rw [spec];simp only [digit,large,ite_true]
      have noGood : ¬HeadClNumberStep.good acc byte := by unfold HeadClNumberStep.good;omega
      rw [result]
      refine ⟨n,a,by omega,by omega,step,?_,fun r h1 h30 h12 h29 h14 h13 _ _ _ => frame r h1 h30 h12 h29 h14 h13,csr⟩
      constructor
      · simpa only [noGood,ite_false] using pc
      · simpa only [HeadClNumberStep.status,digit,large,true_and,ite_true] using status
    · have newBound : HeadClNumberMath.next acc byte≤1024 := by omega
      have isGood : HeadClNumberStep.good acc byte := ⟨digit,newBound⟩
      have atAdvance : a.pc=0x80003256#32 := by simpa only [isGood,ite_true] using pc
      have nextSpec : clLoop g finish 1024 acc pos=clLoop g finish 1024 (HeadClNumberMath.next acc byte) (pos+1) := by
        rw [spec];simp only [digit,large,ite_true,ite_false]
      have a1 : a.get 1=400#32 := by simpa only [HeadClNumberStep.status,digit,large,and_false,ite_false] using status
      obtain ⟨a14,a13⟩ := values digit
      obtain ⟨d,advance,pc2,v11,v10,v31,frame2,csr2⟩ := HeadClNumberAdvance.contract B a ram buf pos finish length atAdvance
        ((frame 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h11)
        ((frame 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h10)
        ((frame 31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h31) inside upper bound
      have source (r : Reg) (h1 : r≠1) (h30 : r≠30) (h12 : r≠12) (h29 : r≠29) (h14 : r≠14) (h13 : r≠13) (h11 : r≠11) (h10 : r≠10) (h31 : r≠31) : d.get r=c.get r :=
        (frame2 r h11 h10 h31).trans (frame r h1 h30 h12 h29 h14 h13)
      have d1 : d.get 1=400#32 := (frame2 1 (by decide) (by decide) (by decide)).trans a1
      have d14 : d.get 14=BitVec.ofNat 32 (HeadClNumberMath.next acc byte) := (frame2 14 (by decide) (by decide) (by decide)).trans a14
      have d13 : d.get 13=0#32 := (frame2 13 (by decide) (by decide) (by decide)).trans a13
      by_cases more : pos+1<finish
      · have atLoop : d.pc=0x80003206#32 := by simpa only [more,ite_true] using pc2
        obtain ⟨rest,e,rlo,rhi,tail,result,frame3,csr3⟩ := contract B d ram sp buf (pos+1) finish length (HeadClNumberMath.next acc byte) atLoop d1
          ((source 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2)
          v10 v31 v11 d14 d13
          ((source 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h16)
          hlimit more upper bound newBound memory stack aligned
        rw [nextSpec]
        refine ⟨n+4+rest,e,by omega,by omega,(step.trans advance).trans tail,result,?_,csr3.trans (csr2.trans csr)⟩
        intro r h1 h30 h12 h29 h14 h13 h11 h10 h31
        exact (frame3 r h1 h30 h12 h29 h14 h13 h11 h10 h31).trans (source r h1 h30 h12 h29 h14 h13 h11 h10 h31)
      · have last : pos+1=finish := by omega
        rw [nextSpec,last,HeadClNumberSpec.finish]
        refine ⟨n+4,d,by omega,by omega,step.trans advance,?_,source,csr2.trans csr⟩
        exact ⟨by simpa only [more,ite_false] using pc2,d14,d13⟩
termination_by finish-pos
 decreasing_by omega
end E5R.Thermostat.HeadClNumberLoop
