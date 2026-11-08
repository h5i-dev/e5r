import Projects.thermostat.HeadCRGuard
import Projects.thermostat.HeadCRRead
import Projects.thermostat.HeadLineScanSpec
import Projects.thermostat.HeadScanMath
namespace E5R.Thermostat.HeadLineTerm
open E5R E5R.Thermostat HttpRequestSpec
open HeadLineScanSpec

def pc (term : Nat) : Word := if term=0 then 0x80002cba#32 else if term=1 then 0x80002ce6#32 else 0x80002d5a#32

/-- After the scanner found CR, the real guard reads a following byte only
    when it lies inside n. It distinguishes CRLF, bare CR and partial input. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (buf : Word) (j n : Nat)
    (hp : c.pc=0x80002ca8#32) (h5 : c.get 5=buf+BitVec.ofNat 32 j)
    (h9 : c.get 9=BitVec.ofNat 32 j) (h14 : c.get 14=BitVec.ofNat 32 n)
    (hm : Memory.Block B buf n) (hj : j<n) (hn : n≤1024) (cr : bytes ram buf j=13) :
    ∃ steps d, 2≤steps ∧ steps≤5 ∧ Quiet.Steps B img steps ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=pc (lineTerm (bytes ram buf) j n) ∧ d.get 9=BitVec.ofNat 32 j ∧
      (∀ r : Reg, r≠15 → r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  have test := HeadScanMath.next_full j n hj hn
  by_cases full : n≤j+1
  · obtain ⟨d,guard,endPC,next,frame,csr⟩ := HeadCRGuard.contract B c ram (BitVec.ofNat 32 j)
      (BitVec.ofNat 32 n) true hp h9 h14 (by simpa only [full,decide_true] using test)
    have term : lineTerm (bytes ram buf) j n=1 := by simp [lineTerm,show ¬n≤j by omega,cr,full]
    refine ⟨2,d,by decide,by decide,guard,?_,(frame 9 (by decide)).trans h9,?_,csr⟩
    · simpa only [term,pc,show ¬(1=0) by decide,ite_false,ite_true] using endPC
    · intro r hr h17;exact frame r hr
  · obtain ⟨a,guard,endPC,next,frame,csr⟩ := HeadCRGuard.contract B c ram (BitVec.ofNat 32 j)
      (BitVec.ofNat 32 n) false hp h9 h14 (by simpa only [full,decide_false] using test)
    have addr : (buf+BitVec.ofNat 32 j)+1#32=buf+BitVec.ofNat 32 (j+1) := by
      rw [BitVec.add_assoc,HeadScanMath.next_word]
    let b := ram (buf+BitVec.ofNat 32 (j+1))
    have readable : B.inRam ((buf+BitVec.ofNat 32 j)+1#32) 1=true := by
      rw [addr]
      exact Memory.block_access hm (off := j+1) (by decide) (by change j+1+1≤n;omega)
    obtain ⟨d,read,endPC2,value,ten,frame2,csr2⟩ := HeadCRRead.contract B a ram (buf+BitVec.ofNat 32 j) b
      endPC ((frame 5 (by decide)).trans h5) readable (by rw [addr])
    refine ⟨5,d,by decide,by decide,guard.trans read,?_,
      (frame2 9 (by decide) (by decide)).trans ((frame 9 (by decide)).trans h9),?_,csr2.trans csr⟩
    · by_cases lf : b.toNat=10
      · have term : lineTerm (bytes ram buf) j n=0 := by
          simp only [lineTerm,show ¬n≤j by omega,cr,show ¬(13=10) by decide,full,ite_false]
          change (if b.toNat≠10 then 2 else 0)=0
          simp only [lf,ne_eq,not_true_eq_false,ite_false]
        simpa only [lf,term,pc,ite_true] using endPC2
      · have term : lineTerm (bytes ram buf) j n=2 := by
          simp only [lineTerm,show ¬n≤j by omega,cr,show ¬(13=10) by decide,full,ite_false]
          change (if b.toNat≠10 then 2 else 0)=2
          simp only [ne_eq,lf,not_false_eq_true,ite_true]
        simpa only [lf,term,pc,show ¬(2=0) by decide,show ¬(2=1) by decide,ite_false] using endPC2
    · intro r hr h17
      exact (frame2 r hr h17).trans (frame r hr)
end E5R.Thermostat.HeadLineTerm
