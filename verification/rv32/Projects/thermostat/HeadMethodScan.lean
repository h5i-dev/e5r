import Projects.thermostat.HeadMethodStep
import Projects.thermostat.HeadMethodAdvance
import Projects.thermostat.HeadMethodSpec
namespace E5R.Thermostat.HeadMethodScan
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

/-- The actual bounded method-token scan, including its real EOF and slice
    guards. Its stop index is the independent `scan isTchar` specification. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (buf : Word) (i j length : Nat)
    (hp : c.pc=0x80002cfa#32) (h12 : c.get 12=BitVec.ofNat 32 length) (h17 : c.get 17=BitVec.ofNat 32 i)
    (h11 : c.get 11=buf) (h9 : c.get 9=BitVec.ofNat 32 j) (hc : HeadMethodClass.Constants c)
    (hi : i<j) (hj : j≤length) (hlen : length≤2048) (hm : Memory.Block B buf length) :
    let g := bytes ram buf
    let m := scan isTchar g i j
    ∃ steps d, 0<steps ∧ steps≤18*(j-i) ∧ Quiet.Steps B img steps ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=HeadMethodSpec.pc g m j ∧ d.get 17=BitVec.ofNat 32 m ∧ HeadMethodClass.Constants d ∧
      (m<j → g m<33 → d.get 19=BitVec.ofNat 32 (g m) ∧ d.get 28=buf+BitVec.ofNat 32 m) ∧
      (∀ r : Reg, r≠17 → r≠19 → r≠28 → d.get r=c.get r) ∧ d.sameCsr c := by
  let g := bytes ram buf
  let b := ram (buf+BitVec.ofNat 32 i)
  obtain ⟨n,d,hlo,hn,trace,endPC,cache,constants,frame,csr⟩ :=
    HeadMethodStep.contract B c ram buf i length hp h12 h17 h11 hc (by omega) hlen hm
  change d.pc=(if b.toNat<33 then 0x80002da2#32 else if isTchar b.toNat then 0x80002cf4#32 else 0x80002efc#32) at endPC
  cases token : isTchar b.toNat with
  | false =>
    have stop : scan isTchar g i j=i := HeadMethodSpec.stop g i j hi token
    change ∃ steps d, _
    rw [stop]
    refine ⟨n,d,by omega,by omega,trace,?_,(frame 17 (by decide) (by decide)).trans h17,constants,
      fun _ small => cache small,fun r _ h19 h28 => frame r h19 h28,csr⟩
    change d.pc=HeadMethodSpec.pc g i j
    simpa only [HeadMethodSpec.pc,show ¬j≤i by omega,g,bytes,
      ←show b=ram (buf+BitVec.ofNat 32 i) from rfl,token,Bool.false_eq_true,ite_false] using endPC
  | true =>
    have nonsmall : ¬b.toNat<33 := HeadMethodSpec.token_not_small b.toNat token
    have accepted : d.pc=0x80002cf4#32 := by simpa only [nonsmall,token,ite_false,ite_true] using endPC
    obtain ⟨e,advance,pc2,index2,frame2,csr2⟩ := HeadMethodAdvance.contract B d ram (BitVec.ofNat 32 i) (BitVec.ofNat 32 j)
      (decide (i+1=j)) accepted ((frame 17 (by decide) (by decide)).trans h17)
      ((frame 9 (by decide) (by decide)).trans h9) (HeadMethodMath.next_test i j hi (by omega))
    have nextIndex : e.get 17=BitVec.ofNat 32 (i+1) := by simpa only [HeadScanMath.next_word] using index2
    have constants2 := HeadMethodClass.preserve_constants_except17 constants frame2
    have specAdvance := HeadMethodSpec.advance g i j hi token
    by_cases atEnd : i+1=j
    · have result : scan isTchar g i j=j := by rw [specAdvance,atEnd,HeadMethodSpec.end_at]
      change ∃ steps d, _
      rw [result]
      refine ⟨n+2,e,by omega,by omega,trace.trans advance,?_,?_,constants2,by intro lt;omega,?_,csr2.trans csr⟩
      · simpa only [atEnd,decide_true,ite_true,HeadMethodSpec.pc,Nat.le_refl] using pc2
      · simpa only [atEnd] using nextIndex
      · intro r h17 h19 h28
        exact (frame2 r h17).trans (frame r h19 h28)
    · have inside : i+1<j := by omega
      have atLoop : e.pc=0x80002cfa#32 := by
        simpa only [atEnd,decide_false,Bool.false_eq_true,ite_false] using pc2
      have source (r : Reg) (h17 : r≠17) (h19 : r≠19) (h28 : r≠28) : e.get r=c.get r :=
        (frame2 r h17).trans (frame r h19 h28)
      obtain ⟨more,f,positive,bound,rest,pc3,index3,constants3,cache3,frame3,csr3⟩ := contract B e ram buf (i+1) j length
        atLoop ((source 12 (by decide) (by decide) (by decide)).trans h12) nextIndex
        ((source 11 (by decide) (by decide) (by decide)).trans h11)
        ((source 9 (by decide) (by decide) (by decide)).trans h9) constants2 inside hj hlen hm
      change ∃ steps d, _
      rw [specAdvance]
      refine ⟨n+2+more,f,by omega,by omega,(trace.trans advance).trans rest,pc3,index3,constants3,cache3,?_,csr3.trans (csr2.trans csr)⟩
      intro r h17 h19 h28
      exact (frame3 r h17 h19 h28).trans (source r h17 h19 h28)
termination_by j-i
 decreasing_by omega
end E5R.Thermostat.HeadMethodScan
