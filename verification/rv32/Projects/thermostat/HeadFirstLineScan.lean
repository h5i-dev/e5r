import Projects.thermostat.HeadLineScan
import Projects.thermostat.HeadLineTerm
namespace E5R.Thermostat.HeadFirstLineScan
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

/-- The complete first-line scan and terminator check, still before method
    and field validation. All actual byte loads are bounded by the slice. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (buf : Word) (n : Nat)
    (hp : c.pc=0x80002c90#32) (h11 : c.get 11=buf) (h9 : c.get 9=0#32)
    (h14 : c.get 14=BitVec.ofNat 32 n) (h15 : c.get 15=10#32) (h17 : c.get 17=13#32)
    (hm : Memory.Block B buf n) (positive : 0<n) (hn : n≤1024) :
    let k := lineEnd (bytes ram buf) 0 n
    ∃ steps d, 0<steps ∧ steps≤7*n+5 ∧ Quiet.Steps B img steps ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=HeadLineTerm.pc (lineTerm (bytes ram buf) k n) ∧ d.get 9=BitVec.ofNat 32 k ∧
      (∀ r : Reg, r≠5 → r≠6 → r≠9 → r≠15 → r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  let g := bytes ram buf
  let k := lineEnd g 0 n
  obtain ⟨a,e,hlo,ha,scan,endPC,index,cache,frame,csr⟩ :=
    HeadLineScan.contract B c ram buf 0 n hp h11 h9 h14 h15 h17 hm positive hn
  have bound : k≤n := scan_le notEol g 0 n (by omega)
  by_cases atEnd : n≤k
  · have eq : k=n := by omega
    have term : lineTerm g k n=1 := by simp only [lineTerm,atEnd,ite_true]
    refine ⟨a,e,hlo,by omega,scan,?_,index,fun r h5 h6 h9 _ _ => frame r h5 h6 h9,csr⟩
    change e.pc=HeadLineTerm.pc (lineTerm g k n)
    change e.pc=pc g k n at endPC
    simpa only [term,HeadLineTerm.pc,pc,show ¬k<n by omega,show ¬(1=0) by decide,ite_false,ite_true] using endPC
  · have inside : k<n := by omega
    have found := HeadLineScanSpec.eol g 0 n inside
    rcases found with lf|cr
    · change g k=10 at lf
      have term : lineTerm g k n=2 := by simp only [lineTerm,show ¬n≤k by omega,lf,ite_false,ite_true]
      refine ⟨a,e,hlo,by omega,scan,?_,index,fun r h5 h6 h9 _ _ => frame r h5 h6 h9,csr⟩
      change e.pc=HeadLineTerm.pc (lineTerm g k n)
      change e.pc=pc g k n at endPC
      simpa only [term,HeadLineTerm.pc,pc,inside,lf,show ¬(2=0) by decide,show ¬(2=1) by decide,ite_false,ite_true] using endPC
    · change g k=13 at cr
      have notLF : g k≠10 := by rw [cr];decide
      have atCR : e.pc=0x80002ca8#32 := by
        change e.pc=pc g k n at endPC
        simpa only [pc,inside,notLF,ite_true,ite_false] using endPC
      obtain ⟨b,d,hblo,hb,check,endPC2,index2,frame2,csr2⟩ := HeadLineTerm.contract B e ram buf k n
        atCR (cache inside).1 index ((frame 14 (by decide) (by decide) (by decide)).trans h14) hm inside hn cr
      refine ⟨a+b,d,by omega,by omega,scan.trans check,endPC2,index2,?_,csr2.trans csr⟩
      intro r h5 h6 h9 h15 h17
      exact (frame2 r h15 h17).trans (frame r h5 h6 h9)
end E5R.Thermostat.HeadFirstLineScan
