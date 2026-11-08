import Projects.thermostat.HeadTargetStep
import Projects.thermostat.HeadTargetAdvance
import Projects.thermostat.HeadTargetSpec
namespace E5R.Thermostat.HeadTargetScan
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

/-- The complete bounded ELF target scan. The stopping position is derived
    from the original byte specification; exhaustion rejects without reading past j. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (buf : Word) (m i j length : Nat)
    (hp : c.pc=0x80002dd8#32) (h17 : c.get 17=BitVec.ofNat 32 m)
    (h30 : c.get 30=BitVec.ofNat 32 (i-m-1)) (h12 : c.get 12=BitVec.ofNat 32 length)
    (h28 : c.get 28=buf+BitVec.ofNat 32 m) (h19 : c.get 19=94#32)
    (h31 : c.get 31=BitVec.ofNat 32 (j-i))
    (hm : m<i) (hi : i<j) (hj : j≤length) (hlen : length≤2048) (mem : Memory.Block B buf length) :
    let g := bytes ram buf
    let te := scan isTargetByte g i j
    ∃ steps d, 0<steps ∧ steps≤11*(j-i) ∧ Quiet.Steps B img steps ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=HeadTargetSpec.pc te j ∧ d.get 30=BitVec.ofNat 32 (te-m-1) ∧ d.get 31=BitVec.ofNat 32 (j-te) ∧
      (te<j → d.get 18=BitVec.ofNat 32 te ∧ d.get 20=BitVec.ofNat 32 (g te) ∧ d.get 6=buf+BitVec.ofNat 32 (te-1) ∧ d.get 7=BitVec.ofNat 32 (te-1)) ∧
      (∀ r : Reg, r≠7 → r≠18 → r≠6 → r≠20 → r≠21 → r≠31 → r≠30 → d.get r=c.get r) ∧ d.sameCsr c := by
  let g := bytes ram buf
  let byte := ram (buf+BitVec.ofNat 32 i)
  obtain ⟨a,trace,pc,index,value,addr,sumIndex,frame,csr⟩ := HeadTargetStep.contract B c ram buf m i length hp h17 h30 h12 h28 h19 hm (by omega) hlen mem
  change a.pc=(if isTargetByte byte.toNat then 0x80002df4#32 else 0x80002dfe#32) at pc
  cases token : isTargetByte byte.toNat with
  | false =>
    have stop : scan isTargetByte g i j=i := HeadTargetSpec.stop g i j hi token
    change ∃ steps d, _
    rw [stop]
    refine ⟨7,a,by decide,by omega,trace,?_,(frame 30 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h30,(frame 31 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h31,
      fun _ => ⟨index,value,addr,sumIndex⟩,fun r h7 h18 h6 h20 h21 _ _ => frame r h7 h18 h6 h20 h21,csr⟩
    simpa only [token,ite_false,Bool.false_eq_true,HeadTargetSpec.pc,hi,ite_true] using pc
  | true =>
    have accepted : a.pc=0x80002df4#32 := by simpa only [token,ite_true] using pc
    obtain ⟨n,d,nlo,nhi,advance,pc2,rem,off,frame2,csr2⟩ := HeadTargetAdvance.contract B a ram m i j accepted
      ((frame 31 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h31) ((frame 30 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h30) hm hi (by omega)
    have source (r : Reg) (h7 : r≠7) (h18 : r≠18) (h6 : r≠6) (h20 : r≠20) (h21 : r≠21) (h31 : r≠31) (h30 : r≠30) : d.get r=c.get r :=
      (frame2 r h31 h30).trans (frame r h7 h18 h6 h20 h21)
    have specAdvance := HeadTargetSpec.advance g i j hi token
    by_cases more : i+1<j
    · have atLoop : d.pc=0x80002dd8#32 := by simpa only [more,ite_true] using pc2
      obtain ⟨rest,e,positive,bound,tail,pc3,off3,rem3,cache3,frame3,csr3⟩ := contract B d ram buf m (i+1) j length atLoop
        ((source 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h17) off ((source 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h12)
        ((source 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h28) ((source 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h19) rem (by omega) more hj hlen mem
      change ∃ steps d, _
      rw [specAdvance]
      refine ⟨7+n+rest,e,by omega,by omega,(trace.trans advance).trans tail,pc3,off3,rem3,cache3,?_,csr3.trans (csr2.trans csr)⟩
      intro r h7 h18 h6 h20 h21 h31 h30
      exact (frame3 r h7 h18 h6 h20 h21 h31 h30).trans (source r h7 h18 h6 h20 h21 h31 h30)
    · have last : i+1=j := by omega
      have result : scan isTargetByte g i j=j := by rw [specAdvance,last,HeadTargetSpec.end_at]
      change ∃ steps d, _
      rw [result]
      refine ⟨7+n,d,by omega,by omega,trace.trans advance,?_,?_,?_,by intro lt;omega,source,csr2.trans csr⟩
      · simpa only [more,ite_false,HeadTargetSpec.pc,Nat.lt_irrefl] using pc2
      · simpa only [last] using off
      · simpa only [last] using rem
termination_by j-i
 decreasing_by omega
end E5R.Thermostat.HeadTargetScan
