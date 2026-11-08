import Projects.thermostat.HeadTargetStart
import Projects.thermostat.HeadTargetScan
namespace E5R.Thermostat.HeadTargetPrefix
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

/-- Target setup and complete scan, including immediate refusal of an empty tail. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (buf : Word) (m j length : Nat)
    (hp : c.pc=0x80002dc0#32) (h17 : c.get 17=BitVec.ofNat 32 m) (h9 : c.get 9=BitVec.ofNat 32 j)
    (h12 : c.get 12=BitVec.ofNat 32 length) (h28 : c.get 28=buf+BitVec.ofNat 32 m)
    (hm : m<j) (hj : j≤length) (hlen : length≤2048) (mem : Memory.Block B buf length) :
    let g := bytes ram buf
    let te := scan isTargetByte g (m+1) j
    ∃ steps d, 0<steps ∧ steps≤7+11*(j-(m+1)) ∧ Quiet.Steps B img steps ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=HeadTargetSpec.pc te j ∧ d.get 29=BitVec.ofNat 32 (m+1) ∧
      (te<j → d.get 18=BitVec.ofNat 32 te ∧ d.get 20=BitVec.ofNat 32 (g te) ∧ d.get 6=buf+BitVec.ofNat 32 (te-1) ∧
        d.get 30=BitVec.ofNat 32 (te-m-1) ∧ d.get 31=BitVec.ofNat 32 (j-te) ∧ d.get 7=BitVec.ofNat 32 (te-1)) ∧
      (∀ r : Reg, r≠29 → r≠30 → r≠31 → r≠8 → r≠19 → r≠7 → r≠18 → r≠6 → r≠20 → r≠21 → d.get r=c.get r) ∧ d.sameCsr c := by
  let g := bytes ram buf
  by_cases more : m+1<j
  · obtain ⟨a,start,pc,first,off,rem,next,constant,frame,csr⟩ := HeadTargetStart.contract B c ram m j hp h17 h9 more (by omega)
    obtain ⟨n,d,positive,bound,scan,endPC,off2,rem2,cache,frame2,csr2⟩ := HeadTargetScan.contract B a ram buf m (m+1) j length pc
      ((frame 17 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h17) (by simpa only [show m+1-m-1=0 by omega] using off)
      ((frame 12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h12) ((frame 28 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h28) constant rem (by omega) more hj hlen mem
    refine ⟨7+n,d,by omega,by omega,start.trans scan,endPC,(frame2 29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans first,?_,?_,csr2.trans csr⟩
    · intro inside
      exact ⟨(cache inside).1,(cache inside).2.1,(cache inside).2.2.1,off2,rem2,(cache inside).2.2.2⟩
    · intro r h29 h30 h31 h8 h19 h7 h18 h6 h20 h21
      exact (frame2 r h7 h18 h6 h20 h21 h31 h30).trans (frame r h29 h30 h31 h8 h19)
  · have last : m+1=j := by omega
    have test : taken .geu (BitVec.ofNat 32 m+1#32) (BitVec.ofNat 32 j)=true := by
      rw [HeadScanMath.next_word,last,HeadTargetMath.geu j j (by omega) (by omega)]
      simp
    obtain ⟨d,guard,pc,index,frame,csr⟩ := HeadTargetGuard.contract B c ram (BitVec.ofNat 32 m) (BitVec.ofNat 32 j) true hp h17 h9 test
    have result : scan isTargetByte g (m+1) j=j := by rw [last,HeadTargetSpec.end_at]
    change ∃ steps d, _
    rw [result]
    refine ⟨2,d,by decide,by omega,guard,?_,index.trans (HeadScanMath.next_word m),by intro lt;omega,?_,csr⟩
    · simpa only [ite_true,HeadTargetSpec.pc,Nat.lt_irrefl,ite_false] using pc
    · intro r h29 h30 h31 h8 h19 h7 h18 h6 h20 h21
      exact frame r h29
end E5R.Thermostat.HeadTargetPrefix
