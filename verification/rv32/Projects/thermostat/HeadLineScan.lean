import Projects.thermostat.HeadScanIteration
import Projects.thermostat.HeadLineScanSpec
import Projects.thermostat.QuietPrefix
namespace E5R.Thermostat.HeadLineScan
open E5R E5R.Thermostat HttpRequestSpec
open HeadLineScanSpec

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (buf : Word) (j n : Nat)
    (hp : c.pc=0x80002c90#32) (h11 : c.get 11=buf) (h9 : c.get 9=BitVec.ofNat 32 j)
    (h14 : c.get 14=BitVec.ofNat 32 n) (h15 : c.get 15=10#32) (h17 : c.get 17=13#32)
    (hm : Memory.Block B buf n) (hj : j<n) (hn : n≤1024) :
    let k := lineEnd (bytes ram buf) j n
    ∃ steps d, 0<steps ∧ steps≤7*(n-j) ∧ Quiet.Steps B img steps ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=pc (bytes ram buf) k n ∧ d.get 9=BitVec.ofNat 32 k ∧
      (k<n → d.get 5=buf+BitVec.ofNat 32 k ∧ d.get 6=BitVec.ofNat 32 (bytes ram buf k)) ∧
      (∀ r : Reg, r≠5 → r≠6 → r≠9 → d.get r=c.get r) ∧ d.sameCsr c := by
  let g := bytes ram buf
  let b := ram (buf+BitVec.ofNat 32 j)
  obtain ⟨a,d,hlo,ha,trace,endpoint,index,cache5,cache6,frame,csr⟩ :=
    HeadScanIteration.contract B c ram buf j n hp h11 h9 h14 h15 h17 hm hj hn
  by_cases eol : b.toNat=10 ∨ b.toNat=13
  · have scanStop : lineEnd g j n=j := HeadLineScanSpec.stop g j n hj eol
    change ∃ steps d, _
    rw [scanStop]
    refine ⟨a,d,by omega,by omega,trace,?_,?_,fun _ => ⟨cache5,cache6⟩,frame,csr⟩
    · change d.pc=pc g j n
      rcases eol with lf|cr
      · simpa only [HeadScanIteration.endpoint,pc,g,bytes,←show b=ram (buf+BitVec.ofNat 32 j) from rfl,lf,hj,ite_true] using endpoint
      · by_cases lf : b.toNat=10
        · simpa only [HeadScanIteration.endpoint,pc,g,bytes,←show b=ram (buf+BitVec.ofNat 32 j) from rfl,lf,hj,ite_true] using endpoint
        · simpa only [HeadScanIteration.endpoint,pc,g,bytes,←show b=ram (buf+BitVec.ofNat 32 j) from rfl,lf,cr,hj,ite_false,ite_true] using endpoint
    · simpa only [HeadScanIteration.cursor,←show b=ram (buf+BitVec.ofNat 32 j) from rfl,eol,ite_true] using index
  · have noLF : b.toNat≠10 := fun h => eol (Or.inl h)
    have noCR : b.toNat≠13 := fun h => eol (Or.inr h)
    have advance := HeadLineScanSpec.advance g j n hj noLF noCR
    have index' : d.get 9=BitVec.ofNat 32 (j+1) := by
      simpa only [HeadScanIteration.cursor,←show b=ram (buf+BitVec.ofNat 32 j) from rfl,eol,ite_false] using index
    by_cases again : j+1<n
    · have atLoop : d.pc=0x80002c90#32 := by
        simpa only [HeadScanIteration.endpoint,←show b=ram (buf+BitVec.ofNat 32 j) from rfl,noLF,noCR,again,ite_false,ite_true] using endpoint
      obtain ⟨more,e,positive,bound,rest,finalPC,finalIndex,cached,frame2,csr2⟩ := contract B d ram buf (j+1) n
        atLoop ((frame 11 (by decide) (by decide) (by decide)).trans h11) index'
        ((frame 14 (by decide) (by decide) (by decide)).trans h14)
        ((frame 15 (by decide) (by decide) (by decide)).trans h15)
        ((frame 17 (by decide) (by decide) (by decide)).trans h17) hm again hn
      change ∃ steps d, _
      rw [advance]
      refine ⟨a+more,e,by omega,by omega,trace.trans rest,finalPC,finalIndex,cached,?_,csr2.trans csr⟩
      intro r h5 h6 h9
      exact (frame2 r h5 h6 h9).trans (frame r h5 h6 h9)
    · have eq : j+1=n := by omega
      have result : lineEnd g j n=n := by rw [advance,eq,HeadLineScanSpec.end_at]
      change ∃ steps d, _
      rw [result]
      refine ⟨a,d,by omega,by omega,trace,?_,?_,by intro h;omega,frame,csr⟩
      · simpa only [HeadScanIteration.endpoint,pc,←show b=ram (buf+BitVec.ofNat 32 j) from rfl,
          noLF,noCR,again,Nat.lt_irrefl,ite_false] using endpoint
      · simpa only [eq] using index'
termination_by n-j
 decreasing_by omega
/-- Every actual strict prefix of the complete bounded first-line scan is
    fault/unsupported-free under the already established IRQ mask. -/
theorem safe_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (buf : Word) (j n : Nat)
    (hp : c.pc=0x80002c90#32) (h11 : c.get 11=buf) (h9 : c.get 9=BitVec.ofNat 32 j)
    (h14 : c.get 14=BitVec.ofNat 32 n) (h15 : c.get 15=10#32) (h17 : c.get 17=13#32)
    (hm : Memory.Block B buf n) (hj : j<n) (hn : n≤1024) (masked : c.mie_=false) :
    let k := lineEnd (bytes ram buf) j n
    ∃ steps d, 0<steps ∧ steps≤7*(n-j) ∧ Trace.Closed B img steps ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=pc (bytes ram buf) k n ∧ d.get 9=BitVec.ofNat 32 k ∧
      (∀ count e reads evs, count<steps → Observed.Steps B img count ⟨c,ram⟩ e reads evs →
        reads=[] ∧ evs=[] ∧ ¬Escapes B img e) := by
  obtain ⟨steps,d,positive,bound,trace,pc,index,cache,frame,csr⟩ :=
    contract B c ram buf j n hp h11 h9 h14 h15 h17 hm hj hn
  exact ⟨steps,d,positive,bound,Interrupt.close trace.det masked,pc,index,
    fun _ _ _ _ hk actual => QuietPrefix.safe trace masked hk actual⟩
end E5R.Thermostat.HeadLineScan
