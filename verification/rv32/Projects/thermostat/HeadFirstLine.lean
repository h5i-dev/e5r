import Projects.thermostat.HeadReady
import Projects.thermostat.QuietPrefix
import Projects.thermostat.HeadFirstLineScan
namespace E5R.Thermostat.HeadFirstLine
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

/-- Actual parser entry through first-line termination, specified against
    the original RX bytes. Successful CRLF stops before method/header checks. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (length : Nat)
    (hp : c.pc=0x80002c46#32) (h2 : c.get 2=sp+384#32) (h13 : c.get 13=sp+3664#32)
    (h12 : c.get 12=BitVec.ofNat 32 length) (h11 : c.get 11=sp+516#32) (hlen : length≤2048)
    (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0)
    (hmax : ramRead ram (sp+3664#32) .w=1024#32) :
    let n := min length 1024
    let g := bytes ram (sp+516#32)
    let k := lineEnd g 0 n
    ∃ steps d, 18≤steps ∧ steps≤27+7*n ∧
      Quiet.Steps B img steps ⟨c,ram⟩ ⟨d,HeadStackSave.memory ram sp c.get⟩ ∧
      d.pc=HeadLineTerm.pc (lineTerm g k n) ∧ d.get 2=sp ∧ d.get 14=BitVec.ofNat 32 n ∧ d.get 16=1024#32 ∧
      (length≠0 → d.get 9=BitVec.ofNat 32 k) ∧
      (∀ r : Reg, r≠2 → r≠5 → r≠6 → r≠9 → r≠14 → r≠15 → r≠16 → r≠17 → d.get r=c.get r) ∧
      ViewFrame.Region ram (HeadStackSave.memory ram sp c.get) (sp+516#32) 2048 ∧ d.sameCsr c := by
  let n := min length 1024
  let saved := HeadStackSave.memory ram sp c.get
  let g := bytes ram (sp+516#32)
  let gs := bytes saved (sp+516#32)
  obtain ⟨a,e,hlo,hi,ready,pc1,stack,limit,max,initial,frame,rx,csr⟩ :=
    HeadReady.contract B c ram sp length hp h2 h13 h12 hlen hm ha hmax
  have agree : ∀ i, i<n → gs i=g i := by
    intro i hi
    have bound : n≤1024 := Nat.min_le_right _ _
    exact congrArg BitVec.toNat (rx ⟨i,by omega⟩)
  have lineEq : lineEnd gs 0 n=lineEnd g 0 n := HeadLineScanSpec.line_congr gs g 0 n agree
  by_cases empty : length=0
  · have nz : n=0 := by simp only [n,empty,Nat.zero_min]
    have line : lineEnd g 0 n=0 := by rw [nz];exact HeadLineScanSpec.end_at g 0
    have term : lineTerm g (lineEnd g 0 n) n=1 := by rw [line,nz];simp only [lineTerm,Nat.le_refl,ite_true]
    refine ⟨a,e,hlo,by omega,ready,?_,stack,limit,max,?_,?_,rx,csr⟩
    · change e.pc=HeadLineTerm.pc (lineTerm g (lineEnd g 0 n) n)
      simpa [term,HeadLineTerm.pc,empty] using pc1
    · intro hne;exact False.elim (hne empty)
    · intro r h2 h5 h6 h9 h14 h15 h16 h17
      exact frame r h2 h9 h14 h15 h16 h17
  · have npos : 0<n := by dsimp only [n];omega
    obtain ⟨zero,ten,thirteen⟩ := initial empty
    have atLoop : e.pc=0x80002c90#32 := by simpa only [empty,ite_false] using pc1
    have buffer : Memory.Block B (sp+516#32) n :=
      Memory.sub_block hm (off := 516) npos (by have : n≤1024 := Nat.min_le_right _ _;omega)
    obtain ⟨b,d,positive,bound,scan,endPC,index,frame2,csr2⟩ := HeadFirstLineScan.contract B e saved (sp+516#32) n
      atLoop ((frame 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h11)
      zero limit ten thirteen buffer npos (Nat.min_le_right _ _)
    have termEq : lineTerm gs (lineEnd gs 0 n) n=lineTerm g (lineEnd g 0 n) n := by
      rw [HeadLineScanSpec.term_congr gs g _ _ agree,lineEq]
    change d.pc=HeadLineTerm.pc (lineTerm gs (lineEnd gs 0 n) n) at endPC
    rw [termEq] at endPC
    change d.get 9=BitVec.ofNat 32 (lineEnd gs 0 n) at index
    rw [lineEq] at index
    refine ⟨a+b,d,by omega,by omega,ready.trans scan,endPC,?_,?_,?_,fun _ => index,?_,rx,csr2.trans csr⟩
    · exact (frame2 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans stack
    · exact (frame2 14 (by decide) (by decide) (by decide) (by decide) (by decide)).trans limit
    · exact (frame2 16 (by decide) (by decide) (by decide) (by decide) (by decide)).trans max
    · intro r h2 h5 h6 h9 h14 h15 h16 h17
      exact (frame2 r h5 h6 h9 h15 h17).trans (frame r h2 h9 h14 h15 h16 h17)
/-- IRQ-aware safety for every actual strict prefix of the entry/first-line
    certificate. The endpoint still belongs to the remaining parser proof. -/
theorem safe_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (length : Nat)
    (hp : c.pc=0x80002c46#32) (h2 : c.get 2=sp+384#32) (h13 : c.get 13=sp+3664#32)
    (h12 : c.get 12=BitVec.ofNat 32 length) (h11 : c.get 11=sp+516#32) (hlen : length≤2048)
    (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0)
    (hmax : ramRead ram (sp+3664#32) .w=1024#32) (masked : c.mie_=false) :
    let n := min length 1024
    let g := bytes ram (sp+516#32)
    ∃ steps d, 18≤steps ∧ steps≤27+7*n ∧
      Trace.Closed B img steps ⟨c,ram⟩ ⟨d,HeadStackSave.memory ram sp c.get⟩ ∧
      d.pc=HeadLineTerm.pc (lineTerm g (lineEnd g 0 n) n) ∧
      (sp=0x80ffea10#32 → ∀ state, AppState.At ram state → AppState.At (HeadStackSave.memory ram sp c.get) state) ∧
      (∀ count e reads evs, count<steps → Observed.Steps B img count ⟨c,ram⟩ e reads evs →
        reads=[] ∧ evs=[] ∧ ¬Escapes B img e) := by
  obtain ⟨steps,d,positive,bound,trace,pc,stack,limit,max,index,frame,rx,csr⟩ :=
    contract B c ram sp length hp h2 h13 h12 h11 hlen hm ha hmax
  refine ⟨steps,d,positive,bound,Interrupt.close trace.det masked,pc,?_,
    fun _ _ _ _ hk actual => QuietPrefix.safe trace masked hk actual⟩
  intro actual state hs
  rw [actual]
  exact HeadStackMemory.app ram c.get state hs
end E5R.Thermostat.HeadFirstLine
