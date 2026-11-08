import Projects.thermostat.HeadMethodInputSpec
import Projects.thermostat.HeadMethodRejectFinish
import Projects.thermostat.HeadEarlyInput
namespace E5R.Thermostat.HeadMethodBadInput
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

def memory (ram : Word → BitVec 8) (sp : Word) (values : Reg → Word) :=
  HeadEarlyFinish.memory (HeadStackSave.memory ram sp values) sp .bad

/-- Cold ELF parser entry through a byte-derived bad-method result and full return.
    The first line has complete CRLF; no header-fields or successful result is assumed. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (input : List (BitVec 8))
    (hp : c.pc=0x80002c46#32) (h2 : c.get 2=sp+384#32) (h10 : c.get 10=sp+4904#32)
    (h11 : c.get 11=sp+516#32) (h12 : c.get 12=BitVec.ofNat 32 input.length) (h13 : c.get 13=sp+3664#32)
    (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0) (hlen : input.length≤2048)
    (hmax : ramRead ram (sp+3664#32) .w=1024#32) (bytesAt : Bytes.At ram (sp+516#32) input)
    (complete : HeadByteInput.term input=0) (bad : HeadMethodInputSpec.Bad input) :
    ∃ steps d, 38≤steps ∧ steps≤68+25*min input.length 1024 ∧
      Quiet.Steps B img steps ⟨c,ram⟩ ⟨d,memory ram sp c.get⟩ ∧
      d.pc=c.get 1 &&& ~~~1 ∧ d.get 2=sp+384#32 ∧ HeadSaved.CoreAt d c.get ∧
      HeadResultView.At (memory ram sp c.get) (sp+4904#32) (HttpRequestBytes.parse input 1024 1024) ∧
      ViewFrame.Region ram (memory ram sp c.get) (sp+516#32) 2048 ∧
      (sp=0x80ffea10#32 → ∀ state, AppState.At ram state → AppState.At (memory ram sp c.get) state) ∧ d.sameCsr c := by
  let n := min input.length 1024
  let g := bytes ram (sp+516#32)
  let w := window (HttpRequestBytes.bytes input) n
  let j := lineEnd g 0 n
  let saved := HeadStackSave.memory ram sp c.get
  let gs := bytes saved (sp+516#32)
  have agree : ∀ k, k<n → g k=w k := HeadByteInput.agree bytesAt
  have lines : j=lineEnd w 0 n := HeadLineScanSpec.line_congr g w 0 n agree
  have term : lineTerm g j n=0 := by
    rw [HeadLineScanSpec.term_congr g w _ _ agree,lines]
    exact complete
  have inside : j+1<n := HeadMethodInputSpec.term_zero_bound g j n term
  have rawBound : j≤input.length := by have := Nat.min_le_left input.length 1024;omega
  have notEmpty : input.length≠0 := by have := Nat.min_le_left input.length 1024;omega
  have badOrig : ¬HeadMethodPrefix.Good g j := by
    intro good
    have mapped := (HeadMethodInputSpec.good_congr g w j (fun k hk => agree k (by omega))).mp good
    rw [lines] at mapped
    exact bad mapped
  obtain ⟨a,e,hlo,hi,first,pc,stack,cap,max,index,frame,rx,csr⟩ :=
    HeadFirstLine.contract B c ram sp input.length hp h2 h13 h12 h11 hlen hm ha hmax
  have pcMethod : e.pc=0x80002cba#32 := by
    change e.pc=HeadLineTerm.pc (lineTerm g j n) at pc
    simpa only [term,HeadLineTerm.pc,ite_true] using pc
  have savedAgree : ∀ k, k<j → gs k=g k := by
    intro k hk
    exact congrArg BitVec.toNat (rx ⟨k,by have := Nat.min_le_right input.length 1024;omega⟩)
  have badSaved : ¬HeadMethodPrefix.Good gs j := by
    intro good
    exact badOrig ((HeadMethodInputSpec.good_congr gs g j savedAgree).mp good)
  have buffer : Memory.Block B (sp+516#32) input.length :=
    Memory.sub_block hm (off := 516) (by omega) (by omega)
  obtain ⟨b,f,blo,bhi,method,pc2,status,cursor,cache,frame2,csr2⟩ :=
    HeadMethodPrefix.contract B e saved (sp+516#32) j input.length pcMethod (index notEmpty)
      ((frame 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h12) ((frame 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h11) rawBound hlen buffer
  have pcReject : f.pc=0x80002efc#32 := by
    change f.pc=(if HeadMethodPrefix.Good gs j then _ else _) at pc2
    simpa only [badSaved,ite_false] using pc2
  obtain ⟨d,finish,endPC,endSP,abi,csr3⟩ := HeadMethodRejectFinish.contract B f saved sp c.get pcReject
    (((frame2 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))).trans stack) (((frame2 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))).trans ((frame 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h10)) status hm ha (HeadSaved.stored ram sp c.get)
  refine ⟨a+b+20,d,by omega,by omega,(first.trans method).trans finish,endPC,endSP,abi,?_,?_,?_,csr3.trans (csr2.trans csr)⟩
  · rw [HeadMethodInputSpec.classification input complete bad]
    exact HeadEarlyFinish.result saved sp .bad
  · have rx2 := HeadEarlyFinish.region saved sp .bad 516 2048 (by decide) (by decide)
    exact fun i => (rx2 i).trans (rx i)
  · intro actual state hs
    change AppState.At (HeadEarlyFinish.memory (HeadStackSave.memory ram sp c.get) sp .bad) state
    rw [actual]
    exact HeadEarlyFinish.app _ _ state (HeadStackMemory.app ram c.get state hs)

theorem safe_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (input : List (BitVec 8))
    (hp : c.pc=0x80002c46#32) (h2 : c.get 2=sp+384#32) (h10 : c.get 10=sp+4904#32)
    (h11 : c.get 11=sp+516#32) (h12 : c.get 12=BitVec.ofNat 32 input.length) (h13 : c.get 13=sp+3664#32)
    (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0) (hlen : input.length≤2048)
    (hmax : ramRead ram (sp+3664#32) .w=1024#32) (bytesAt : Bytes.At ram (sp+516#32) input)
    (complete : HeadByteInput.term input=0) (bad : HeadMethodInputSpec.Bad input) (masked : c.mie_=false) :
    ∃ steps d, 38≤steps ∧ steps≤68+25*min input.length 1024 ∧
      Trace.Closed B img steps ⟨c,ram⟩ ⟨d,memory ram sp c.get⟩ ∧
      d.pc=c.get 1 &&& ~~~1 ∧ HeadResultView.At (memory ram sp c.get) (sp+4904#32) (HttpRequestBytes.parse input 1024 1024) ∧
      (∀ count e reads evs, count<steps → Observed.Steps B img count ⟨c,ram⟩ e reads evs →
        reads=[] ∧ evs=[] ∧ ¬Escapes B img e) := by
  obtain ⟨steps,d,hlo,hi,trace,pc,stack,abi,result,rx,app,csr⟩ :=
    contract B c ram sp input hp h2 h10 h11 h12 h13 hm ha hlen hmax bytesAt complete bad
  exact ⟨steps,d,hlo,hi,Interrupt.close trace.det masked,pc,result,
    fun _ _ _ _ hk actual => QuietPrefix.safe trace masked hk actual⟩
end E5R.Thermostat.HeadMethodBadInput
