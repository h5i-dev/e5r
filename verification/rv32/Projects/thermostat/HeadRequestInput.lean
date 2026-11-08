import Projects.thermostat.HeadRequestLine
import Projects.thermostat.HeadRequestCongr
import Projects.thermostat.HeadFirstLine
import Projects.thermostat.HeadByteInput
namespace E5R.Thermostat.HeadRequestInput
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

def line (input : List (BitVec 8)) : Nat :=
  let n := min input.length 1024
  lineEnd (window (HttpRequestBytes.bytes input) n) 0 n

def request (input : List (BitVec 8)) : ReqLine :=
  let n := min input.length 1024
  requestLine (window (HttpRequestBytes.bytes input) n) 0 (line input)

/-- Cold ELF parser entry through all request-line decoding, derived from
    actual input bytes. Bad lines fully return an encoded rejection; valid
    lines establish the real header entry with every metadata word in RAM. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (input : List (BitVec 8))
    (hp : c.pc=0x80002c46#32) (h2 : c.get 2=sp+384#32) (h10 : c.get 10=sp+4904#32)
    (h11 : c.get 11=sp+516#32) (h12 : c.get 12=BitVec.ofNat 32 input.length) (h13 : c.get 13=sp+3664#32)
    (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0) (hlen : input.length≤2048)
    (hmax : ramRead ram (sp+3664#32) .w=1024#32) (bytesAt : Bytes.At ram (sp+516#32) input)
    (complete : HeadByteInput.term input=0) :
    ∃ steps d after, 19≤steps ∧ steps≤153+36*min input.length 1024 ∧ Quiet.Steps B img steps ⟨c,ram⟩ ⟨d,after⟩ ∧
      HeadRequestOutcome.At d after sp c.get (line input) input.length (min input.length 1024) (request input) ∧
      ViewFrame.Region ram after (sp+516#32) 2048 ∧
      (sp=0x80ffea10#32 → ∀ state, AppState.At ram state → AppState.At after state) ∧ HeadSaved.At after sp c.get ∧ d.sameCsr c := by
  let n := min input.length 1024
  let g := bytes ram (sp+516#32)
  let w := window (HttpRequestBytes.bytes input) n
  let j := line input
  let saved := HeadStackSave.memory ram sp c.get
  let gs := bytes saved (sp+516#32)
  have agree : ∀ k, k<n → g k=w k := HeadByteInput.agree bytesAt
  have lines : lineEnd g 0 n=j := HeadLineScanSpec.line_congr g w 0 n agree
  have term : lineTerm g (lineEnd g 0 n) n=0 := by
    rw [HeadLineScanSpec.term_congr g w _ _ agree,lines]
    exact complete
  have inside : j+1<n := by
    rw [lines] at term
    exact HeadMethodInputSpec.term_zero_bound g j n term
  have rawBound : j≤input.length := by have := Nat.min_le_left input.length 1024;omega
  have positive : 0<input.length := by have := Nat.min_le_left input.length 1024;omega
  obtain ⟨a,e,alo,ahi,first,pc,stack,cap,max,index,frame,rx,csr⟩ := HeadFirstLine.contract B c ram sp input.length hp h2 h13 h12 h11 hlen hm ha hmax
  have atLine : e.pc=0x80002cba#32 := by
    change e.pc=HeadLineTerm.pc (lineTerm g (lineEnd g 0 n) n) at pc
    simpa only [term,HeadLineTerm.pc,ite_true] using pc
  have indexJ : e.get 9=BitVec.ofNat 32 j := by
    have idx := index (by omega)
    change e.get 9=BitVec.ofNat 32 (lineEnd g 0 n) at idx
    exact idx.trans (congrArg (BitVec.ofNat 32) lines)
  obtain ⟨b,d,after,blo,bhi,body,result,rx2,appFrame,savedAfter,csr2⟩ := HeadRequestLine.contract B e saved sp j input.length n c.get atLine stack indexJ
    ((frame 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h10) ((frame 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h11) ((frame 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h12) ((frame 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h13) cap max
    rawBound hlen hm ha (HeadSaved.stored ram sp c.get) positive
  have savedAgree : ∀ k, k<j → gs k=w k := by
    intro k hk
    have raw : gs k=g k := congrArg BitVec.toNat (rx ⟨k,by have := Nat.min_le_right input.length 1024;omega⟩)
    exact raw.trans (agree k (by omega))
  have reqEq : requestLine gs 0 j=request input := HeadRequestCongr.requestLine gs w j savedAgree
  refine ⟨a+b,d,after,by omega,by omega,first.trans body,?_,?_,?_,savedAfter,csr2.trans csr⟩
  · change HeadRequestOutcome.At d after sp c.get j input.length n (requestLine gs 0 j) at result
    rw [reqEq] at result
    exact result
  · exact fun i => (rx2 i).trans (rx i)
  · intro actual state app
    have appSaved : AppState.At saved state := by
      change AppState.At (HeadStackSave.memory ram sp c.get) state
      rw [actual]
      exact HeadStackMemory.app ram c.get state app
    exact appFrame actual state appSaved
theorem safe_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (input : List (BitVec 8))
    (hp : c.pc=0x80002c46#32) (h2 : c.get 2=sp+384#32) (h10 : c.get 10=sp+4904#32)
    (h11 : c.get 11=sp+516#32) (h12 : c.get 12=BitVec.ofNat 32 input.length) (h13 : c.get 13=sp+3664#32)
    (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0) (hlen : input.length≤2048)
    (hmax : ramRead ram (sp+3664#32) .w=1024#32) (bytesAt : Bytes.At ram (sp+516#32) input)
    (complete : HeadByteInput.term input=0) (masked : c.mie_=false) :
    ∃ steps d after, 19≤steps ∧ steps≤153+36*min input.length 1024 ∧ Trace.Closed B img steps ⟨c,ram⟩ ⟨d,after⟩ ∧
      HeadRequestOutcome.At d after sp c.get (line input) input.length (min input.length 1024) (request input) ∧
      ViewFrame.Region ram after (sp+516#32) 2048 ∧
      (sp=0x80ffea10#32 → ∀ state, AppState.At ram state → AppState.At after state) ∧ HeadSaved.At after sp c.get ∧ d.sameCsr c ∧
      (∀ count e reads evs, count<steps → Observed.Steps B img count ⟨c,ram⟩ e reads evs →
        reads=[] ∧ evs=[] ∧ ¬Escapes B img e) := by
  obtain ⟨steps,d,after,hlo,hi,trace,result,rx,app,savedOut,csr⟩ := contract B c ram sp input
    hp h2 h10 h11 h12 h13 hm ha hlen hmax bytesAt complete
  exact ⟨steps,d,after,hlo,hi,Interrupt.close trace.det masked,result,rx,app,savedOut,csr,
    fun _ _ _ _ hk actual => QuietPrefix.safe trace masked hk actual⟩
end E5R.Thermostat.HeadRequestInput
