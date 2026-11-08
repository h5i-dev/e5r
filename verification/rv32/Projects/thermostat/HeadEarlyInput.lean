import Projects.thermostat.HeadFirstLine
import Projects.thermostat.HeadByteInput
namespace E5R.Thermostat.HeadEarlyInput
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

def memory (ram : Word → BitVec 8) (sp : Word) (values : Reg → Word) (input : List (BitVec 8)) :=
  HeadEarlyFinish.memory (HeadStackSave.memory ram sp values) sp (HeadEarlyPath.kind input.length (HeadByteInput.term input))

/-- A byte-slice-to-ELF parser theorem for incomplete first lines and malformed
    terminators, including the full ABI return and actual result representation.
    Complete valid first lines remain the next parser-proof obligation. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (input : List (BitVec 8))
    (hp : c.pc=0x80002c46#32) (h2 : c.get 2=sp+384#32) (h10 : c.get 10=sp+4904#32)
    (h11 : c.get 11=sp+516#32) (h12 : c.get 12=BitVec.ofNat 32 input.length) (h13 : c.get 13=sp+3664#32)
    (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0) (hlen : input.length≤2048)
    (hmax : ramRead ram (sp+3664#32) .w=1024#32) (bytesAt : Bytes.At ram (sp+516#32) input)
    (early : HeadByteInput.term input=1 ∨ HeadByteInput.term input=2) :
    ∃ n d, 38≤n ∧ n≤49+7*min input.length 1024 ∧
      Quiet.Steps B img n ⟨c,ram⟩ ⟨d,memory ram sp c.get input⟩ ∧
      d.pc=c.get 1 &&& ~~~1 ∧ d.get 2=sp+384#32 ∧ HeadSaved.CoreAt d c.get ∧
      HeadResultView.At (memory ram sp c.get input) (sp+4904#32) (HttpRequestBytes.parse input 1024 1024) ∧
      ViewFrame.Region ram (memory ram sp c.get input) (sp+516#32) 2048 ∧
      (sp=0x80ffea10#32 → ∀ state, AppState.At ram state → AppState.At (memory ram sp c.get input) state) ∧ d.sameCsr c := by
  let limit := min input.length 1024
  let g := HeadLineScanSpec.bytes ram (sp+516#32)
  let w := window (HttpRequestBytes.bytes input) limit
  have agree : ∀ k, k<limit → g k=w k := HeadByteInput.agree bytesAt
  have lines : lineEnd g 0 limit=lineEnd w 0 limit := HeadLineScanSpec.line_congr g w 0 limit agree
  have terms : lineTerm g (lineEnd g 0 limit) limit=HeadByteInput.term input := by
    rw [HeadLineScanSpec.term_congr g w _ _ agree,lines]
    rfl
  obtain ⟨a,e,hlo,hi,first,pc,stack,cap,max,index,frame,rx,csr⟩ :=
    HeadFirstLine.contract B c ram sp input.length hp h2 h13 h12 h11 hlen hm ha hmax
  change e.pc=HeadLineTerm.pc (lineTerm g (lineEnd g 0 limit) limit) at pc
  rw [terms] at pc
  let saved := HeadStackSave.memory ram sp c.get
  obtain ⟨b,d,blo,bhi,finish,endPC,endSP,abi,result,csr2⟩ := HeadEarlyPath.contract B e saved sp c.get input.length
    (HeadByteInput.term input) pc early stack
    ((frame 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h10)
    ((frame 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h12)
    max hlen hm ha (HeadSaved.stored ram sp c.get)
  refine ⟨a+b,d,by omega,by omega,first.trans finish,endPC,endSP,abi,?_,?_,?_,csr2.trans csr⟩
  · rw [HeadByteInput.classification input early]
    exact result
  · have rx2 := HeadEarlyFinish.region saved sp (HeadEarlyPath.kind input.length (HeadByteInput.term input))
      516 2048 (by decide) (by decide)
    exact fun i => (rx2 i).trans (rx i)
  · intro actual state hs
    change AppState.At (HeadEarlyFinish.memory (HeadStackSave.memory ram sp c.get) sp
      (HeadEarlyPath.kind input.length (HeadByteInput.term input))) state
    rw [actual]
    exact HeadEarlyFinish.app _ _ state (HeadStackMemory.app ram c.get state hs)

/-- All actual strict prefixes of these byte-derived early parser returns
    agree with the instruction certificate under the established IRQ mask. -/
theorem safe_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (input : List (BitVec 8))
    (hp : c.pc=0x80002c46#32) (h2 : c.get 2=sp+384#32) (h10 : c.get 10=sp+4904#32)
    (h11 : c.get 11=sp+516#32) (h12 : c.get 12=BitVec.ofNat 32 input.length) (h13 : c.get 13=sp+3664#32)
    (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0) (hlen : input.length≤2048)
    (hmax : ramRead ram (sp+3664#32) .w=1024#32) (bytesAt : Bytes.At ram (sp+516#32) input)
    (early : HeadByteInput.term input=1 ∨ HeadByteInput.term input=2) (masked : c.mie_=false) :
    ∃ n d, 38≤n ∧ n≤49+7*min input.length 1024 ∧
      Trace.Closed B img n ⟨c,ram⟩ ⟨d,memory ram sp c.get input⟩ ∧
      d.pc=c.get 1 &&& ~~~1 ∧ HeadResultView.At (memory ram sp c.get input) (sp+4904#32) (HttpRequestBytes.parse input 1024 1024) ∧
      (∀ count e reads evs, count<n → Observed.Steps B img count ⟨c,ram⟩ e reads evs →
        reads=[] ∧ evs=[] ∧ ¬Escapes B img e) := by
  obtain ⟨n,d,hlo,hi,trace,pc,stack,abi,result,rx,app,csr⟩ :=
    contract B c ram sp input hp h2 h10 h11 h12 h13 hm ha hlen hmax bytesAt early
  exact ⟨n,d,hlo,hi,Interrupt.close trace.det masked,pc,result,
    fun _ _ _ _ hk actual => QuietPrefix.safe trace masked hk actual⟩
end E5R.Thermostat.HeadEarlyInput
