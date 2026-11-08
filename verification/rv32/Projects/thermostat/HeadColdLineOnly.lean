import Projects.thermostat.HeadRequestInputStorage
import Projects.thermostat.HeadFieldsBeginMore
import Projects.thermostat.HeadColdLineOnlySpec
namespace E5R.Thermostat.HeadColdLineOnly
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

/-- Cold actual parse_head through complete ABI return for every complete
    first-line input with no available header line. Configuration and all
    object/stack prerequisites are established by actual preceding stores. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (input : List (BitVec 8))
    (hp : c.pc=0x80002c46#32) (h2 : c.get 2=sp+384#32) (h10 : c.get 10=sp+4904#32)
    (h11 : c.get 11=sp+516#32) (h12 : c.get 12=BitVec.ofNat 32 input.length) (h13 : c.get 13=sp+3664#32)
    (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0) (hlen : input.length≤2048)
    (hmax : ramRead ram (sp+3664#32) .w=1024#32) (bytesAt : Bytes.At ram (sp+516#32) input)
    (complete : HeadByteInput.term input=0)
    (hbody : ramRead ram (sp+3668#32) .w=1024#32) (noHeader : min input.length 1024≤HeadRequestInputStorage.line input+2) :
    ∃ steps d after, 19≤steps ∧ steps≤435+36*min input.length 1024 ∧ Quiet.Steps B img steps ⟨c,ram⟩ ⟨d,after⟩ ∧
      d.pc=c.get 1 &&& ~~~1 ∧ d.get 2=sp+384#32 ∧ HeadSaved.CoreAt d c.get ∧
      HeadResultView.At after (sp+4904#32) (HttpRequestBytes.parse input 1024 1024) ∧
      ViewFrame.Region ram after (sp+516#32) 2048 ∧
      (sp=0x80ffea10#32 → ∀ state, AppState.At ram state → AppState.At after state) ∧ d.sameCsr c := by
  let cap := min input.length 1024
  let j := HeadRequestInputStorage.line input
  have capBound : cap≤1024 := Nat.min_le_right input.length 1024
  have lineBound : j≤cap := scan_le notEol (window (HttpRequestBytes.bytes input) cap) 0 cap (by omega)
  obtain ⟨n,a,after,nlo,nhi,first,result,rx,app,saved,csr,config⟩ := HeadRequestInputStorage.contract B c ram sp input hp h2 h10 h11 h12 h13 hm ha hlen hmax bytesAt complete
  cases request : HeadRequestInputStorage.request input with
  | bad status =>
    rw [request] at result
    obtain ⟨pc,stack,abi,encoded⟩ := result
    refine ⟨n,a,after,nlo,by omega,first,pc,stack,abi,?_,rx,app,csr⟩
    rw [HeadColdLineOnlySpec.parsed input complete noHeader,HeadColdLineOnlySpec.result,request]
    exact encoded
  | ok ms me ts te minor =>
    rw [request] at result
    have ready := result.2.2
    have body : ramRead after (sp+3668#32) .w=1024#32 := by
      have word := ViewFrame.word config 4 (by decide)
      have ptr : (sp+3664#32)+4#32=sp+3668#32 := by rw [BitVec.add_assoc];rfl
      rw [ptr] at word
      exact word.trans hbody
    obtain ⟨m,d,finalRAM,mlo,mhi,finish,pc,stack,abi,encoded,rx2,app2,csr2⟩ := HeadFieldsBeginMore.contract B a after sp me te j minor input.length cap c.get
      ready body (by omega) capBound noHeader hlen hm ha saved
    refine ⟨n+m,d,finalRAM,by omega,by omega,first.trans finish,pc,stack,abi,?_,fun i => (rx2 i).trans (rx i),?_,csr2.trans csr⟩
    · rw [HeadColdLineOnlySpec.parsed input complete noHeader,HeadColdLineOnlySpec.result,request]
      exact encoded
    · intro actual state initial
      apply AppState.preserve after finalRAM state (app actual state initial)
      simpa only [ViewFrame.Region,actual,show 0x80ffea10#32+428#32=0x80ffebbc#32 by decide +kernel] using app2
end E5R.Thermostat.HeadColdLineOnly
