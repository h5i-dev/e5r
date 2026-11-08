import Projects.thermostat.HeadColdSpec
namespace E5R.Thermostat.HeadColdComplete
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

def budget (cap : Nat) : Nat := 802+36*cap+HeadFieldsLoopComplete.budget cap 0

/-- Cold actual parser with a complete first line, all headers, Host/framing
    checks, complete RAM result and real ABI return. Every typed header derives
    from the original byte slice. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (input : List (BitVec 8))
    (hp : c.pc=0x80002c46#32) (h2 : c.get 2=sp+384#32) (h10 : c.get 10=sp+4904#32)
    (h11 : c.get 11=sp+516#32) (h12 : c.get 12=BitVec.ofNat 32 input.length) (h13 : c.get 13=sp+3664#32)
    (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0) (hlen : input.length≤2048)
    (hmax : ramRead ram (sp+3664#32) .w=1024#32) (bytesAt : Bytes.At ram (sp+516#32) input)
    (complete : HeadByteInput.term input=0) (hbody : ramRead ram (sp+3668#32) .w=1024#32)
    (clOutside : ∀ q : Fin 14, B.inRam (BitVec.ofNat 32 (0x80005de0+q.val)) 1=false)
    (teOutside : ∀ q : Fin 17, B.inRam (BitVec.ofNat 32 (0x80005dee+q.val)) 1=false) :
    ∃ steps d after, 19≤steps ∧ steps≤budget (min input.length 1024) ∧ Quiet.Steps B img steps ⟨c,ram⟩ ⟨d,after⟩ ∧
      d.pc=c.get 1 &&& ~~~1 ∧ d.get 2=sp+384#32 ∧ HeadSaved.CoreAt d c.get ∧
      HeadFinalResult.At after (sp+4904#32) (HttpRequestBytes.parse input 1024 1024) ∧
      ViewFrame.Region ram after (sp+516#32) 2048 ∧
      (sp=0x80ffea10#32 → ∀ state, AppState.At ram state → AppState.At after state) ∧ d.sameCsr c := by
  let cap := min input.length 1024
  let j := HeadRequestInputStorage.line input
  have capBound : cap≤1024 := Nat.min_le_right input.length 1024
  have lineBound : j≤cap := scan_le notEol (HeadColdSpec.inputBytes input) 0 cap (by omega)
  obtain ⟨n,a,after,nlo,nhi,first,result,rx,app,saved,csr,config⟩ := HeadRequestInputStorage.contract B c ram sp input hp h2 h10 h11 h12 h13 hm ha hlen hmax bytesAt complete
  cases request : HeadRequestInputStorage.request input with
  | bad status =>
    rw [request] at result
    obtain ⟨pc,stack,abi,encoded⟩ := result
    refine ⟨n,a,after,nlo,?_,first,pc,stack,abi,?_,rx,app,csr⟩
    · unfold budget;omega
    · rw [HeadColdSpec.bad input status complete request]
      exact encoded
  | ok ms me ts te minor =>
    rw [request] at result
    have ready := result.2.2
    have version : minor≤1 := (HeadRequestSuccess.shape (HeadColdSpec.inputBytes input) j ms me ts te minor request).2.2
    have body : ramRead after (sp+3668#32) .w=1024#32 := by
      have word := ViewFrame.word config 4 (by decide)
      have ptr : (sp+3664#32)+4#32=sp+3668#32 := by rw [BitVec.add_assoc];rfl
      rw [ptr] at word
      exact word.trans hbody
    obtain ⟨m,d,finalRAM,mlo,mhi,finish,pc,stack,abi,encoded,frames,csr2⟩ := HeadFieldsWhole.contract B a after sp me te j minor input.length cap c.get
      ready body (by omega) capBound (Nat.min_le_left _ _) hlen version hm ha saved clOutside teOutside
    have agree (k : Nat) (hk : k<cap) : bytes after (sp+516#32) k=HeadColdSpec.inputBytes input k :=
      (congrArg BitVec.toNat (rx ⟨k,by omega⟩)).trans (HeadByteInput.agree bytesAt k hk)
    have sameFields := HeadFieldsCongr.fields (bytes after (sp+516#32)) (HeadColdSpec.inputBytes input) cap minor (j+2) Fields.empty agree
    change HeadFinalResult.At finalRAM (sp+4904#32) (HeadFieldsFinish.result input.length me (me+1) te minor (fields (bytes after (sp+516#32)) cap minor 1024 (j+2) Fields.empty)) at encoded
    rw [sameFields] at encoded
    refine ⟨n+m,d,finalRAM,by omega,?_,first.trans finish,pc,stack,abi,?_,?_,?_,csr2.trans csr⟩
    · dsimp only [cap] at mhi
      unfold budget;omega
    · rw [HeadColdSpec.good input ms me ts te minor complete request]
      exact encoded
    · exact HeadRegionFrame.trans rx (frames 516 2048 (by decide) (by decide) (Or.inl (by decide)))
    · intro actual state initial
      apply AppState.preserve after finalRAM state (app actual state initial)
      simpa only [ViewFrame.Region,actual,show 0x80ffea10#32+428#32=0x80ffebbc#32 by decide +kernel] using frames 428 25 (by decide) (by decide) (Or.inl (by decide))
end E5R.Thermostat.HeadColdComplete
