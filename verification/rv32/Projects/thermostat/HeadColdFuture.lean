import Projects.thermostat.HeadColdFutureComplete
import Projects.thermostat.HeadPrefix
namespace E5R.Thermostat.HeadColdFuture
open E5R E5R.Thermostat

/-- Complete actual ELF parse_head for every receive slice of at most 2048
    bytes, including malformed/truncated first lines, all fields and successful
    result construction. This is a parser contract, not a firmware loop claim. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (input : List (BitVec 8))
    (hp : c.pc=0x80002c46#32) (h2 : c.get 2=sp+384#32) (h10 : c.get 10=sp+4904#32)
    (h11 : c.get 11=sp+516#32) (h12 : c.get 12=BitVec.ofNat 32 input.length) (h13 : c.get 13=sp+3664#32)
    (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0) (hlen : input.length≤2048)
    (hmax : ramRead ram (sp+3664#32) .w=1024#32) (bytesAt : Bytes.At ram (sp+516#32) input)
    (hbody : ramRead ram (sp+3668#32) .w=1024#32)
    (clOutside : ∀ q : Fin 14, B.inRam (BitVec.ofNat 32 (0x80005de0+q.val)) 1=false)
    (teOutside : ∀ q : Fin 17, B.inRam (BitVec.ofNat 32 (0x80005dee+q.val)) 1=false) :
    ∃ steps d after, 19≤steps ∧ steps≤HeadColdFutureComplete.budget (min input.length 1024) ∧ Quiet.Steps B img steps ⟨c,ram⟩ ⟨d,after⟩ ∧
      d.pc=c.get 1 &&& ~~~1 ∧ d.get 2=sp+384#32 ∧ HeadSaved.CoreAt d c.get ∧
      HeadFinalResult.At after (sp+4904#32) (HttpRequestBytes.parse input 1024 1024) ∧
      ViewFrame.Region ram after (sp+516#32) 2048 ∧
      (sp=0x80ffea10#32 → ∀ state, AppState.At ram state → AppState.At after state) ∧ d.sameCsr c ∧ ViewFrame.Region ram after (sp+3588#32) 449 := by
  by_cases complete : HeadByteInput.term input=0
  · exact HeadColdFutureComplete.contract B c ram sp input hp h2 h10 h11 h12 h13 hm ha hlen hmax bytesAt complete hbody clOutside teOutside
  · have early : HeadByteInput.term input=1 ∨ HeadByteInput.term input=2 := (HeadPrefix.term_cases input).resolve_left complete
    obtain ⟨steps,d,lo,hi,trace,dpc,dsp,regs,result,rx,app,csr⟩ := HeadEarlyInput.contract B c ram sp input hp h2 h10 h11 h12 h13 hm ha hlen hmax bytesAt early
    have future : ViewFrame.Region ram (HeadEarlyInput.memory ram sp c.get input) (sp+3588#32) 449 :=
      HeadRegionFrame.trans (HeadStackMemory.region ram sp c.get 3588 449 (by decide) (by decide))
        (HeadEarlyFinish.region (HeadStackSave.memory ram sp c.get) sp _ 3588 449 (by decide) (Or.inl (by decide)))
    exact ⟨steps,d,_,by omega,by unfold HeadColdFutureComplete.budget;omega,trace,dpc,dsp,regs,HeadFinalResult.early result,rx,app,csr,future⟩

theorem safe_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (input : List (BitVec 8))
    (hp : c.pc=0x80002c46#32) (h2 : c.get 2=sp+384#32) (h10 : c.get 10=sp+4904#32)
    (h11 : c.get 11=sp+516#32) (h12 : c.get 12=BitVec.ofNat 32 input.length) (h13 : c.get 13=sp+3664#32)
    (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0) (hlen : input.length≤2048)
    (hmax : ramRead ram (sp+3664#32) .w=1024#32) (bytesAt : Bytes.At ram (sp+516#32) input)
    (hbody : ramRead ram (sp+3668#32) .w=1024#32)
    (clOutside : ∀ q : Fin 14, B.inRam (BitVec.ofNat 32 (0x80005de0+q.val)) 1=false)
    (teOutside : ∀ q : Fin 17, B.inRam (BitVec.ofNat 32 (0x80005dee+q.val)) 1=false) (masked : c.mie_=false) :
    ∃ steps d after, 19≤steps ∧ steps≤HeadColdFutureComplete.budget (min input.length 1024) ∧ Trace.Closed B img steps ⟨c,ram⟩ ⟨d,after⟩ ∧
      d.pc=c.get 1 &&& ~~~1 ∧ d.get 2=sp+384#32 ∧ HeadSaved.CoreAt d c.get ∧
      HeadFinalResult.At after (sp+4904#32) (HttpRequestBytes.parse input 1024 1024) ∧
      ViewFrame.Region ram after (sp+516#32) 2048 ∧
      (sp=0x80ffea10#32 → ∀ state, AppState.At ram state → AppState.At after state) ∧ d.sameCsr c ∧ ViewFrame.Region ram after (sp+3588#32) 449 ∧
      (∀ count e reads evs, count<steps → Observed.Steps B img count ⟨c,ram⟩ e reads evs → reads=[] ∧ evs=[] ∧ ¬Escapes B img e) := by
  obtain ⟨steps,d,after,lo,hi,trace,dpc,dsp,regs,result,rx,app,csr,future⟩ := contract B c ram sp input hp h2 h10 h11 h12 h13 hm ha hlen hmax bytesAt hbody clOutside teOutside
  exact ⟨steps,d,after,lo,hi,Interrupt.close trace.det masked,dpc,dsp,regs,result,rx,app,csr,future,
    fun _ _ _ _ hk actual => QuietPrefix.safe trace masked hk actual⟩
end E5R.Thermostat.HeadColdFuture
