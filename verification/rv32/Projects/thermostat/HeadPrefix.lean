import Projects.thermostat.HeadRequestInput
import Projects.thermostat.HeadEarlyInput
namespace E5R.Thermostat.HeadPrefix
open E5R E5R.Thermostat HttpRequestSpec

/-- Actual parser prefix result: a complete early return specified by parseHead,
    or a decoded request-line result (which itself returns on error or establishes
    concrete header-entry state). No successful HeadR result is postulated. -/
def At (c : Core) (ram : Word → BitVec 8) (sp : Word) (values : Reg → Word) (input : List (BitVec 8)) : Prop :=
  if HeadByteInput.term input=0 then
    HeadRequestOutcome.At c ram sp values (HeadRequestInput.line input) input.length (min input.length 1024) (HeadRequestInput.request input)
  else c.pc=values 1 &&& ~~~1 ∧ c.get 2=sp+384#32 ∧ HeadSaved.CoreAt c values ∧
    HeadResultView.At ram (sp+4904#32) (HttpRequestBytes.parse input 1024 1024)

theorem term_cases (input : List (BitVec 8)) :
    HeadByteInput.term input=0 ∨ HeadByteInput.term input=1 ∨ HeadByteInput.term input=2 := by
  unfold HeadByteInput.term lineTerm
  dsimp only
  repeat' first | omega | split

/-- Cold ELF parser entry for every byte slice of at most 2048 bytes, including
    empty/truncated/malformed first lines. Every case returns as specified or
    reaches the checked header-parser entry; IRQ-disabled strict prefixes have
    no unsupported/fault escape. Header fields remain a separate obligation. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (input : List (BitVec 8))
    (hp : c.pc=0x80002c46#32) (h2 : c.get 2=sp+384#32) (h10 : c.get 10=sp+4904#32)
    (h11 : c.get 11=sp+516#32) (h12 : c.get 12=BitVec.ofNat 32 input.length) (h13 : c.get 13=sp+3664#32)
    (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0) (hlen : input.length≤2048)
    (hmax : ramRead ram (sp+3664#32) .w=1024#32) (bytesAt : Bytes.At ram (sp+516#32) input) :
    ∃ steps d after, 19≤steps ∧ steps≤153+36*min input.length 1024 ∧ Quiet.Steps B img steps ⟨c,ram⟩ ⟨d,after⟩ ∧
      At d after sp c.get input ∧ ViewFrame.Region ram after (sp+516#32) 2048 ∧
      (sp=0x80ffea10#32 → ∀ state, AppState.At ram state → AppState.At after state) ∧
      HeadSaved.At after sp c.get ∧ d.sameCsr c := by
  by_cases complete : HeadByteInput.term input=0
  · obtain ⟨steps,d,after,hlo,hi,trace,result,rx,app,saved,csr⟩ := HeadRequestInput.contract B c ram sp input
      hp h2 h10 h11 h12 h13 hm ha hlen hmax bytesAt complete
    refine ⟨steps,d,after,hlo,hi,trace,?_,rx,app,saved,csr⟩
    simpa only [At,complete,ite_true] using result
  · have early : HeadByteInput.term input=1 ∨ HeadByteInput.term input=2 := (term_cases input).resolve_left complete
    obtain ⟨steps,d,hlo,hi,trace,pc,stack,abi,result,rx,app,csr⟩ := HeadEarlyInput.contract B c ram sp input
      hp h2 h10 h11 h12 h13 hm ha hlen hmax bytesAt early
    refine ⟨steps,d,_,by omega,by omega,trace,?_,rx,app,?_,csr⟩
    · simp only [At,complete,ite_false]
      exact ⟨pc,stack,abi,result⟩
    · exact HeadEarlyFinish.saved (HeadSaved.stored ram sp c.get)
theorem safe_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (input : List (BitVec 8))
    (hp : c.pc=0x80002c46#32) (h2 : c.get 2=sp+384#32) (h10 : c.get 10=sp+4904#32)
    (h11 : c.get 11=sp+516#32) (h12 : c.get 12=BitVec.ofNat 32 input.length) (h13 : c.get 13=sp+3664#32)
    (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0) (hlen : input.length≤2048)
    (hmax : ramRead ram (sp+3664#32) .w=1024#32) (bytesAt : Bytes.At ram (sp+516#32) input) (masked : c.mie_=false) :
    ∃ steps d after, 19≤steps ∧ steps≤153+36*min input.length 1024 ∧ Trace.Closed B img steps ⟨c,ram⟩ ⟨d,after⟩ ∧
      At d after sp c.get input ∧ ViewFrame.Region ram after (sp+516#32) 2048 ∧
      (sp=0x80ffea10#32 → ∀ state, AppState.At ram state → AppState.At after state) ∧
      HeadSaved.At after sp c.get ∧ d.sameCsr c ∧
      (∀ count e reads evs, count<steps → Observed.Steps B img count ⟨c,ram⟩ e reads evs →
        reads=[] ∧ evs=[] ∧ ¬Escapes B img e) := by
  obtain ⟨steps,d,after,hlo,hi,trace,result,rx,app,saved,csr⟩ := contract B c ram sp input
    hp h2 h10 h11 h12 h13 hm ha hlen hmax bytesAt
  exact ⟨steps,d,after,hlo,hi,Interrupt.close trace.det masked,result,rx,app,saved,csr,
    fun _ _ _ _ hk actual => QuietPrefix.safe trace masked hk actual⟩
end E5R.Thermostat.HeadPrefix
