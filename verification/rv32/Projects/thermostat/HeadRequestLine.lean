import Projects.thermostat.HeadRequestChecked
namespace E5R.Thermostat.HeadRequestLine
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

/-- All actual request-line cases after a complete first-line delimiter.
    The independent parser chooses a real encoded error return or a fully
    established header-parser entry. The raw buffer remains immutable. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (j length cap : Nat) (values : Reg → Word)
    (hp : c.pc=0x80002cba#32) (h2 : c.get 2=sp) (h9 : c.get 9=BitVec.ofNat 32 j)
    (h10 : c.get 10=sp+4904#32) (h11 : c.get 11=sp+516#32) (h12 : c.get 12=BitVec.ofNat 32 length)
    (h13 : c.get 13=sp+3664#32) (h14 : c.get 14=BitVec.ofNat 32 cap) (h16 : c.get 16=1024#32)
    (hj : j≤length) (hlen : length≤2048) (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0)
    (saved : HeadSaved.At ram sp values) (positive : 0<length) :
    ∃ n d after, 0<n ∧ n≤126+29*j ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      HeadRequestOutcome.At d after sp values j length cap (requestLine (bytes ram (sp+516#32)) 0 j) ∧
      ViewFrame.Region ram after (sp+516#32) 2048 ∧
      (sp=0x80ffea10#32 → ∀ state, AppState.At ram state → AppState.At after state) ∧ HeadSaved.At after sp values ∧ d.sameCsr c := by
  by_cases good : HeadMethodTarget.Good (bytes ram (sp+516#32)) j
  · exact HeadRequestChecked.contract B c ram sp j length cap values hp h2 h9 h10 h11 h12 h13 h14 h16 hj hlen hm ha saved good
  · have buffer : Memory.Block B (sp+516#32) length := Memory.sub_block hm (off := 516) positive (by omega)
    obtain ⟨a,e,alo,ahi,first,pc,status,cache,frame,csr⟩ := HeadMethodTarget.contract B c ram (sp+516#32) j length hp h9 h12 h11 hj hlen buffer
    have atReject : e.pc=0x80002efc#32 := by simpa only [good,ite_false] using pc
    obtain ⟨d,finish,endPC,endSP,abi,out,csr2⟩ := HeadRequestReject.contract B e ram sp values 400 atReject
      ((frame 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2) ((frame 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h10) status (by decide) hm ha saved
    refine ⟨a+20,d,_,by omega,by omega,first.trans finish,?_,?_,?_,?_,csr2.trans csr⟩
    · rw [HeadRequestLineSpec.bad_prefix (bytes ram (sp+516#32)) j good]
      exact ⟨endPC,endSP,abi,out⟩
    · exact HeadResultFrame.reject_region ram sp 4#32 400#32 516 2048 (by decide) (by decide)
    · intro actual state app
      apply AppState.preserve ram _ state app
      have f := HeadResultFrame.reject_region ram sp 4#32 400#32 428 25 (by decide) (by decide)
      simpa only [ViewFrame.Region,actual,show 0x80ffea10#32+428#32=0x80ffebbc#32 by decide +kernel] using f
    · exact HeadResultFrame.reject_saved saved
theorem safe_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (j length cap : Nat) (values : Reg → Word)
    (hp : c.pc=0x80002cba#32) (h2 : c.get 2=sp) (h9 : c.get 9=BitVec.ofNat 32 j)
    (h10 : c.get 10=sp+4904#32) (h11 : c.get 11=sp+516#32) (h12 : c.get 12=BitVec.ofNat 32 length)
    (h13 : c.get 13=sp+3664#32) (h14 : c.get 14=BitVec.ofNat 32 cap) (h16 : c.get 16=1024#32)
    (hj : j≤length) (hlen : length≤2048) (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0)
    (saved : HeadSaved.At ram sp values) (positive : 0<length) (masked : c.mie_=false) :
    ∃ n d after, 0<n ∧ n≤126+29*j ∧ Trace.Closed B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      HeadRequestOutcome.At d after sp values j length cap (requestLine (bytes ram (sp+516#32)) 0 j) ∧
      ViewFrame.Region ram after (sp+516#32) 2048 ∧
      (sp=0x80ffea10#32 → ∀ state, AppState.At ram state → AppState.At after state) ∧ HeadSaved.At after sp values ∧ d.sameCsr c ∧
      (∀ count e reads evs, count<n → Observed.Steps B img count ⟨c,ram⟩ e reads evs →
        reads=[] ∧ evs=[] ∧ ¬Escapes B img e) := by
  obtain ⟨n,d,after,hlo,hi,trace,result,rx,app,savedOut,csr⟩ := contract B c ram sp j length cap values
    hp h2 h9 h10 h11 h12 h13 h14 h16 hj hlen hm ha saved positive
  exact ⟨n,d,after,hlo,hi,Interrupt.close trace.det masked,result,rx,app,savedOut,csr,
    fun _ _ _ _ hk actual => QuietPrefix.safe trace masked hk actual⟩
end E5R.Thermostat.HeadRequestLine
