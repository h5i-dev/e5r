import Projects.thermostat.HeadVersion
import Projects.thermostat.HeadRequestRejectPath
namespace E5R.Thermostat.HeadVersionReject
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

def status (ram : Word → BitVec 8) (sp : Word) (te : Nat) : Nat :=
  if HttpRequestSpec.version (bytes ram (sp+516#32)) (te+1) (te+9)=3 then 400 else 505

def memory (ram : Word → BitVec 8) (sp : Word) (c : Core) (te : Nat) :=
  HeadResultStore.memory (HeadVersion.memory ram sp c te) (sp+4904#32) 4#32 (BitVec.ofNat 32 (status ram sp te))

/-- Actual complete version rejection and full parser ABI return. The status
    is computed from independent byte-level version, including unsupported 505. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (m te length : Nat)
    (hp : c.pc=0x80002e20#32) (h2 : c.get 2=sp) (h10 : c.get 10=sp+4904#32) (h11 : c.get 11=sp+516#32)
    (h12 : c.get 12=BitVec.ofNat 32 length) (h17 : c.get 17=BitVec.ofNat 32 m)
    (h30 : c.get 30=BitVec.ofNat 32 (te-m-1)) (h7 : c.get 7=BitVec.ofNat 32 (te-1))
    (h6 : c.get 6=sp+516#32+BitVec.ofNat 32 (te-1)) (h15 : c.get 15=400#32)
    (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0)
    (hmt : m<te) (hw : te+9≤length) (hlen : length≤2048) (values : Reg → Word) (saved : HeadSaved.At ram sp values)
    (refused : ¬HttpRequestSpec.version (bytes ram (sp+516#32)) (te+1) (te+9)<2) :
    ∃ n d, 23≤n ∧ n≤89 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,memory ram sp c te⟩ ∧
      d.pc=values 1 &&& ~~~1 ∧ d.get 2=sp+384#32 ∧ HeadSaved.CoreAt d values ∧
      HeadResultView.At (memory ram sp c te) (sp+4904#32) (.reject (status ram sp te)) ∧
      ViewFrame.Region ram (memory ram sp c te) (sp+516#32) 2048 ∧
      (sp=0x80ffea10#32 → ∀ state, AppState.At ram state → AppState.At (memory ram sp c te) state) ∧ d.sameCsr c := by
  let v := HttpRequestSpec.version (bytes ram (sp+516#32)) (te+1) (te+9)
  obtain ⟨a,e,alo,ahi,parse,result,stack,reloadWord,frame,csr⟩ := HeadVersion.contract B c ram sp m te length
    hp h2 h10 h11 h12 h17 h30 h7 h6 h15 hm ha hmt hw hlen
  change HeadVersionResult.At e v (c.get 13) (sp+4904#32) at result
  unfold HeadVersionResult.At at result
  have refusedV : ¬v<2 := refused
  simp only [refusedV,ite_false] at result
  have statusWord : e.get 15=BitVec.ofNat 32 (status ram sp te) := by
    have hs := result.2.1
    by_cases three : v=3
    · simpa only [status,show HttpRequestSpec.version (bytes ram (sp+516#32)) (te+1) (te+9)=v from rfl,three,ite_true] using hs
    · simpa only [status,show HttpRequestSpec.version (bytes ram (sp+516#32)) (te+1) (te+9)=v from rfl,three,ite_false] using hs
  have statusBound : status ram sp te<65536 := by unfold status;split <;> decide
  obtain ⟨b,d,blo,bhi,finish,endPC,endSP,abi,out,csr2⟩ := HeadRequestRejectPath.contract B e (HeadVersion.memory ram sp c te) sp values (status ram sp te)
    result.1 stack reloadWord result.2.2 statusWord statusBound hm ha (HeadVersion.saved ram sp c te values saved)
  refine ⟨a+b,d,by omega,by omega,parse.trans finish,endPC,endSP,abi,out,?_,?_,csr2.trans csr⟩
  · have f1 := HeadVersion.region ram sp c te 516 2048 (by decide) (by decide)
    have f2 := HeadResultFrame.reject_region (HeadVersion.memory ram sp c te) sp 4#32 (BitVec.ofNat 32 (status ram sp te)) 516 2048 (by decide) (by decide)
    exact fun i => (f2 i).trans (f1 i)
  · intro actual state app
    apply AppState.preserve ram _ state app
    have f1 := HeadVersion.region ram sp c te 428 25 (by decide) (by decide)
    have f2 := HeadResultFrame.reject_region (HeadVersion.memory ram sp c te) sp 4#32 (BitVec.ofNat 32 (status ram sp te)) 428 25 (by decide) (by decide)
    have frame : ViewFrame.Region ram (memory ram sp c te) (sp+428#32) 25 := fun i => (f2 i).trans (f1 i)
    simpa only [ViewFrame.Region,actual,show 0x80ffea10#32+428#32=0x80ffebbc#32 by decide +kernel] using frame
end E5R.Thermostat.HeadVersionReject
