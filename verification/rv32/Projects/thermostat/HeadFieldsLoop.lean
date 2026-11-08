import Projects.thermostat.HeadFieldsStep
import Projects.thermostat.HeadFieldsProgress
namespace E5R.Thermostat.HeadFieldsLoop
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

def budget (cap count : Nat) : Nat := (17-count)*(662+108*cap)

def At (c : Core) (ram : Word → BitVec 8) (sp : Word) (length minor : Nat) : Fielded → Prop
  | .more => c.pc=0x800033ea#32
  | .bad status => c.pc=0x8000342c#32 ∧ c.get 1=BitVec.ofNat 32 status
  | .done f len => c.pc=0x80003456#32 ∧ c.get 24=BitVec.ofNat 32 (len-2) ∧
      HeadFieldsView.At ram sp f ∧ c.get 23=(if f.te then 1#32 else 0#32)

theorem one_budget (cap count : Nat) (bound : count≤16) : 662+108*cap≤budget cap count := by
  have h := Nat.mul_le_mul_right (662+108*cap) (show 1≤17-count by omega)
  simpa only [Nat.one_mul,budget] using h

/-- All actual F58 header iterations until More/Bad/empty-line completion.
    Every continued iteration appends one real field, so the capacity guard
    bounds execution by seventeen iterations. The fixed input agreement is
    bounded by cap, avoiding unsound equality across wrapping RAM aliases. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (g : Nat → Nat)
    (i cap length minor : Nat) (f : Fields)
    (regs : HeadFieldsRegs.At c sp i length minor f) (metadata : HeadFieldsMeta.At ram sp length cap)
    (fields : HeadFieldsView.At ram sp f) (agree : ∀ k, k<cap → bytes ram (sp+516#32) k=g k)
    (inside : i<cap) (upper : cap≤length) (bound : length≤2048) (version : minor≤1)
    (stack : Memory.Block B sp 5312) (aligned : sp.toNat%4=0)
    (clOutside : ∀ q : Fin 14, B.inRam (BitVec.ofNat 32 (0x80005de0+q.val)) 1=false)
    (teOutside : ∀ q : Fin 17, B.inRam (BitVec.ofNat 32 (0x80005dee+q.val)) 1=false) :
    ∃ n d after, 10≤n ∧ n≤budget cap f.headers.length ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      At d after sp length minor (HttpRequestSpec.fields g cap minor 1024 i f) ∧
      HeadFieldsMeta.At after sp length cap ∧ HeadFieldsConstants.At d sp length minor ∧
      HeadFieldsStepFrame.At ram after sp ∧ HeadRegisterFrame.At c d HeadFieldsStep.writes ∧ d.sameCsr c := by
  obtain ⟨n,a,mid,lo,hi,step,post,metadataMid,constantsMid,memoryFrame,regFrame,csr⟩ := HeadFieldsStep.contract B c ram sp i cap length minor f regs metadata fields inside upper bound version stack aligned clOutside teOutside
  have inputEq := HeadFieldsInputCongr.one_congr (bytes ram (sp+516#32)) g i cap minor f inside agree
  rw [inputEq] at post
  have spec := HeadFieldsStepSpec.fields_eq g i cap minor f inside
  have oneBound : n≤662+108*cap := by omega
  have baseBound : n≤budget cap f.headers.length := Nat.le_trans oneBound (one_budget cap f.headers.length fields.count_bound)
  cases selected : HeadFieldsStepSpec.one g i cap minor f with
  | more =>
    have got : a.pc=0x800033ea#32 := by simpa only [HeadFieldsStep.At,selected] using post
    rw [spec,selected]
    exact ⟨n,a,mid,lo,baseBound,step,got,metadataMid,constantsMid,memoryFrame,regFrame,csr⟩
  | bad status =>
    have got : a.pc=0x8000342c#32 ∧ a.get 1=BitVec.ofNat 32 status := by simpa only [HeadFieldsStep.At,selected] using post
    rw [spec,selected]
    exact ⟨n,a,mid,lo,baseBound,step,got,metadataMid,constantsMid,memoryFrame,regFrame,csr⟩
  | done nextFields len =>
    have got : a.pc=0x80003456#32 ∧ a.get 24=BitVec.ofNat 32 (len-2) ∧ HeadFieldsView.At mid sp nextFields ∧ a.get 23=(if nextFields.te then 1#32 else 0#32) := by
      simpa only [HeadFieldsStep.At,selected] using post
    rw [spec,selected]
    exact ⟨n,a,mid,lo,baseBound,step,got,metadataMid,constantsMid,memoryFrame,regFrame,csr⟩
  | again index nextFields =>
    have got : HeadFieldsRegs.At a sp index length minor nextFields ∧ HeadFieldsView.At mid sp nextFields := by
      simpa only [HeadFieldsStep.At,selected] using post
    obtain ⟨progress,indexBound,countNext⟩ := HeadFieldsProgress.again g i cap minor index f nextFields inside selected
    have agreeMid (k : Nat) (hk : k<cap) : bytes mid (sp+516#32) k=g k := by
      have rx := memoryFrame 516 2048 (by decide) (by decide)
      exact (congrArg BitVec.toNat (rx ⟨k,by omega⟩)).trans (agree k hk)
    obtain ⟨rest,d,after,rlo,rhi,tail,result,metadataAfter,constantsAfter,memoryAfter,frameAfter,csrAfter⟩ := contract B a mid sp g index cap length minor nextFields
      got.1 metadataMid got.2 agreeMid indexBound upper bound version stack aligned clOutside teOutside
    have shift : 17-f.headers.length=(17-nextFields.headers.length)+1 := by have h := got.2.count_bound;omega
    have budgetShift : budget cap f.headers.length=budget cap nextFields.headers.length+(662+108*cap) := by
      unfold budget
      rw [shift,Nat.add_mul,Nat.one_mul]
    have totalBound : n+rest≤budget cap f.headers.length := by rw [budgetShift];omega
    rw [spec,selected]
    exact ⟨n+rest,d,after,by omega,totalBound,step.trans tail,result,metadataAfter,constantsAfter,
      HeadFieldsStepFrame.trans memoryFrame memoryAfter,
      HeadRegisterFrame.mono (HeadRegisterFrame.trans regFrame frameAfter) (by decide +kernel),csrAfter.trans csr⟩
termination_by 17-f.headers.length
 decreasing_by have old := fields.count_bound;have new := got.2.count_bound;omega
end E5R.Thermostat.HeadFieldsLoop
