import Projects.thermostat.HeadFinalResult
import Projects.thermostat.HeadFieldsLoopComplete
import Projects.thermostat.HeadFieldsResultSpec
import Projects.thermostat.HeadFieldsMore
import Projects.thermostat.HeadFieldsReject
namespace E5R.Thermostat.HeadFieldsFinish
open E5R E5R.Thermostat HttpRequestSpec

def result (length method targetStart targetEnd minor : Nat) : Fielded → HeadR
  | .more => HeadFieldsMore.out length
  | .bad status => .reject status
  | .done f len => HeadFinalResult.result method targetStart targetEnd len minor f

def Frame (before after : Word → BitVec 8) (sp : Word) : Prop :=
  ∀ off size : Nat, off+size≤5312 → (off+size≤4904 ∨ 5201≤off) → ViewFrame.Region before after (sp+BitVec.ofNat 32 off) size

/-- The three actual header-loop exits, including all success stores and every
    ABI return. Bounds below are derived from the independent fields parser. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word)
    (length cap method targetStart targetEnd minor : Nat) (parsed : Fielded) (saved : Reg → Word)
    (cut : HeadFieldsLoopComplete.At c ram sp length minor parsed) (bounds : HeadFieldsResultSpec.Bound cap parsed)
    (h2 : c.get 2=sp) (version : minor≤1) (lengthBound : length≤2048)
    (raw : ramRead ram (sp+48#32) .w=BitVec.ofNat 32 length) (maximum : ramRead ram (sp+36#32) .w=1024#32)
    (output : ramRead ram (sp+52#32) .w=sp+4904#32)
    (methodWord : ramRead ram (sp+20#32) .w=BitVec.ofNat 32 method)
    (targetStartWord : ramRead ram (sp+24#32) .w=BitVec.ofNat 32 targetStart)
    (targetEndWord : ramRead ram (sp+28#32) .w=BitVec.ofNat 32 targetEnd)
    (stack : Memory.Block B sp 5312) (aligned : sp.toNat%4=0) (stored : HeadSaved.At ram sp saved) :
    ∃ n d after, 21≤n ∧ n≤392 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      d.pc=saved 1 &&& ~~~1 ∧ d.get 2=sp+384#32 ∧ HeadSaved.CoreAt d saved ∧
      HeadFinalResult.At after (sp+4904#32) (result length method targetStart targetEnd minor parsed) ∧ Frame ram after sp ∧ d.sameCsr c := by
  cases parsed with
  | more =>
    obtain ⟨n,d,lo,hi,steps,dpc,dsp,regs,view,csr⟩ := HeadFieldsMore.contract B c ram sp length saved cut h2 raw maximum output lengthBound stack aligned stored
    refine ⟨n,d,_,by omega,by omega,steps,dpc,dsp,regs,HeadFinalResult.early view,?_,csr⟩
    intro off size bound apart
    exact HeadFieldsMore.region ram sp length off size (by omega) (by rcases apart with h|h <;> omega)
  | bad status =>
    obtain ⟨d,steps,dpc,dsp,regs,view,csr⟩ := HeadFieldsReject.contract B c ram sp saved status cut.1 h2 output cut.2 bounds stack aligned stored
    refine ⟨21,d,_,by decide,by decide,steps,dpc,dsp,regs,view,?_,csr⟩
    intro off size bound apart
    exact HeadResultFrame.reject_region ram sp _ _ off size (by omega) (by rcases apart with h|h <;> omega)
  | done f len =>
    obtain ⟨pc,position,view,transfer,count,constants⟩ := cut
    obtain ⟨n,d,lo,hi,steps,dpc,dsp,regs,viewAfter,csr⟩ := HeadFinalResult.contract B c ram sp method targetStart targetEnd len minor length f saved
      pc constants view count position transfer bounds.1 version output methodWord targetStartWord targetEndWord stack aligned stored
    exact ⟨n,d,_,by omega,hi,steps,dpc,dsp,regs,viewAfter,HeadFinalResult.region ram sp method targetStart targetEnd len minor f,csr⟩
end E5R.Thermostat.HeadFieldsFinish
