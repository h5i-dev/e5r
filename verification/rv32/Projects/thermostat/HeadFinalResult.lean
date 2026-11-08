import Projects.thermostat.HeadCompletedView
import Projects.thermostat.HeadMissingHostFinish
import Projects.thermostat.HeadRegionFrame
namespace E5R.Thermostat.HeadFinalResult
open E5R E5R.Thermostat HttpRequestSpec

def At (ram : Word → BitVec 8) (dst : Word) : HeadR → Prop
  | .incomplete => HeadResultView.At ram dst .incomplete
  | .reject status => HeadResultView.At ram dst (.reject status)
  | .done h => HeadCompletedView.At ram dst h

theorem early {ram dst result} (h : HeadResultView.At ram dst result) : At ram dst result := by
  cases result with
  | incomplete => exact h
  | reject status => exact h
  | done head => exact False.elim h

def result (method targetStart targetEnd len minor : Nat) (f : Fields) : HeadR :=
  if minor=1 ∧ f.host=false then .reject 400 else .done (HeadCompletedView.head method targetStart targetEnd len minor f)

def memory (ram : Word → BitVec 8) (sp : Word) (method targetStart targetEnd len minor : Nat) (f : Fields) :=
  if minor=1 ∧ f.host=false then HeadResultStore.memory ram (sp+4904#32) 4#32 400#32
  else HeadCompletedView.memory ram sp method targetStart targetEnd len minor f

/-- Actual Done cutpoint through both Host refusal and complete success ABI
    returns. The complete result is established in RAM, not merely in registers. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word)
    (method targetStart targetEnd len minor length : Nat) (f : Fields) (saved : Reg → Word)
    (hp : c.pc=0x80003456#32) (constants : HeadFieldsConstants.At c sp length minor)
    (view : HeadFieldsView.At ram sp f) (count : c.get 9=BitVec.ofNat 32 f.headers.length)
    (position : c.get 24=BitVec.ofNat 32 (len-2)) (transfer : c.get 23=(if f.te then 1#32 else 0#32))
    (positive : 2≤len) (version : minor≤1)
    (output : ramRead ram (sp+52#32) .w=sp+4904#32)
    (methodWord : ramRead ram (sp+20#32) .w=BitVec.ofNat 32 method)
    (targetStartWord : ramRead ram (sp+24#32) .w=BitVec.ofNat 32 targetStart)
    (targetEndWord : ramRead ram (sp+28#32) .w=BitVec.ofNat 32 targetEnd)
    (stack : Memory.Block B sp 5312) (aligned : sp.toNat%4=0) (stored : HeadSaved.At ram sp saved) :
    ∃ n d, 27≤n ∧ n≤392 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,memory ram sp method targetStart targetEnd len minor f⟩ ∧
      d.pc=saved 1 &&& ~~~1 ∧ d.get 2=sp+384#32 ∧ HeadSaved.CoreAt d saved ∧
      At (memory ram sp method targetStart targetEnd len minor f) (sp+4904#32) (result method targetStart targetEnd len minor f) ∧ d.sameCsr c := by
  have small : Memory.Block B sp 327 := by simpa only [BitVec.add_zero] using Memory.sub_block stack (off := 0) (by decide) (by decide)
  obtain ⟨n,a,lo,hi,ta,post,ac⟩ := HeadDonePrepare.contract B c ram sp f len minor length hp constants view count position transfer positive version small aligned
  by_cases missing : minor=1 ∧ f.host=false
  · have bad : HeadDonePrepare.Missing a sp := by simpa only [missing,true_and,ite_true] using post
    obtain ⟨d,td,dpc,dsp,regs,resultView,dc⟩ := HeadMissingHostFinish.contract B a ram sp saved bad output stack aligned stored
    refine ⟨n+20,d,by omega,by omega,?_,dpc,dsp,regs,?_,dc.trans ac⟩
    · simpa only [memory,missing,true_and,ite_true] using ta.trans td
    · simpa only [memory,result,missing,true_and,ite_true] using early resultView
  · have ready : HeadDonePrepare.Ready a sp f len minor := by simpa only [missing,ite_false] using post
    obtain ⟨d,td,dpc,dsp,regs,dc⟩ := HeadDoneCommit.contract B a ram sp _ _ _ _ _ _ _ _ _ saved
      ready.pc ready.stack ready.tag ready.low ready.high ready.count ready.length ready.version output methodWord targetStartWord targetEndWord stack aligned stored
    refine ⟨n+380,d,by omega,by omega,?_,dpc,dsp,regs,?_,dc.trans ac⟩
    · simpa only [memory,missing,ite_false,HeadCompletedView.memory] using ta.trans td
    · simpa only [memory,result,missing,ite_false,At] using HeadCompletedView.stored B ram sp method targetStart targetEnd len minor f view stack version

theorem region (ram : Word → BitVec 8) (sp : Word) (method targetStart targetEnd len minor : Nat) (f : Fields)
    (off size : Nat) (bound : off+size≤5312) (apart : off+size≤4904 ∨ 5201≤off) :
    ViewFrame.Region ram (memory ram sp method targetStart targetEnd len minor f) (sp+BitVec.ofNat 32 off) size := by
  unfold memory
  split
  · exact HeadResultFrame.reject_region ram sp 4#32 400#32 off size (by omega) (by rcases apart with h|h <;> omega)
  · apply HeadRegionFrame.trans (HeadCopyHeader256.frame ram sp off size bound (by rcases apart with h|h <;> omega))
    exact HeadDoneMemory.region _ sp _ _ _ _ _ _ _ _ _ off size bound (by rcases apart with h|h <;> omega) (by rcases apart with h|h <;> omega)
end E5R.Thermostat.HeadFinalResult
