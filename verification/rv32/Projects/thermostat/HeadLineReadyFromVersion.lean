import Projects.thermostat.HeadVersion
import Projects.thermostat.HeadLineReady
namespace E5R.Thermostat.HeadLineReadyFromVersion
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

/-- Read back all header-entry metadata from the actual version scratch stores.
    The caller supplies register equalities established by the real prefix. -/
theorem contract (c d : Core) (ram : Word → BitVec 8) (sp : Word) (m te j length cap : Nat)
    (ht : 0<te)
    (h5 : c.get 5=9409#32) (h10 : c.get 10=sp+4904#32) (h11 : c.get 11=sp+516#32)
    (h12 : c.get 12=BitVec.ofNat 32 length) (h13 : c.get 13=sp+3664#32)
    (h14 : c.get 14=BitVec.ofNat 32 cap) (h16 : c.get 16=1024#32)
    (h17 : c.get 17=BitVec.ofNat 32 m) (h18 : c.get 18=BitVec.ofNat 32 te)
    (h29 : c.get 29=BitVec.ofNat 32 (m+1)) (stack : d.get 2=sp) (firstLine : d.get 9=BitVec.ofNat 32 j)
    (accepted : HttpRequestSpec.version (bytes ram (sp+516#32)) (te+1) (te+9)<2)
    (result : HeadVersionResult.At d (HttpRequestSpec.version (bytes ram (sp+516#32)) (te+1) (te+9)) (c.get 13) (sp+4904#32)) :
    HeadLineReady.At d (HeadVersion.memory ram sp c te) sp m te j
      (HttpRequestSpec.version (bytes ram (sp+516#32)) (te+1) (te+9)) length cap := by
  have result' := result
  unfold HeadVersionResult.At at result'
  simp only [accepted,ite_true] at result'
  have mem := HeadVersion.memory_accepted ram sp c te ht accepted
  refine ⟨result'.1,stack,firstLine,result'.2.1,result'.2.2.1,result'.2.2.2.trans h13,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals rw [mem]
  · exact (HeadVersionStorage.methodEnd_word ram sp c).trans h17
  · exact (HeadVersionStorage.targetStart_word ram sp c).trans h29
  · exact (HeadVersionStorage.targetEnd_word ram sp c).trans h18
  · exact (HeadVersionStorage.mask_word ram sp c).trans h5
  · exact (HeadVersionStorage.maxHead_word ram sp c).trans h16
  · exact (HeadVersionStorage.n_word ram sp c).trans h14
  · exact (HeadVersionStorage.buf_word ram sp c).trans h11
  · exact (HeadVersionStorage.length_word ram sp c).trans h12
  · exact (HeadVersionStorage.dst_word ram sp c).trans h10
end E5R.Thermostat.HeadLineReadyFromVersion
