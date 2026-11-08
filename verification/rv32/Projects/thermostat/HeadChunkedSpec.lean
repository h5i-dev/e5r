import Projects.thermostat.HttpRequestSpec
import Projects.thermostat.Usize
namespace E5R.Thermostat.HeadChunkedSpec
open E5R E5R.Thermostat HttpRequestSpec

def Prefix (g : Nat → Nat) (s : Nat) : Prop :=
  lower (g s)=99 ∧ lower (g (s+1))=104 ∧ lower (g (s+2))=117 ∧
    lower (g (s+3))=110 ∧ lower (g (s+4))=107 ∧ lower (g (s+5))=101 ∧ lower (g (s+6))=100
instance (g : Nat → Nat) (s : Nat) : Decidable (Prefix g s) := by unfold Prefix;infer_instance

theorem guard (start length k : Nat) (hn : length≤2048) (hs : start+7≤length) (hk : k≤6) :
    taken .eq (BitVec.ofNat 32 length-BitVec.ofNat 32 start) (BitVec.ofNat 32 k)=false := by
  rw [BitVec.ofNat_sub_ofNat_of_le length start (by omega) (by omega),Usize.eq _ _ (by omega) (by omega)]
  simp only [show length-start≠k by omega,decide_false]
theorem eqFrom_chunked (g : Nat → Nat) (s : Nat) : eqFrom g s litChunked 0=decide (Prefix g s) := by
  have e7 : eqFrom g s litChunked 7=true := by rw [eqFrom];rfl
  have e6 : eqFrom g s litChunked 6=(if lower (g (s+6))≠100 then false else eqFrom g s litChunked 7) := by rw [eqFrom];rfl
  have e5 : eqFrom g s litChunked 5=(if lower (g (s+5))≠101 then false else eqFrom g s litChunked 6) := by rw [eqFrom];rfl
  have e4 : eqFrom g s litChunked 4=(if lower (g (s+4))≠107 then false else eqFrom g s litChunked 5) := by rw [eqFrom];rfl
  have e3 : eqFrom g s litChunked 3=(if lower (g (s+3))≠110 then false else eqFrom g s litChunked 4) := by rw [eqFrom];rfl
  have e2 : eqFrom g s litChunked 2=(if lower (g (s+2))≠117 then false else eqFrom g s litChunked 3) := by rw [eqFrom];rfl
  have e1 : eqFrom g s litChunked 1=(if lower (g (s+1))≠104 then false else eqFrom g s litChunked 2) := by rw [eqFrom];rfl
  have e0 : eqFrom g s litChunked 0=(if lower (g (s+0))≠99 then false else eqFrom g s litChunked 1) := by rw [eqFrom];rfl
  rw [e0,e1,e2,e3,e4,e5,e6,e7]
  by_cases h0 : lower (g (s+0))=99 <;> by_cases h1 : lower (g (s+1))=104 <;> by_cases h2 : lower (g (s+2))=117 <;> by_cases h3 : lower (g (s+3))=110 <;> by_cases h4 : lower (g (s+4))=107 <;> by_cases h5 : lower (g (s+5))=101 <;> by_cases h6 : lower (g (s+6))=100 <;> simp [Prefix,h0,h1,h2,h3,h4,h5,h6]

theorem eqCi_chunked (g : Nat → Nat) (s : Nat) : eqCi g s (s+7) litChunked=decide (Prefix g s) := by
  rw [eqCi,ite_eq_right (by change ¬(s+7<s ∨ s+7-s≠7);omega)]
  exact eqFrom_chunked g s

end E5R.Thermostat.HeadChunkedSpec
