import Projects.thermostat.HttpRequestSpec
import Projects.thermostat.Usize
namespace E5R.Thermostat.HeadHostSpec
open E5R E5R.Thermostat HttpRequestSpec

def Prefix (g : Nat → Nat) (s : Nat) : Prop :=
  lower (g s)=104 ∧ lower (g (s+1))=111 ∧ lower (g (s+2))=115 ∧ lower (g (s+3))=116
instance (g : Nat → Nat) (s : Nat) : Decidable (Prefix g s) := by unfold Prefix;infer_instance

theorem eqFrom_host (g : Nat → Nat) (s : Nat) : eqFrom g s litHost 0=decide (Prefix g s) := by
  have e4 : eqFrom g s litHost 4=true := by rw [eqFrom];rfl
  have e3 : eqFrom g s litHost 3=(if lower (g (s+3))≠116 then false else eqFrom g s litHost 4) := by rw [eqFrom];rfl
  have e2 : eqFrom g s litHost 2=(if lower (g (s+2))≠115 then false else eqFrom g s litHost 3) := by rw [eqFrom];rfl
  have e1 : eqFrom g s litHost 1=(if lower (g (s+1))≠111 then false else eqFrom g s litHost 2) := by rw [eqFrom];rfl
  have e0 : eqFrom g s litHost 0=(if lower (g (s+0))≠104 then false else eqFrom g s litHost 1) := by rw [eqFrom];rfl
  rw [e0,e1,e2,e3,e4]
  by_cases a : lower (g s)=104 <;> by_cases b : lower (g (s+1))=111 <;>
    by_cases c : lower (g (s+2))=115 <;> by_cases d : lower (g (s+3))=116 <;> simp [Prefix,a,b,c,d]

theorem classify_width4 (g : Nat → Nat) (s : Nat) : classify g s (s+4)=(if Prefix g s then 1 else 0) := by
  have host : eqCi g s (s+4) litHost=decide (Prefix g s) := by
    change (if s+4<s ∨ s+4-s≠4 then false else eqFrom g s litHost 0)=_
    rw [ite_eq_right (by omega)]
    exact eqFrom_host g s
  have contentLength : eqCi g s (s+4) litContentLength=false := by
    change (if s+4<s ∨ s+4-s≠14 then false else _)=false
    rw [ite_eq_left (by omega)]
  have transferEncoding : eqCi g s (s+4) litTransferEncoding=false := by
    change (if s+4<s ∨ s+4-s≠17 then false else _)=false
    rw [ite_eq_left (by omega)]
  rw [classify,host,contentLength,transferEncoding]
  by_cases good : Prefix g s <;> simp [good]

theorem guard (start length k : Nat) (hn : length≤2048) (hs : start+4≤length) (hk : k≤3) :
    taken .eq (BitVec.ofNat 32 length-BitVec.ofNat 32 start) (BitVec.ofNat 32 k)=false := by
  rw [BitVec.ofNat_sub_ofNat_of_le length start (by omega) (by omega),Usize.eq _ _ (by omega) (by omega)]
  simp only [show length-start≠k by omega,decide_false]
end E5R.Thermostat.HeadHostSpec
