import Projects.thermostat.HttpRequestSpec
namespace E5R.Thermostat.HeadVersionSpec
open E5R E5R.Thermostat HttpRequestSpec

def Prefix (g : Nat → Nat) (s : Nat) : Prop :=
  g s=72 ∧ g (s+1)=84 ∧ g (s+2)=84 ∧ g (s+3)=80 ∧ g (s+4)=47

instance (g : Nat → Nat) (s : Nat) : Decidable (Prefix g s) := by unfold Prefix;infer_instance

theorem eqAt_prefix (g : Nat → Nat) (s : Nat) : eqAt g s litHttp 0=decide (Prefix g s) := by
  have e5 : eqAt g s litHttp 5=true := by rw [eqAt];rfl
  have e4 : eqAt g s litHttp 4=(if g (s+4)≠47 then false else eqAt g s litHttp 5) := by rw [eqAt];rfl
  have e3 : eqAt g s litHttp 3=(if g (s+3)≠80 then false else eqAt g s litHttp 4) := by rw [eqAt];rfl
  have e2 : eqAt g s litHttp 2=(if g (s+2)≠84 then false else eqAt g s litHttp 3) := by rw [eqAt];rfl
  have e1 : eqAt g s litHttp 1=(if g (s+1)≠84 then false else eqAt g s litHttp 2) := by rw [eqAt];rfl
  have e0 : eqAt g s litHttp 0=(if g (s+0)≠72 then false else eqAt g s litHttp 1) := by rw [eqAt];rfl
  rw [e0,e1,e2,e3,e4,e5]
  by_cases a : g s=72 <;> by_cases b : g (s+1)=84 <;> by_cases c : g (s+2)=84 <;>
    by_cases d : g (s+3)=80 <;> by_cases e : g (s+4)=47 <;> simp [Prefix,a,b,c,d,e]

theorem version (g : Nat → Nat) (s : Nat) :
    HttpRequestSpec.version g s (s+8)=
      if Prefix g s then versionDigits (g (s+5)) (g (s+6)) (g (s+7)) else 3 := by
  unfold HttpRequestSpec.version
  have bound : ¬s+8<s := by omega
  have width : s+8-s=8 := by omega
  rw [width]
  simp only [bound,Nat.lt_irrefl,not_true_eq_false,or_self,ite_false,eqAt_prefix]
  by_cases good : Prefix g s <;> simp [good]

theorem digits_le (a dot b : Nat) : versionDigits a dot b≤3 := by
  unfold versionDigits
  repeat' first | split | omega
theorem version_le (g : Nat → Nat) (s e : Nat) : HttpRequestSpec.version g s e≤3 := by
  unfold HttpRequestSpec.version
  split
  · decide
  · split
    · decide
    · exact digits_le _ _ _
end E5R.Thermostat.HeadVersionSpec
