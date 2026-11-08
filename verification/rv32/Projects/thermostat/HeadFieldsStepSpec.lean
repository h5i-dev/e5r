import Projects.thermostat.HeadLineScanSpec
import Projects.thermostat.HeadFieldLineSpec
namespace E5R.Thermostat.HeadFieldsStepSpec
open E5R E5R.Thermostat HttpRequestSpec

inductive Next where
  | more
  | bad (status : Nat)
  | done (f : Fields) (length : Nat)
  | again (index : Nat) (f : Fields)
  deriving DecidableEq, Repr

def one (g : Nat → Nat) (i cap minor : Nat) (f : Fields) : Next :=
  match HeadFieldLineSpec.next g i cap with
  | .more => .more
  | .bad status => .bad status
  | .done length => .done f length
  | .header le parsed => match parsed with
    | .bad status => .bad status
    | .ok ne vs ve => match addHeader g f i ne vs ve le minor 1024 with
      | .bad status => .bad status
      | .ok f' => if le+2<cap then .again (le+2) f' else .more

def eval (g : Nat → Nat) (cap minor : Nat) : Next → Fielded
  | .more => .more
  | .bad status => .bad status
  | .done f length => .done f length
  | .again index f => fields g cap minor 1024 index f

theorem header_bound (g : Nat → Nat) (i cap le : Nat) (parsed : HdrLine)
    (inside : i<cap) (value : HeadFieldLineSpec.next g i cap=.header le parsed) : i≤le ∧ le≤cap := by
  unfold HeadFieldLineSpec.next at value
  dsimp only at value
  split at value
  next more => cases value
  next notMore =>
    split at value
    next bad => cases value
    next notBad =>
      split at value
      next empty => cases value
      next nonempty =>
        cases value
        exact ⟨HttpRequestSpec.scan_ge notEol g i cap,
          HttpRequestSpec.scan_le notEol g i cap (by omega)⟩

theorem fields_eq (g : Nat → Nat) (i cap minor : Nat) (f : Fields) (inside : i<cap) :
    fields g cap minor 1024 i f=eval g cap minor (one g i cap minor f) := by
  rw [fields,ite_eq_left inside]
  unfold one HeadFieldLineSpec.next
  dsimp only
  by_cases more : lineTerm g (lineEnd g i cap) cap=1
  · simp only [more,ite_true,eval]
  · simp only [more,ite_false]
    by_cases bad : lineTerm g (lineEnd g i cap) cap=2
    · simp only [bad,ite_true,eval]
    · simp only [bad,ite_false]
      by_cases empty : (lineEnd g i cap)=i
      · simp only [empty,ite_true,eval]
      · simp only [empty,ite_false]
        cases parsed : headerLine g i (lineEnd g i cap) with
        | bad status => simp only [parsed,eval]
        | ok ne vs ve =>
          simp only [parsed]
          cases added : addHeader g f i ne vs ve (lineEnd g i cap) minor 1024 with
          | bad status => simp only [added,eval]
          | ok next =>
            simp only [added]
            by_cases again : (lineEnd g i cap)+2<cap
            · simp only [again,ite_true,eval]
            · simp only [again,ite_false,eval]
              rw [fields,ite_eq_right again]
end E5R.Thermostat.HeadFieldsStepSpec
