import Projects.thermostat.HeadActionSpec
import Projects.thermostat.HeadClValue
import Projects.thermostat.HeadTeValue
namespace E5R.Thermostat.HeadClassSpec
open E5R E5R.Thermostat HttpRequestSpec

theorem different (g : Nat → Nat) (s e : Nat) (lit : List Nat) (width : e-s≠lit.length) : eqCi g s e lit=false := by
  unfold eqCi
  rw [ite_eq_left (Or.inr width)]

theorem width14 (g : Nat → Nat) (s : Nat) :
    classify g s (s+14)=(if eqCi g s (s+14) litContentLength then 2 else 0) := by
  unfold classify
  rw [different g s (s+14) litHost (by change s+14-s≠4;omega),
    different g s (s+14) litTransferEncoding (by change s+14-s≠17;omega)]
  simp only [Bool.false_eq_true,ite_false]

theorem width17 (g : Nat → Nat) (s : Nat) :
    classify g s (s+17)=(if eqCi g s (s+17) litTransferEncoding then 3 else 0) := by
  unfold classify
  rw [different g s (s+17) litHost (by change s+17-s≠4;omega),
    different g s (s+17) litContentLength (by change s+17-s≠14;omega)]
  simp only [Bool.false_eq_true,ite_false]

theorem other (g : Nat → Nat) (s e : Nat) (host : e-s≠4) (cl : e-s≠14) (te : e-s≠17) : classify g s e=0 := by
  unfold classify
  rw [different g s e litHost host,different g s e litContentLength cl,different g s e litTransferEncoding te]
  rfl

theorem non_host_kinds (g : Nat → Nat) (s e : Nat) (notHost : e-s≠4) :
    classify g s e=0 ∨ classify g s e=2 ∨ classify g s e=3 := by
  have noHost := different g s e litHost notHost
  simp only [classify,noHost,Bool.false_eq_true,ite_false]
  cases eqCi g s e litContentLength <;> cases eqCi g s e litTransferEncoding <;> decide

def ofCl (f : Fields) : Num → Added
  | .bad status => .bad status
  | .ok value => .ok {f with hasCl := true, cl := value}
def ofTe (f : Fields) : Option Nat → Added
  | some status => .bad status
  | none => .ok {f with te := true}

theorem cl_action (g : Nat → Nat) (f : Fields) (ns ne vs ve le minor : Nat) (kind : classify g ns ne=2) :
    HeadActionSpec.action g f ns ne vs ve le minor 1024=ofCl f (HeadClValue.outcome g f vs ve le) := by
  simp only [HeadActionSpec.action,kind,show ¬(2=1) by decide,ite_false,ite_true]
  unfold HeadClValue.outcome HeadClPreflight.Bad
  by_cases bad : f.hasCl ∨ f.te ∨ ve≠le
  · simp only [bad,ite_true];rfl
  · simp only [bad,ite_false]
    cases contentLength g vs ve 1024 <;> rfl

theorem te_action (g : Nat → Nat) (f : Fields) (ns ne vs ve le minor : Nat) (kind : classify g ns ne=3) :
    HeadActionSpec.action g f ns ne vs ve le minor 1024=ofTe f (HeadTeValue.outcome g f vs ve le minor) := by
  simp only [HeadActionSpec.action,kind,show ¬(3=1) by decide,show ¬(3=2) by decide,ite_false,ite_true]
  unfold HeadTeValue.outcome HeadTePreflight.Bad
  by_cases bad : minor=0 ∨ f.te ∨ f.hasCl ∨ ve≠le
  · simp only [bad,ite_true];rfl
  · simp only [bad,ite_false]
    cases eqCi g vs ve litChunked <;> rfl

theorem ordinary_action (g : Nat → Nat) (f : Fields) (ns ne vs ve le minor : Nat) (kind : classify g ns ne=0) :
    HeadActionSpec.action g f ns ne vs ve le minor 1024=.ok f := by
  simp only [HeadActionSpec.action,kind,show ¬(0=1) by decide,show ¬(0=2) by decide,show ¬(0=3) by decide,ite_false]
end E5R.Thermostat.HeadClassSpec
