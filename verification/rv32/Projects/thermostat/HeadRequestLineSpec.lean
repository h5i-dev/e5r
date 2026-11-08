import Projects.thermostat.HeadMethodTarget
import Projects.thermostat.HeadMethodInputSpec
import Projects.thermostat.HeadTargetValidationSpec
import Projects.thermostat.HeadVersionSpec
namespace E5R.Thermostat.HeadRequestLineSpec
open E5R E5R.Thermostat HttpRequestSpec

/-- Derive early target rejection, including a wrong version width, from
    the independent request-line parser rather than postulating a typed error. -/
theorem bad_target (g : Nat → Nat) (j : Nat) (methodGood : HeadMethodPrefix.Good g j)
    (bad : ¬HeadTargetValidationSpec.Good g (scan isTchar g 0 j) (scan isTargetByte g (scan isTchar g 0 j+1) j) j) :
    requestLine g 0 j=ReqLine.bad 400 := by
  let m := scan isTchar g 0 j
  let te := scan isTargetByte g (m+1) j
  have method : 0<m ∧ m<j ∧ g m=32 := methodGood
  have methodNonempty : ¬(m=0 ∨ j≤m) := by omega
  have methodSpace : ¬g m≠32 := by intro h;exact h method.2.2
  unfold requestLine
  dsimp only
  change (if m=0 ∨ j≤m then ReqLine.bad 400 else if g m≠32 then ReqLine.bad 400 else
    if te=m+1 ∨ j≤te then ReqLine.bad 400 else if g (m+1)≠47 ∨ g te≠32 then ReqLine.bad 400 else
      let v := version g (te+1) j
      if v=3 then ReqLine.bad 400 else if v=2 then ReqLine.bad 505 else ReqLine.ok 0 m (m+1) te v)=_
  simp only [methodNonempty,methodSpace,ite_false]
  by_cases empty : te=m+1 ∨ j≤te
  · simp only [empty,ite_true]
  · simp only [empty,ite_false]
    by_cases delimiter : g (m+1)≠47 ∨ g te≠32
    · simp only [delimiter,ite_true]
    · simp only [delimiter,ite_false]
      have lower : m+1≤te := scan_ge isTargetByte g (m+1) j
      have span : m+1<te ∧ te<j := by omega
      have chars : g te=32 ∧ g (m+1)=47 := by omega
      have wrongWidth : j-te≠9 := by
        intro width
        exact bad ⟨span.1,span.2,chars.1,chars.2,width⟩
      have wrongVersion : version g (te+1) j=3 := by
        unfold version
        have notEight : j-(te+1)≠8 := by omega
        split
        · rfl
        · rename_i goodWidth
          exact False.elim (goodWidth (Or.inr notEight))
      simp only [wrongVersion,ite_true]

theorem checked_target (g : Nat → Nat) (j : Nat) (methodGood : HeadMethodPrefix.Good g j)
    (targetGood : HeadTargetValidationSpec.Good g (scan isTchar g 0 j) (scan isTargetByte g (scan isTchar g 0 j+1) j) j) :
    let m := scan isTchar g 0 j
    let te := scan isTargetByte g (m+1) j
    let v := version g (te+1) j
    requestLine g 0 j=(if v=3 then ReqLine.bad 400 else if v=2 then ReqLine.bad 505 else ReqLine.ok 0 m (m+1) te v) := by
  let m := scan isTchar g 0 j
  let te := scan isTargetByte g (m+1) j
  have method : 0<m ∧ m<j ∧ g m=32 := methodGood
  have target : m+1<te ∧ te<j ∧ g te=32 ∧ g (m+1)=47 ∧ j-te=9 := targetGood
  have methodNonempty : ¬(m=0 ∨ j≤m) := by omega
  have methodSpace : ¬g m≠32 := fun h => h method.2.2
  have targetNonempty : ¬(te=m+1 ∨ j≤te) := by omega
  have delimiter : ¬(g (m+1)≠47 ∨ g te≠32) := by omega
  unfold requestLine
  dsimp only
  change (if m=0 ∨ j≤m then _ else if g m≠32 then _ else if te=m+1 ∨ j≤te then _ else if g (m+1)≠47 ∨ g te≠32 then _ else _) = _
  simp only [methodNonempty,methodSpace,targetNonempty,delimiter,ite_false]
theorem bad_prefix (g : Nat → Nat) (j : Nat) (bad : ¬HeadMethodTarget.Good g j) :
    requestLine g 0 j=ReqLine.bad 400 := by
  by_cases method : HeadMethodPrefix.Good g j
  · exact bad_target g j method (fun target => bad ⟨method,target⟩)
  · exact HeadMethodInputSpec.bad_request g j method
end E5R.Thermostat.HeadRequestLineSpec
