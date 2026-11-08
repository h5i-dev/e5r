namespace E5R.Thermostat.MainMethodSpec

/-- Method discriminants in the application's declared Rust enum order. -/
inductive Method where
  | get | head | post | put | patch | delete | other
  deriving DecidableEq, Repr

def tag : Method → Nat
  | .get => 0 | .head => 1 | .post => 2 | .put => 3 | .patch => 4 | .delete => 5 | .other => 6

/-- Exact, case-sensitive octets. No token is inferred from its length alone. -/
def decode (input : List Nat) : Method :=
  if input=[71,69,84] then .get
  else if input=[72,69,65,68] then .head
  else if input=[80,79,83,84] then .post
  else if input=[80,85,84] then .put
  else if input=[80,65,84,67,72] then .patch
  else if input=[68,69,76,69,84,69] then .delete
  else .other

def classify (len : Nat) (g : Nat → Nat) : Method :=
  if len=3 ∧ g 0=71 ∧ g 1=69 ∧ g 2=84 then .get
  else if len=4 ∧ g 0=72 ∧ g 1=69 ∧ g 2=65 ∧ g 3=68 then .head
  else if len=4 ∧ g 0=80 ∧ g 1=79 ∧ g 2=83 ∧ g 3=84 then .post
  else if len=3 ∧ g 0=80 ∧ g 1=85 ∧ g 2=84 then .put
  else if len=5 ∧ g 0=80 ∧ g 1=65 ∧ g 2=84 ∧ g 3=67 ∧ g 4=72 then .patch
  else if len=6 ∧ g 0=68 ∧ g 1=69 ∧ g 2=76 ∧ g 3=69 ∧ g 4=84 ∧ g 5=69 then .delete
  else .other

/-- The indexed classifier agrees with exact whole-list token matching. -/
theorem correspondence (input : List Nat) :
    classify input.length (fun i => input[i]?.getD 0)=decode input := by
  cases input with
  | nil => rfl
  | cons a tail =>
    cases tail with
    | nil => simp [classify,decode]
    | cons b tail =>
      cases tail with
      | nil => simp [classify,decode]
      | cons c tail =>
        cases tail with
        | nil => simp [classify,decode]
        | cons d tail =>
          cases tail with
          | nil => simp [classify,decode]
          | cons e tail =>
            cases tail with
            | nil => simp [classify,decode]
            | cons f tail =>
              cases tail with
              | nil => simp [classify,decode]
              | cons g tail =>
                have ne3 : ¬(a::b::c::d::e::f::g::tail).length=3 := by simp only [List.length_cons];omega
                have ne4 : ¬(a::b::c::d::e::f::g::tail).length=4 := by simp only [List.length_cons];omega
                have ne5 : ¬(a::b::c::d::e::f::g::tail).length=5 := by simp only [List.length_cons];omega
                have ne6 : ¬(a::b::c::d::e::f::g::tail).length=6 := by simp only [List.length_cons];omega
                simp only [classify,ne3,ne4,ne5,ne6,false_and,ite_false]
                have n3 : (a::b::c::d::e::f::g::tail)≠[71,69,84] := by intro h;have eq := congrArg List.length h;simp only [List.length_cons,List.length_nil] at eq;omega
                have n4 : (a::b::c::d::e::f::g::tail)≠[72,69,65,68] := by intro h;have eq := congrArg List.length h;simp only [List.length_cons,List.length_nil] at eq;omega
                have n4p : (a::b::c::d::e::f::g::tail)≠[80,79,83,84] := by intro h;have eq := congrArg List.length h;simp only [List.length_cons,List.length_nil] at eq;omega
                have n3p : (a::b::c::d::e::f::g::tail)≠[80,85,84] := by intro h;have eq := congrArg List.length h;simp only [List.length_cons,List.length_nil] at eq;omega
                have n5 : (a::b::c::d::e::f::g::tail)≠[80,65,84,67,72] := by intro h;have eq := congrArg List.length h;simp only [List.length_cons,List.length_nil] at eq;omega
                have n6 : (a::b::c::d::e::f::g::tail)≠[68,69,76,69,84,69] := by intro h;have eq := congrArg List.length h;simp only [List.length_cons,List.length_nil] at eq;omega
                simp [decode,n3,n4,n4p,n3p,n5,n6]

end E5R.Thermostat.MainMethodSpec
