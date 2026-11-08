import Projects.thermostat.WireSpec
namespace E5R.Thermostat.RelaySpec
open E5R E5R.Thermostat

def body (idx : Word) (xs : List (BitVec 8)) : Except Nat Spec.Command :=
  if xs = WireSpec.ascii "on" then .ok (.relay (idx.setWidth 8) true)
  else if xs = WireSpec.ascii "off" then .ok (.relay (idx.setWidth 8) false)
  else .error 400

theorem two (idx : Word) (xs : List (BitVec 8)) (hl : xs.length = 2) :
    body idx xs = (if xs = WireSpec.ascii "on" then .ok (.relay (idx.setWidth 8) true) else .error 400) := by
  have hn : xs ≠ WireSpec.ascii "off" := by
    intro he;have h := congrArg List.length he;change xs.length = 3 at h;omega
  simp only [body,ite_eq_right hn]

theorem three (idx : Word) (a b z : BitVec 8) :
    body idx [a,b,z] = (if a = 111#8 ∧ b = 102#8 ∧ z = 102#8 then .ok (.relay (idx.setWidth 8) false) else .error 400) := by
  have hn : [a,b,z] ≠ WireSpec.ascii "on" := by
    intro he;have h := congrArg List.length he;change 3 = 2 at h;omega
  have he : [a,b,z] = WireSpec.ascii "off" ↔ a = 111#8 ∧ b = 102#8 ∧ z = 102#8 := by
    change [a,b,z] = [111#8,102#8,102#8] ↔ _;simp
  simp only [body,ite_eq_right hn,he]

theorem other (idx : Word) (xs : List (BitVec 8)) (h2 : xs.length ≠ 2) (h3 : xs.length ≠ 3) : body idx xs = .error 400 := by
  have hn : xs ≠ WireSpec.ascii "on" := by intro he;apply h2;rw [he];rfl
  have hf : xs ≠ WireSpec.ascii "off" := by intro he;apply h3;rw [he];rfl
  simp only [body,ite_eq_right hn,ite_eq_right hf]
end E5R.Thermostat.RelaySpec
