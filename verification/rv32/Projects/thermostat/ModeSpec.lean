import Projects.thermostat.WireSpec
namespace E5R.Thermostat.ModeSpec
open E5R E5R.Thermostat

def value (body : List (BitVec 8)) : Except Nat Spec.Command :=
  if body = WireSpec.ascii "off" then .ok (.mode .off)
  else if body = WireSpec.ascii "heat" then .ok (.mode .heat)
  else if body = WireSpec.ascii "auto" then .ok (.mode .auto)
  else .error 400

theorem as_decode (body : List (BitVec 8)) (first : Option (List (BitVec 8))) :
    WireSpec.decode (WireSpec.ascii "/mode") body first = value (TrimMath.trim body) := by rfl

theorem auto_first (bs : List (BitVec 8)) :
    value (97#8::bs) = (if bs = WireSpec.ascii "uto" then .ok (.mode .auto) else .error 400) := by
  change (if 97#8::bs = [111#8,102#8,102#8] then _ else if 97#8::bs = [104#8,101#8,97#8,116#8] then _
    else if 97#8::bs = 97#8::WireSpec.ascii "uto" then _ else _) = _
  simp only [List.cons.injEq]
  simp

theorem heat_first (bs : List (BitVec 8)) :
    value (104#8::bs) = (if bs = WireSpec.ascii "eat" then .ok (.mode .heat) else .error 400) := by
  change (if 104#8::bs = [111#8,102#8,102#8] then _ else if 104#8::bs = 104#8::WireSpec.ascii "eat" then _
    else if 104#8::bs = [97#8,117#8,116#8,111#8] then _ else _) = _
  simp only [List.cons.injEq]
  simp

theorem other_four (b : BitVec 8) (bs : List (BitVec 8)) (hl : bs.length = 3)
    (ha : b ≠ 97#8) (hh : b ≠ 104#8) : value (b::bs) = .error 400 := by
  have hoff : b::bs ≠ WireSpec.ascii "off" := by
    intro he
    have hn := congrArg List.length he
    change bs.length+1 = 3 at hn
    omega
  have hheat : b::bs ≠ WireSpec.ascii "heat" := by
    intro he;exact hh (List.cons.inj he).1
  have hauto : b::bs ≠ WireSpec.ascii "auto" := by
    intro he;exact ha (List.cons.inj he).1
  simp only [value,ite_eq_right hoff,ite_eq_right hheat,ite_eq_right hauto]
end E5R.Thermostat.ModeSpec
