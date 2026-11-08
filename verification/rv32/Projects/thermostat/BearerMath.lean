import Projects.thermostat.AuthSpec
namespace E5R.Thermostat.BearerMath
open E5R E5R.Thermostat

theorem prefix_match (xs : List (BitVec 8)) :
    (WireSpec.ascii "Bearer ").isPrefixOf xs = true ↔ xs.take 7 = WireSpec.ascii "Bearer " := by
  rw [List.isPrefixOf_iff_prefix,List.prefix_iff_eq_take]
  change WireSpec.ascii "Bearer " = xs.take 7 ↔ xs.take 7 = WireSpec.ascii "Bearer "
  exact eq_comm

theorem enough (xs : List (BitVec 8)) (hp : xs.take 7 = WireSpec.ascii "Bearer ") : 7 ≤ xs.length := by
  have hl := congrArg List.length hp
  simp only [List.length_take] at hl
  change min 7 xs.length = 7 at hl
  omega

theorem split_eq (xs key : List (BitVec 8)) (hp : xs.take 7 = WireSpec.ascii "Bearer ") :
    xs = WireSpec.ascii "Bearer "++key ↔ xs.drop 7 = key := by
  constructor
  · intro h;rw [h]
    change ((WireSpec.ascii "Bearer ")++key).drop (WireSpec.ascii "Bearer ").length = key
    simp
  · intro h
    have hs := List.take_append_drop 7 xs
    rw [hp,h] at hs
    exact hs.symm

theorem authorized (xs key : List (BitVec 8)) :
    AuthSpec.authorized (some xs) key = decide (xs = WireSpec.ascii "Bearer "++key) := by
  change (match (if (WireSpec.ascii "Bearer ").isPrefixOf xs then some (xs.drop 7) else none) with
    | none => false | some t => decide (t = key)) = _
  by_cases hp : (WireSpec.ascii "Bearer ").isPrefixOf xs = true
  · have ht := (prefix_match xs).mp hp
    have he := split_eq xs key ht
    simp only [hp,ite_true,he]
  · have hn : xs ≠ WireSpec.ascii "Bearer "++key := by
      intro he;apply hp
      rw [List.isPrefixOf_iff_prefix]
      exact ⟨key,he.symm⟩
    have hb : (WireSpec.ascii "Bearer ").isPrefixOf xs = false := Bool.eq_false_iff.mpr hp
    simp only [hb,Bool.false_eq_true,ite_false,decide_eq_false hn]
end E5R.Thermostat.BearerMath
