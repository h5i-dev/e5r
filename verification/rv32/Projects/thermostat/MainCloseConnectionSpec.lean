import Projects.thermostat.HeaderSpec
set_option autoImplicit false
namespace E5R.Thermostat.MainCloseConnectionSpec
open E5R E5R.Thermostat

def connection : List (BitVec 8) := [99#8,111#8,110#8,110#8,101#8,99#8,116#8,105#8,111#8,110#8]
def folded (g : Nat → BitVec 8) : List (BitVec 8) :=
  [HeaderSpec.lower (g 0),HeaderSpec.lower (g 1),HeaderSpec.lower (g 2),HeaderSpec.lower (g 3),HeaderSpec.lower (g 4),
   HeaderSpec.lower (g 5),HeaderSpec.lower (g 6),HeaderSpec.lower (g 7),HeaderSpec.lower (g 8),HeaderSpec.lower (g 9)]
def all (g : Nat → BitVec 8) : Bool := decide (folded g=connection)

theorem connection_ascii : connection=WireSpec.ascii "connection" := by decide +kernel
theorem connection_lower : connection.map HeaderSpec.lower=connection := by decide +kernel

theorem correspondence (xs : List (BitVec 8)) (length : xs.length=10) :
    HeaderSpec.same xs (WireSpec.ascii "connection")=all (fun i => xs[i]?.getD 0#8) := by
  have mapped : xs.map HeaderSpec.lower=folded (fun i => xs[i]?.getD 0#8) := by
    apply List.ext_getElem
    · simp only [List.length_map,length,folded,List.length_cons,List.length_nil]
    · intro i hi hj
      have inside : i<10 := by simpa only [List.length_map,length] using hi
      have casesIndex : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 := by omega
      rcases casesIndex with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals simp only [List.getElem_map,folded,List.getElem_cons_zero,List.getElem_cons_succ]
      all_goals rw [List.getElem?_eq_getElem (by omega)]; rfl
  unfold HeaderSpec.same all
  rw [←connection_ascii,connection_lower,mapped]
end E5R.Thermostat.MainCloseConnectionSpec
