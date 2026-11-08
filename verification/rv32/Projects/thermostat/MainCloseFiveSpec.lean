import Projects.thermostat.HeaderSpec
set_option autoImplicit false
namespace E5R.Thermostat.MainCloseFiveSpec
open E5R E5R.Thermostat

def close : List (BitVec 8) := [99#8,108#8,111#8,115#8,101#8]
def folded (g : Nat → BitVec 8) : List (BitVec 8) :=
  [HeaderSpec.lower (g 0),HeaderSpec.lower (g 1),HeaderSpec.lower (g 2),HeaderSpec.lower (g 3),HeaderSpec.lower (g 4)]
def all (g : Nat → BitVec 8) : Bool := decide (folded g=close)

theorem close_ascii : close=WireSpec.ascii "close" := by decide +kernel
theorem close_lower : close.map HeaderSpec.lower=close := by decide +kernel

theorem correspondence (xs : List (BitVec 8)) (length : xs.length=5) :
    HeaderSpec.same xs (WireSpec.ascii "close")=all (fun i => xs[i]?.getD 0#8) := by
  have mapped : xs.map HeaderSpec.lower=folded (fun i => xs[i]?.getD 0#8) := by
    apply List.ext_getElem
    · simp only [List.length_map,length,folded,List.length_cons,List.length_nil]
    · intro i hi hj
      have inside : i<5 := by simpa only [List.length_map,length] using hi
      have casesIndex : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
      rcases casesIndex with rfl|rfl|rfl|rfl|rfl
      all_goals simp only [List.getElem_map,folded,List.getElem_cons_zero,List.getElem_cons_succ]
      all_goals rw [List.getElem?_eq_getElem (by omega)]; rfl
  unfold HeaderSpec.same all
  rw [←close_ascii,close_lower,mapped]
end E5R.Thermostat.MainCloseFiveSpec
