import Projects.thermostat.MainMethodSpec
import Projects.thermostat.Bytes
set_option autoImplicit false
namespace E5R.Thermostat.MainMethodBytes
open E5R E5R.Thermostat

theorem congr (len : Nat) (g h : Nat → Nat) (agree : ∀ k, k<len → g k=h k) :
    MainMethodSpec.classify len g=MainMethodSpec.classify len h := by
  by_cases eq3 : len=3
  · subst len
    have a0 := agree 0 (by decide)
    have a1 := agree 1 (by decide)
    have a2 := agree 2 (by decide)
    simp [MainMethodSpec.classify,a0,a1,a2]
  · by_cases eq4 : len=4
    · subst len
      have a0 := agree 0 (by decide)
      have a1 := agree 1 (by decide)
      have a2 := agree 2 (by decide)
      have a3 := agree 3 (by decide)
      simp [MainMethodSpec.classify,a0,a1,a2,a3]
    · by_cases eq5 : len=5
      · subst len
        have a0 := agree 0 (by decide)
        have a1 := agree 1 (by decide)
        have a2 := agree 2 (by decide)
        have a3 := agree 3 (by decide)
        have a4 := agree 4 (by decide)
        simp [MainMethodSpec.classify,a0,a1,a2,a3,a4]
      · by_cases eq6 : len=6
        · subst len
          have a0 := agree 0 (by decide)
          have a1 := agree 1 (by decide)
          have a2 := agree 2 (by decide)
          have a3 := agree 3 (by decide)
          have a4 := agree 4 (by decide)
          have a5 := agree 5 (by decide)
          simp [MainMethodSpec.classify,a0,a1,a2,a3,a4,a5]
        · simp [MainMethodSpec.classify,eq3,eq4,eq5,eq6]

def byte (input : List (BitVec 8)) (k : Nat) : BitVec 8 := input[k]?.getD 0#8

def token (input : List (BitVec 8)) (len : Nat) : List Nat := (input.take len).map BitVec.toNat

theorem take_correspondence (input : List (BitVec 8)) (len : Nat) (bound : len≤input.length) :
    MainMethodSpec.classify len (fun k => (byte input k).toNat)=MainMethodSpec.decode (token input len) := by
  have length : (token input len).length=len := by simp [token,List.length_take,Nat.min_eq_left bound]
  have agree (k : Nat) (inside : k<len) : (byte input k).toNat=((token input len)[k]?.getD 0) := by
    have hi : k<input.length := by omega
    simp only [token,byte,List.getElem?_map,List.getElem?_take_of_lt inside,List.getElem?_eq_getElem hi]
    rfl
  rw [congr len _ _ agree]
  simpa only [length] using MainMethodSpec.correspondence (token input len)
end E5R.Thermostat.MainMethodBytes
