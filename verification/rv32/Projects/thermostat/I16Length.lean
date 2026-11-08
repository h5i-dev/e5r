import Projects.thermostat.I16Ready
import Projects.thermostat.DecimalDigits
namespace E5R.Thermostat.I16Ready
open E5R E5R.Thermostat

theorem decimal_length (n : Nat) (hn : n ≤ 32768) :
    (ReplyJson.decimal n).length = length n := by
  by_cases h1 : n < 10
  · rw [DecimalDigits.one n h1]
    simp only [length,offset,ite_eq_left h1];rfl
  · by_cases h2 : n < 100
    · rw [DecimalDigits.two n (by omega) h2]
      simp only [length,offset,ite_eq_right h1,ite_eq_left h2];rfl
    · by_cases h3 : n < 1000
      · rw [DecimalDigits.three n (by omega) h3]
        simp only [length,offset,ite_eq_right h1,ite_eq_right h2,ite_eq_left h3];rfl
      · by_cases h4 : n < 10000
        · rw [DecimalDigits.four n (by omega) h4]
          simp only [length,offset,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_left h4];rfl
        · rw [DecimalDigits.five n (by omega) (by omega)]
          simp only [length,offset,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4];rfl

theorem offset_bounds (n : Nat) : 3 ≤ offset n ∧ offset n ≤ 7 := by
  unfold offset
  repeat first | split | omega

theorem source_end (n : Nat) (hn : n ≤ 32768) : offset n+(ReplyJson.decimal n).length = 8 := by
  rw [decimal_length n hn,length]
  have ho := offset_bounds n
  omega
end E5R.Thermostat.I16Ready
