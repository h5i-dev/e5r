import Projects.thermostat.ReplyJson
import Projects.thermostat.DecimalDigits
namespace E5R.Thermostat.HttpDecDigitsSpec
open E5R E5R.Thermostat

theorem cases (n : Nat) (hn : n≤832) : ReplyJson.decimal n=
    if n<10 then [DecimalDigits.digit (n%10)]
    else if n<100 then [DecimalDigits.digit ((n/10)%10),DecimalDigits.digit (n%10)]
    else [DecimalDigits.digit (n/100),DecimalDigits.digit ((n/10)%10),DecimalDigits.digit (n%10)] := by
  by_cases h1 : n<10
  · rw [ReplyJson.decimal,if_pos h1,if_pos h1,Nat.mod_eq_of_lt h1]
    rfl
  · rw [ReplyJson.decimal,if_neg h1,if_neg h1]
    by_cases h2 : n<100
    · rw [if_pos h2,ReplyJson.decimal,if_pos (show n/10<10 by omega),Nat.mod_eq_of_lt (show n/10<10 by omega)]
      rfl
    · rw [if_neg h2,ReplyJson.decimal,if_neg (show ¬n/10<10 by omega)]
      rw [show (n/10)/10=n/100 by omega,ReplyJson.decimal,if_pos (show n/100<10 by omega)]
      rfl

theorem length (n : Nat) (hn : n≤832) : (ReplyJson.decimal n).length=(if n<10 then 1 else if n<100 then 2 else 3) := by
  rw [cases n hn]
  split <;> first | rfl | (split <;> rfl)

theorem bounds (n : Nat) (hn : n≤832) : 0<(ReplyJson.decimal n).length ∧ (ReplyJson.decimal n).length≤3 := by
  rw [length n hn]
  split <;> first | decide | (split <;> decide)
end E5R.Thermostat.HttpDecDigitsSpec
