import Projects.thermostat.ReplyJson
namespace E5R.Thermostat.DecimalDigits
open E5R E5R.Thermostat

def digit (n : Nat) : BitVec 8 := BitVec.ofNat 8 (48+n)

theorem one (n : Nat) (hn : n < 10) : ReplyJson.decimal n = [digit n] := by
  rw [ReplyJson.decimal,ite_eq_left hn];rfl

theorem two (n : Nat) (hn : 10 ≤ n) (hb : n < 100) :
    ReplyJson.decimal n = [digit (n/10),digit (n%10)] := by
  rw [ReplyJson.decimal,ite_eq_right (by omega),one (n/10) (by omega)];rfl

theorem three (n : Nat) (hn : 100 ≤ n) (hb : n < 1000) :
    ReplyJson.decimal n = [digit (n/100),digit (n/10%10),digit (n%10)] := by
  rw [ReplyJson.decimal,ite_eq_right (by omega),two (n/10) (by omega) (by omega)]
  rw [Nat.div_div_eq_div_mul];rfl

theorem four (n : Nat) (hn : 1000 ≤ n) (hb : n < 10000) :
    ReplyJson.decimal n = [digit (n/1000),digit (n/100%10),digit (n/10%10),digit (n%10)] := by
  rw [ReplyJson.decimal,ite_eq_right (by omega),three (n/10) (by omega) (by omega)]
  simp only [Nat.div_div_eq_div_mul];rfl

theorem five (n : Nat) (hn : 10000 ≤ n) (hb : n < 100000) :
    ReplyJson.decimal n = [digit (n/10000),digit (n/1000%10),digit (n/100%10),digit (n/10%10),digit (n%10)] := by
  rw [ReplyJson.decimal,ite_eq_right (by omega),four (n/10) (by omega) (by omega)]
  simp only [Nat.div_div_eq_div_mul];rfl
end E5R.Thermostat.DecimalDigits

namespace E5R.Thermostat.DecimalDigits
open E5R E5R.Thermostat

theorem pair_two (n : Nat) (hn : 10 ≤ n) (hb : n < 100) :
    ReplyJson.decimal n = [digit ((n%100)/10),digit ((n%100)%10)] := by
  rw [Nat.mod_eq_of_lt hb]
  exact two n hn hb

theorem pair_three (n : Nat) (hn : 100 ≤ n) (hb : n < 1000) :
    ReplyJson.decimal n = [digit (n/100),digit ((n%100)/10),digit ((n%100)%10)] := by
  have h1 : (n%100)/10 = n/10%10 := by omega
  have h2 : (n%100)%10 = n%10 := by omega
  rw [h1,h2]
  exact three n hn hb
end E5R.Thermostat.DecimalDigits

namespace E5R.Thermostat.DecimalDigits
open E5R E5R.Thermostat

def fourTail (n : Nat) : List (BitVec 8) :=
  [digit ((n%10000)/100/10),digit ((n%10000)/100%10),digit (((n%10000)%100)/10),digit (((n%10000)%100)%10)]

theorem pair_four (n : Nat) (hn : 1000 ≤ n) (hb : n < 10000) : ReplyJson.decimal n = fourTail n := by
  unfold fourTail
  rw [Nat.mod_eq_of_lt hb]
  have h1 : n/100/10 = n/1000 := by omega
  have h2 : (n%100)/10 = n/10%10 := by omega
  have h3 : (n%100)%10 = n%10 := by omega
  rw [h1,h2,h3]
  exact four n hn hb

theorem pair_five (n : Nat) (hn : 10000 ≤ n) (hb : n < 100000) :
    ReplyJson.decimal n = digit (n/10000)::fourTail n := by
  unfold fourTail
  have h1 : (n%10000)/100/10 = n/1000%10 := by omega
  have h2 : (n%10000)/100%10 = n/100%10 := by omega
  have h3 : ((n%10000)%100)/10 = n/10%10 := by omega
  have h4 : ((n%10000)%100)%10 = n%10 := by omega
  rw [h1,h2,h3,h4]
  exact five n hn hb
end E5R.Thermostat.DecimalDigits
