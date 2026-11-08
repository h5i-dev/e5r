import Projects.thermostat.ReplyJson
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.ReplyJsonBounds
open E5R E5R.Thermostat

theorem decimal_length (k : Nat) : ∀ n, 0 < k → n < 10^k → (ReplyJson.decimal n).length ≤ k := by
  induction k with
  | zero => intro n hk hn;omega
  | succ k ih =>
    intro n hk hn
    rw [ReplyJson.decimal]
    by_cases hsmall : n < 10
    · simp only [ite_eq_left hsmall,List.length_cons,List.length_nil];omega
    · rw [ite_eq_right hsmall,List.length_append,List.length_cons,List.length_nil]
      have hkpos : 0 < k := by
        by_cases hz : k = 0
        · subst k;change n < 10 at hn;omega
        · omega
      have hd : n/10 < 10^k := (Nat.div_lt_iff_lt_mul (by decide)).2 (by simpa only [Nat.pow_succ] using hn)
      have hl := ih (n/10) hkpos hd
      omega

theorem magnitude (v : BitVec 16) : v.toInt.natAbs ≤ 32768 := by
  have hh := @BitVec.toInt_lt 16 v
  have hl := @BitVec.le_two_mul_toInt 16 v
  change v.toInt < 32768 at hh
  change -65536 ≤ 2*v.toInt at hl
  by_cases hp : 0 ≤ v.toInt
  · have ha := Int.natAbs_of_nonneg hp;omega
  · have ha := Int.ofNat_natAbs_of_nonpos (show v.toInt ≤ 0 by omega);omega

theorem signed_length (v : BitVec 16) : (ReplyJson.signed v).length ≤ 6 := by
  have hm := magnitude v
  have hd := decimal_length 5 v.toInt.natAbs (by decide) (by change v.toInt.natAbs < 100000;omega)
  unfold ReplyJson.signed
  rw [List.length_append]
  split <;> simp only [List.length_cons,List.length_nil] <;> omega
end E5R.Thermostat.ReplyJsonBounds
