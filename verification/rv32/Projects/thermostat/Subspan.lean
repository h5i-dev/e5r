import Projects.thermostat.ByteSlices
namespace E5R.Thermostat.Bytes
open E5R E5R.Thermostat

theorem take_span {B ram p xs} (hs : Span B ram p xs) (n : Nat) : Span B ram p (xs.take n) := by
  have h : Span B ram p (xs.take n++xs.drop n) := by rw [List.take_append_drop];exact hs
  exact left_part h

theorem drop_span {B ram p xs} (hs : Span B ram p xs) (n : Nat) (hn : n ≤ xs.length) :
    Span B ram (p+BitVec.ofNat 32 n) (xs.drop n) := by
  have h : Span B ram p (xs.take n++xs.drop n) := by rw [List.take_append_drop];exact hs
  have hh := suffix h
  simpa only [List.length_take,Nat.min_eq_left hn] using hh

theorem subspan {B ram p xs} (hs : Span B ram p xs) (s e : Nat) (hb : s ≤ e ∧ e ≤ xs.length) :
    Span B ram (p+BitVec.ofNat 32 s) ((xs.drop s).take (e-s)) :=
  take_span (drop_span hs s (by omega)) _

theorem subspan_length (xs : List (BitVec 8)) (s e : Nat) (hb : s ≤ e ∧ e ≤ xs.length) :
    ((xs.drop s).take (e-s)).length = e-s := by
  rw [List.length_take,List.length_drop,Nat.min_eq_left (by omega)]
end E5R.Thermostat.Bytes
